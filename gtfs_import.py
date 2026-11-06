#!/usr/bin/env python3
"""
Condense MTA bus GTFS folders into one compact schedule.sqlite for busstring.py.

Usage, on your Mac in the "bus tracking" folder:
  python3 gtfs_import.py gtfs
where "gtfs" holds the region folders (gtfs_b, gtfs_bx, gtfs_m, gtfs_q, gtfs_si,
gtfs_busco). It writes schedule.sqlite, which goes on the server next to
busstring.py. Re-run it each time the MTA publishes a new quarterly schedule.

If bus_lanes.csv (NYC DOT "Bus Lanes - Local Streets", exported as CSV) is in
the same folder, it also works out which stretches of each route have a bus
lane, of what type, and when the lane is in effect.

Standard library only (Python 3.8+).
"""
import csv
import math
import os
import re
import sqlite3
import sys
import time
from datetime import date, timedelta

LAT0 = 40.7          # New York; for converting coordinates to meters
EARTH = 6371000.0


def read(folder, name):
    path = os.path.join(folder, name)
    if not os.path.exists(path):
        return
    with open(path, newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            yield {(k or "").strip(): (v or "").strip() for k, v in r.items()}


def secs(hms):
    h, m, s = hms.split(":")
    return int(h) * 3600 + int(m) * 60 + int(s)


def ymd(s):
    return date(int(s[:4]), int(s[4:6]), int(s[6:8]))


def to_xy(lat, lon):
    return (math.radians(lon) * EARTH * math.cos(math.radians(LAT0)),
            math.radians(lat) * EARTH)


def project(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    l2 = dx * dx + dy * dy
    u = 0.0 if l2 == 0 else max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / l2))
    return math.hypot(px - (ax + u * dx), py - (ay + u * dy)), u


def distances_on_shape(stop_xy, shape):
    """Distance along the shape (meters) for each stop, in order. Searches forward
    from the previous stop so routes that loop back near themselves stay in order."""
    out, i0, n = [], 0, len(shape)
    for px, py in stop_xy:
        best = None
        for i in range(i0, n - 1):
            ax, ay, ac = shape[i]
            bx, by, _ = shape[i + 1]
            d, u = project(px, py, ax, ay, bx, by)
            if best is None or d < best[0]:
                best = (d, i, u)
            if best[0] < 100 and ac - shape[best[1]][2] > 2000:
                break                      # well past a close match: stop looking
        if best is None:
            out.append(out[-1] if out else 0.0)
            continue
        _, i, u = best
        dist = shape[i][2] + u * (shape[i + 1][2] - shape[i][2])
        out.append(max(dist, out[-1]) if out else dist)
        i0 = i
    return out


def straight_line(stop_xy):
    out = [0.0]
    for (ax, ay), (bx, by) in zip(stop_xy, stop_xy[1:]):
        out.append(out[-1] + math.hypot(bx - ax, by - ay))
    return out


SCHEMA = """
CREATE TABLE routes (route TEXT PRIMARY KEY COLLATE NOCASE, short_name TEXT, long_name TEXT, color TEXT);
CREATE TABLE patterns (pid INTEGER PRIMARY KEY, route TEXT COLLATE NOCASE, direction INTEGER, shape TEXT);
CREATE TABLE pattern_stops (pid INTEGER, seq INTEGER, stop_id TEXT, dist REAL,
                            PRIMARY KEY (pid, seq)) WITHOUT ROWID;
CREATE TABLE trips (trip_id TEXT PRIMARY KEY, route TEXT COLLATE NOCASE, direction INTEGER,
                    svc TEXT, headsign TEXT, pid INTEGER, t0 INTEGER, t1 INTEGER,
                    offsets TEXT) WITHOUT ROWID;
CREATE TABLE service_dates (date INTEGER, svc TEXT, PRIMARY KEY (date, svc)) WITHOUT ROWID;
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE lanes (shape TEXT, d0 REAL, d1 REAL, kind TEXT, hours TEXT, days INTEGER);
CREATE INDEX lanes_shape ON lanes(shape);
"""


# ---------------------------------------------------------------- bus lanes

def parse_hours(text):
    """"7AM-10AM/4PM-7PM" -> "420-600,960-1140" (minutes after midnight);
    "24 Hours", blank or unreadable -> "all"."""
    t = text.lower().replace(" ", "")
    if not t or t.startswith("24"):
        return "all"
    out = []
    for part in re.split(r"[/,&]|and", t):
        m = re.match(r"(\d{1,2})(?::(\d\d))?(am|pm)?-(\d{1,2})(?::(\d\d))?(am|pm)?$", part)
        if not m:
            continue
        h1, m1, a1, h2, m2, a2 = m.groups()
        a1, a2 = a1 or a2, a2 or a1
        def minutes(h, mm, ap):
            return (int(h) % 12 + (12 if ap == "pm" else 0)) * 60 + int(mm or 0)
        start, end = minutes(h1, m1, a1), minutes(h2, m2, a2)
        if end > start:
            out.append(f"{start}-{end}")
    return ",".join(out) or "all"


def load_lanes(path):
    """Read the DOT bus lane CSV into lane descriptions plus a grid index of
    lane segments (in meters) for fast lookups."""
    csv.field_size_limit(10 ** 9)
    lanes, segs, grid = [], [], {}
    with open(path, newline="", encoding="utf-8-sig") as f:
        for r in csv.DictReader(f):
            lane_type = (r.get("Lane_Type") or "").strip().lower()
            if lane_type in ("enhanced bus stop", "left turn lane"):
                continue
            kind = ("busway" if lane_type == "busway"
                    else "shared" if (r.get("Lane_Type1") or "").strip() == "Shared Lane" else "lane")
            days = {"5": 5, "6": 6}.get((r.get("Days_Code") or "").strip(), 7)
            info = (kind, parse_hours(r.get("Hours") or ""), days,
                    (r.get("Direction") or "").strip().upper())
            li = len(lanes)
            lanes.append(info)
            for part in re.findall(r"\(([^()]+)\)", r.get("the_geom") or ""):
                pts = []
                for pair in part.split(","):
                    lon, lat = map(float, pair.split())
                    pts.append(to_xy(lat, lon))
                for (ax, ay), (bx, by) in zip(pts, pts[1:]):
                    length = math.hypot(bx - ax, by - ay)
                    if length == 0:
                        continue
                    si = len(segs)
                    segs.append((ax, ay, bx, by, (bx - ax) / length, (by - ay) / length, li))
                    for cx in range(int((min(ax, bx) - 30) // 100), int((max(ax, bx) + 30) // 100) + 1):
                        for cy in range(int((min(ay, by) - 30) // 100), int((max(ay, by) + 30) // 100) + 1):
                            grid.setdefault((cx, cy), []).append(si)
    return lanes, segs, grid


def lanes_on_shape(line, lanes, segs, grid):
    """Walk the route shape every ~20 m and note the bus lane under it, if any:
    within 25 m, running parallel, and in the same direction as the bus."""
    samples = []
    for i in range(len(line) - 1):
        ax, ay, ac = line[i]
        bx, by, bc = line[i + 1]
        length = bc - ac
        if length <= 0:
            continue
        ux, uy = (bx - ax) / length, (by - ay) / length
        n = max(1, int(length // 20))
        for k in range(n):
            f = (k + 0.5) / n
            px, py, d = ax + f * (bx - ax), ay + f * (by - ay), ac + f * length
            best = None
            for si in grid.get((int(px // 100), int(py // 100)), ()):
                sx1, sy1, sx2, sy2, vx, vy, li = segs[si]
                if abs(ux * vx + uy * vy) < 0.866:          # not within 30 degrees of parallel
                    continue
                dirn = lanes[li][3]
                if ((dirn == "NB" and uy <= 0) or (dirn == "SB" and uy >= 0) or
                        (dirn == "EB" and ux <= 0) or (dirn == "WB" and ux >= 0)):
                    continue                                 # lane serves the other direction
                gap, _ = project(px, py, sx1, sy1, sx2, sy2)
                if gap <= 25 and (best is None or gap < best[0]):
                    best = (gap, li)
            if best:
                samples.append((d, lanes[best[1]][:3]))
    intervals = []
    for d, sig in samples:
        if intervals and intervals[-1][2] == sig and d - intervals[-1][1] <= 45:
            intervals[-1][1] = d
        else:
            intervals.append([d, d, sig])
    return [(max(0.0, a - 10), b + 10, sig) for a, b, sig in intervals if b - a >= 10]


def import_folder(db, folder, state):
    tag = os.path.basename(os.path.normpath(folder))
    started = time.time()

    stops = {}
    for r in read(folder, "stops.txt"):
        try:
            stops[r["stop_id"]] = to_xy(float(r["stop_lat"]), float(r["stop_lon"]))
        except (KeyError, ValueError):
            pass

    raw = {}
    for r in read(folder, "shapes.txt"):
        raw.setdefault(r["shape_id"], []).append(
            (int(r["shape_pt_sequence"]), float(r["shape_pt_lat"]), float(r["shape_pt_lon"])))
    shapes = {}
    for sid, pts in raw.items():
        pts.sort()
        line, cum, prev = [], 0.0, None
        for _, lat, lon in pts:
            x, y = to_xy(lat, lon)
            if prev:
                cum += math.hypot(x - prev[0], y - prev[1])
            line.append((x, y, cum))
            prev = (x, y)
        shapes[sid] = line
    del raw

    db.executemany("INSERT OR IGNORE INTO routes VALUES (?,?,?,?)",
                   [(r["route_id"], r.get("route_short_name", ""), r.get("route_long_name", ""),
                     r.get("route_color", "")) for r in read(folder, "routes.txt")])

    # Service IDs are prefixed with the folder so different regions can't collide.
    active = set()
    for r in read(folder, "calendar.txt"):
        days = [r.get(d) == "1" for d in ("monday", "tuesday", "wednesday", "thursday",
                                          "friday", "saturday", "sunday")]
        d, end = ymd(r["start_date"]), ymd(r["end_date"])
        while d <= end:
            if days[d.weekday()]:
                active.add((int(d.strftime("%Y%m%d")), f"{tag}:{r['service_id']}"))
            d += timedelta(days=1)
    for r in read(folder, "calendar_dates.txt"):
        key = (int(r["date"]), f"{tag}:{r['service_id']}")
        if r.get("exception_type") == "1":
            active.add(key)
        elif r.get("exception_type") == "2":
            active.discard(key)
    db.executemany("INSERT OR IGNORE INTO service_dates VALUES (?,?)", sorted(active))
    if active:
        ds = [d for d, _ in active]
        state["first"] = min(state.get("first", 99999999), min(ds))
        state["last"] = max(state.get("last", 0), max(ds))

    trips = {}
    for r in read(folder, "trips.txt"):
        if r["trip_id"] in state["seen"]:
            continue
        trips[r["trip_id"]] = (r["route_id"], int(r.get("direction_id") or 0),
                               f"{tag}:{r['service_id']}", r.get("trip_headsign", ""),
                               r.get("shape_id", ""))

    # stop_times can be huge, so sort it on disk rather than in memory.
    tmp_path = state["out"] + ".tmp-stoptimes"
    if os.path.exists(tmp_path):
        os.remove(tmp_path)
    tmp = sqlite3.connect(tmp_path)
    tmp.execute("CREATE TABLE st (trip TEXT, seq INTEGER, t INTEGER, stop TEXT)")
    batch = []
    for r in read(folder, "stop_times.txt"):
        tstr = r.get("arrival_time") or r.get("departure_time")
        batch.append((r["trip_id"], int(r["stop_sequence"]), secs(tstr) if tstr else None, r["stop_id"]))
        if len(batch) >= 200000:
            tmp.executemany("INSERT INTO st VALUES (?,?,?,?)", batch)
            batch = []
    tmp.executemany("INSERT INTO st VALUES (?,?,?,?)", batch)
    tmp.execute("CREATE INDEX st_i ON st(trip, seq)")
    tmp.commit()

    patterns = state["patterns"]
    out_trips, out_patterns, out_pstops = [], [], []

    def flush(trip_id, rows):
        info = trips.get(trip_id)
        if not info or len(rows) < 2:
            return
        route, direction, svc, headsign, shape_id = info
        stop_ids = tuple(r[2] for r in rows)
        key = (route, direction, shape_id, stop_ids)
        pid = patterns.get(key)
        if pid is None:
            xy = [stops.get(s, (0.0, 0.0)) for s in stop_ids]
            shape = shapes.get(shape_id)
            dists = distances_on_shape(xy, shape) if shape and len(shape) > 1 else straight_line(xy)
            pid = len(patterns) + 1
            patterns[key] = pid
            out_patterns.append((pid, route, direction, f"{tag}:{shape_id}"))
            out_pstops.extend((pid, i, s, round(d, 1)) for i, (s, d) in enumerate(zip(stop_ids, dists)))
            state["dists"][pid] = dists
        times = [r[1] for r in rows]
        known = [i for i, t in enumerate(times) if t is not None]
        if len(known) < 2:
            return
        # Fill any blank times by distance between the nearest known times.
        dists = state["dists"][pid]
        for a, b in zip(known, known[1:]):
            for i in range(a + 1, b):
                span = dists[b] - dists[a]
                frac = (dists[i] - dists[a]) / span if span else (i - a) / (b - a)
                times[i] = round(times[a] + frac * (times[b] - times[a]))
        for i in range(known[0]):
            times[i] = times[known[0]]
        for i in range(known[-1] + 1, len(times)):
            times[i] = times[known[-1]]
        t0 = times[0]
        out_trips.append((trip_id, route, direction, svc, headsign, pid, t0, times[-1],
                          ",".join(str(t - t0) for t in times)))
        state["seen"].add(trip_id)

    current, rows = None, []
    for trip, _seq, t, stop in tmp.execute("SELECT trip, seq, t, stop FROM st ORDER BY trip, seq"):
        if trip != current:
            if current is not None:
                flush(current, rows)
            current, rows = trip, []
        rows.append((trip, t, stop))
    if current is not None:
        flush(current, rows)
    tmp.close()
    os.remove(tmp_path)

    if state.get("lanes"):
        lanes, segs, grid = state["lanes"]
        used = {t[4] for t in trips.values()}
        rows = []
        for sid in used:
            if sid in shapes and len(shapes[sid]) > 1:
                for d0, d1, (kind, hours, days) in lanes_on_shape(shapes[sid], lanes, segs, grid):
                    rows.append((f"{tag}:{sid}", round(d0, 1), round(d1, 1), kind, hours, days))
        db.executemany("INSERT INTO lanes VALUES (?,?,?,?,?,?)", rows)
        state["lane_rows"] = state.get("lane_rows", 0) + len(rows)

    db.executemany("INSERT INTO patterns VALUES (?,?,?,?)", out_patterns)
    db.executemany("INSERT INTO pattern_stops VALUES (?,?,?,?)", out_pstops)
    db.executemany("INSERT OR IGNORE INTO trips VALUES (?,?,?,?,?,?,?,?,?)", out_trips)
    db.commit()
    print(f"  {tag}: {len(out_trips):,} trips, {len(out_patterns):,} stop patterns "
          f"({time.time() - started:.0f} s)", flush=True)


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else "gtfs"
    out = sys.argv[2] if len(sys.argv) > 2 else "schedule.sqlite"
    if not os.path.isdir(src):
        sys.exit(f"Folder not found: {src}")
    folders = sorted(os.path.join(src, d) for d in os.listdir(src)
                     if os.path.isfile(os.path.join(src, d, "trips.txt")))
    if not folders and os.path.isfile(os.path.join(src, "trips.txt")):
        folders = [src]
    if not folders:
        sys.exit(f"No GTFS folders (with trips.txt) found inside {src}")

    building = out + ".building"
    if os.path.exists(building):
        os.remove(building)
    db = sqlite3.connect(building)
    db.executescript(SCHEMA)
    state = {"seen": set(), "patterns": {}, "dists": {}, "out": out}
    lanes_csv = "bus_lanes.csv"
    if os.path.exists(lanes_csv):
        state["lanes"] = load_lanes(lanes_csv)
        print(f"Read {len(state['lanes'][0]):,} bus lane segments from {lanes_csv}.", flush=True)
    else:
        print(f"No {lanes_csv} here, so bus lanes are skipped.", flush=True)
    print(f"Reading {len(folders)} GTFS folders. This takes a few minutes.", flush=True)
    for folder in folders:
        import_folder(db, folder, state)

    db.execute("CREATE INDEX trips_route ON trips(route, svc)")
    db.executemany("INSERT INTO meta VALUES (?,?)", [
        ("built", time.strftime("%Y-%m-%d %H:%M")),
        ("first_date", str(state.get("first", ""))),
        ("last_date", str(state.get("last", ""))),
    ])
    db.commit()
    db.execute("VACUUM")
    db.close()
    os.replace(building, out)
    first, last = str(state.get("first", "")), str(state.get("last", ""))
    print(f"\nWrote {out} ({os.path.getsize(out) / 1e6:.0f} MB): {len(state['seen']):,} trips, "
          f"service dates {first[4:6]}/{first[6:]}/{first[:4]} to {last[4:6]}/{last[6:]}/{last[:4]}.")
    if "lanes" in state:
        print(f"Matched bus lanes to {state.get('lane_rows', 0):,} stretches of route.")


if __name__ == "__main__":
    main()

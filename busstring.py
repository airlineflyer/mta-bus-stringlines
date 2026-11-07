#!/usr/bin/env python3
"""
MTA bus stringlines: a bus equivalent of pvibien.com/stringline.htm

One script, two jobs, running together:
  1. Collector: every 30 s, pulls the MTA Bus Time SIRI VehicleMonitoring feed
     for the whole fleet and stores each bus's distance along its route in SQLite.
  2. Server: serves stringline.html and a small JSON/CSV API on http://localhost:8000

Usage:
  export MTA_BUSTIME_KEY=your-key        # free: https://register.developer.obanyc.com/
  python3 busstring.py                   # collect + serve
  python3 busstring.py --routes B63,M15+,Bx12+   # only store these routes
  python3 busstring.py --serve-only      # browse already-collected data

Standard library only (Python 3.8+).
"""
import argparse
import bisect
import csv
import gzip
import io
import json
import math
import os
import re
import sqlite3
import statistics
import sys
import threading
import time
import urllib.parse
import urllib.request
from datetime import date, datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
FEED = "https://bustime.mta.info/api/siri/vehicle-monitoring.json"
POLL_SECONDS = 30          # MTA asks for no more than one request every 30 s
MAX_GAP_SECONDS = 15 * 60  # a gap longer than this breaks a string
BACKSLIDE_METERS = 150     # GPS snapping backwards more than this is dropped
SCHEDULE_DB = os.path.join(HERE, "schedule.sqlite")   # made by gtfs_import.py
STOP_REFRESH_SECONDS = 6 * 3600  # how often to re-fetch a route's full stop list


# ---------------------------------------------------------------- database

def connect(path):
    db = sqlite3.connect(path, check_same_thread=False, timeout=30)
    db.execute("PRAGMA journal_mode=WAL")
    db.executescript("""
    CREATE TABLE IF NOT EXISTS positions (
        route TEXT, direction INTEGER, trip TEXT, vehicle TEXT,
        ts INTEGER, dist REAL, pattern TEXT, dest TEXT,
        next_stop TEXT,
        PRIMARY KEY (vehicle, ts)
    );
    CREATE INDEX IF NOT EXISTS pos_route_ts ON positions(route, ts);
    CREATE TABLE IF NOT EXISTS stops (
        route TEXT, direction INTEGER, pattern TEXT,
        stop_id TEXT, stop_name TEXT, dist REAL, seen INTEGER,
        PRIMARY KEY (route, direction, pattern, stop_id)
    );
    CREATE TABLE IF NOT EXISTS lines (route TEXT PRIMARY KEY, line_ref TEXT);
    -- One row per 10 minutes the collector was running, so missing trips are only
    -- judged for times we were actually watching.
    CREATE TABLE IF NOT EXISTS heartbeat (bucket INTEGER PRIMARY KEY);
    """)
    # Older databases: add the bus status column ("normalProgress|layover" etc.).
    if "progress" not in [r[1] for r in db.execute("PRAGMA table_info(positions)")]:
        db.execute("ALTER TABLE positions ADD COLUMN progress TEXT")
    cols = [r[1] for r in db.execute("PRAGMA table_info(positions)")]
    for col, kind in (("occupancy", "TEXT"), ("load", "INTEGER"), ("capacity", "INTEGER")):
        if col not in cols:     # passenger load: category, count aboard, and capacity, when reported
            db.execute(f"ALTER TABLE positions ADD COLUMN {col} {kind}")
    return db


# ---------------------------------------------------------------- collector

def first(v):
    """SIRI JSON sometimes wraps names in a list."""
    if isinstance(v, list):
        return v[0] if v else None
    return v


def iso_to_epoch(s):
    if not s:
        return None
    s = re.sub(r"\.\d+", "", s)          # drop fractional seconds
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    try:
        return int(datetime.fromisoformat(s).timestamp())
    except ValueError:
        return None


def activities(payload):
    deliveries = payload.get("Siri", {}).get("ServiceDelivery", {}) \
                        .get("VehicleMonitoringDelivery", [])
    for d in deliveries:
        for act in d.get("VehicleActivity", []) or []:
            yield act


def parse_feed(payload, route_filter=None):
    """Yield (position_row, stop_row, line_ref) tuples from a SIRI VehicleMonitoring response."""
    deliveries = payload.get("Siri", {}).get("ServiceDelivery", {}) \
                        .get("VehicleMonitoringDelivery", [])
    for d in deliveries:
        for act in d.get("VehicleActivity", []) or []:
            mvj = act.get("MonitoredVehicleJourney") or {}
            line_ref = mvj.get("LineRef") or ""
            route = line_ref.split("_", 1)[-1]                     # "MTA NYCT_B63" -> "B63"
            if not route or (route_filter and route not in route_filter):
                continue
            call = mvj.get("MonitoredCall") or {}
            dist = ((call.get("Extensions") or {}).get("Distances") or {})
            along = dist.get("CallDistanceAlongRoute")
            from_call = dist.get("DistanceFromCall")
            ts = iso_to_epoch(act.get("RecordedAtTime"))
            if along is None or from_call is None or ts is None:
                continue
            try:
                direction = int(mvj.get("DirectionRef") or 0)
            except ValueError:
                direction = 0
            trip = ((mvj.get("FramedVehicleJourneyRef") or {})
                    .get("DatedVehicleJourneyRef") or "")
            vehicle = mvj.get("VehicleRef") or ""
            pattern = mvj.get("JourneyPatternRef") or ""
            stop_id = call.get("StopPointRef") or ""
            stop_name = first(call.get("StopPointName")) or stop_id
            progress = f"{first(mvj.get('ProgressRate')) or ''}|{first(mvj.get('ProgressStatus')) or ''}"
            caps = (call.get("Extensions") or {}).get("Capacities") or {}
            occupancy = first(mvj.get("Occupancy")) or first(act.get("Occupancy")) or None

            def as_int(v):
                try:
                    return int(v)
                except (TypeError, ValueError):
                    return None
            load, capacity = as_int(caps.get("EstimatedPassengerCount")), as_int(caps.get("EstimatedPassengerCapacity"))
            pos = (route, direction, trip, vehicle, ts,
                   round(float(along) - float(from_call), 1), pattern,
                   first(mvj.get("DestinationName")) or "", stop_name, progress, occupancy, load, capacity)
            stop = (route, direction, pattern, stop_id, stop_name, round(float(along), 1))
            yield pos, stop, line_ref


def get_json(url, timeout):
    """Fetch JSON, asking for a compressed response to cut download size."""
    req = urllib.request.Request(url, headers={"Accept-Encoding": "gzip"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read()
        if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
    return json.loads(raw)


def prune(db, keep_days):
    """Delete positions older than keep_days, one route at a time so each
    delete uses the route index and never locks the database for long."""
    cutoff = int(time.time()) - keep_days * 86400
    removed = 0
    for (route,) in db.execute("SELECT route FROM lines").fetchall():
        with db:
            removed += db.execute("DELETE FROM positions WHERE route=? AND ts<?",
                                  (route, cutoff)).rowcount
    print(f"[{time.strftime('%H:%M:%S')}] removed {removed} positions older than "
          f"{keep_days} days", flush=True)


def collect_once(db, key, route_filter):
    url = FEED + "?" + urllib.parse.urlencode({
        "key": key, "VehicleMonitoringDetailLevel": "normal"})
    payload = get_json(url, 60)
    if "ErrorCondition" in json.dumps(payload)[:2000]:
        raise RuntimeError(json.dumps(payload)[:500])
    rows = list(parse_feed(payload, route_filter))
    with db:
        db.executemany("""INSERT OR IGNORE INTO positions
                          (route, direction, trip, vehicle, ts, dist, pattern, dest, next_stop, progress,
                           occupancy, load, capacity)
                          VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                       [r[0] for r in rows])
        db.executemany("""
            INSERT INTO stops VALUES (?,?,?,?,?,?,1)
            ON CONFLICT(route, direction, pattern, stop_id)
            DO UPDATE SET seen = seen + 1, stop_name = excluded.stop_name,
                          dist = excluded.dist""", [r[1] for r in rows])
        if rows:
            db.execute("INSERT OR IGNORE INTO heartbeat VALUES (?)", (int(time.time()) // 600,))
        db.executemany("INSERT OR REPLACE INTO lines VALUES (?,?)",
                       {(r[1][0], r[2]) for r in rows})
    return len(rows)


_last_stop_fetch = {}
_stop_lock = threading.Lock()


def fetch_route_stops(db, key, route):
    """Ask Bus Time for every running bus on one route with its full list of
    upcoming stops, and store each stop's distance along the route. Runs when a
    route is opened, at most once every few hours per route."""
    if not key:
        return
    with _stop_lock:
        if time.time() - _last_stop_fetch.get(route, 0) < STOP_REFRESH_SECONDS:
            return
        _last_stop_fetch[route] = time.time()
    row = db.execute("SELECT line_ref FROM lines WHERE route=?", (route,)).fetchone()
    if not row or not row[0]:
        _last_stop_fetch.pop(route, None)
        return
    url = FEED + "?" + urllib.parse.urlencode({
        "key": key, "LineRef": row[0], "VehicleMonitoringDetailLevel": "calls"})
    try:
        payload = get_json(url, 20)
    except Exception as e:
        print(f"stop list fetch for {route} failed: {e}", file=sys.stderr, flush=True)
        _last_stop_fetch.pop(route, None)
        return
    stops = []
    for act in activities(payload):
        mvj = act.get("MonitoredVehicleJourney") or {}
        try:
            direction = int(mvj.get("DirectionRef") or 0)
        except ValueError:
            direction = 0
        pattern = mvj.get("JourneyPatternRef") or ""
        calls = ((mvj.get("OnwardCalls") or {}).get("OnwardCall") or [])
        for call in [mvj.get("MonitoredCall") or {}] + list(calls):
            along = (((call.get("Extensions") or {}).get("Distances") or {})
                     .get("CallDistanceAlongRoute"))
            stop_id = call.get("StopPointRef")
            if along is None or not stop_id:
                continue
            stops.append((route, direction, pattern, stop_id,
                          first(call.get("StopPointName")) or stop_id, round(float(along), 1)))
    with db:
        db.executemany("""
            INSERT INTO stops VALUES (?,?,?,?,?,?,1)
            ON CONFLICT(route, direction, pattern, stop_id)
            DO UPDATE SET seen = seen + 1, stop_name = excluded.stop_name,
                          dist = excluded.dist""", stops)
    print(f"[{time.strftime('%H:%M:%S')}] loaded {len(set(s[3] for s in stops))} stops for {route}",
          flush=True)


def collector_loop(db, key, route_filter, keep_days=0):
    last_prune = 0
    while True:
        started = time.time()
        if keep_days and started - last_prune > 3600:
            try:
                prune(db, keep_days)
            except Exception as e:
                print(f"prune error: {e}", file=sys.stderr, flush=True)
            last_prune = started
        try:
            n = collect_once(db, key, route_filter)
            print(f"[{time.strftime('%H:%M:%S')}] stored {n} bus positions", flush=True)
        except Exception as e:  # keep going through network blips
            print(f"[{time.strftime('%H:%M:%S')}] feed error: {e}", file=sys.stderr, flush=True)
        time.sleep(max(1, POLL_SECONDS - (time.time() - started)))


# ---------------------------------------------------------------- queries

def route_sort_key(r):
    m = re.match(r"([A-Za-z]+)(\d+)(.*)", r)
    return (m.group(1).upper(), int(m.group(2)), m.group(3)) if m else (r, 0, "")


def list_routes(db):
    # The small lines table holds one row per route, so this stays instant
    # however much position data has piled up.
    rows = db.execute("SELECT route FROM lines").fetchall()
    if not rows:  # databases from before the lines table existed
        rows = db.execute("SELECT DISTINCT route FROM positions").fetchall()
    return sorted((r[0] for r in rows), key=route_sort_key)


def stop_list(db, route, direction):
    """Stops of the most-observed journey pattern for this route + direction."""
    best = db.execute("""SELECT pattern FROM stops WHERE route=? AND direction=?
                         GROUP BY pattern ORDER BY COUNT(*) DESC, SUM(seen) DESC LIMIT 1""",
                      (route, direction)).fetchone()
    if not best:
        return []
    rows = db.execute("""SELECT stop_name, dist, stop_id FROM stops
                         WHERE route=? AND direction=? AND pattern=? ORDER BY dist""",
                      (route, direction, best[0])).fetchall()
    return [{"name": n, "dist": d, "id": i} for n, d, i in rows]


# ---------------------------------------------------------------- route variants
# Trips that start or end partway along a route (short trips, alternate terminals) report
# their distance from their own first stop, as does the schedule. Everything is drawn on
# one axis, the route's most common variant, so each variant's distances are translated
# onto it through the stops they share.

def bare_stop(stop_id):
    """'MTA_400123' (live feed) and '400123' (schedule) are the same stop."""
    return str(stop_id).split("_", 1)[-1]


def make_mapper(pairs):
    """pairs: [(variant distance, main distance)] at shared stops. Returns a function that
    maps any variant distance onto the main axis (straight lines between shared stops,
    and the nearest offset beyond them), or None if there's nothing to go on."""
    pairs = sorted(set(pairs))
    if not pairs:
        return None
    if len(pairs) == 1:
        off = pairs[0][1] - pairs[0][0]
        return lambda d: d + off
    xs = [a for a, _ in pairs]

    def f(d):
        if d <= xs[0]:
            return d + pairs[0][1] - pairs[0][0]
        if d >= xs[-1]:
            return d + pairs[-1][1] - pairs[-1][0]
        j = bisect.bisect_right(xs, d) - 1
        (a0, b0), (a1, b1) = pairs[j], pairs[j + 1]
        return b0 + (d - a0) / (a1 - a0) * (b1 - b0) if a1 > a0 else b0
    return f


_variant_cache = {}


def live_mappers(db, route):
    """For each (direction, live journey pattern) that isn't the main one, a function
    mapping its distances onto the main pattern's axis. Refreshed every 10 minutes."""
    hit = _variant_cache.get(route)
    if hit and time.time() - hit[0] < 600:
        return hit[1]
    out = {}
    for direction in (0, 1):
        main = {bare_stop(s["id"]): s["dist"] for s in stop_list(db, route, direction)}
        if not main:
            continue
        variants = {}
        for pattern, stop_id, dist in db.execute(
                "SELECT pattern, stop_id, dist FROM stops WHERE route=? AND direction=?", (route, direction)):
            m = main.get(bare_stop(stop_id))
            if m is not None:
                variants.setdefault(pattern, []).append((dist, m))
        for pattern, pairs in variants.items():
            if all(abs(a - b) < 1 for a, b in pairs):
                continue                            # already on the main axis
            f = make_mapper(pairs)
            if f:
                out[(direction, pattern)] = f
    _variant_cache[route] = (time.time(), out)
    return out


def raw_positions(db, route, start, end):
    rows = db.execute("""SELECT route, direction, trip, vehicle, ts, dist, pattern, dest, next_stop, progress,
                                occupancy, load, capacity
                         FROM positions WHERE route=? AND ts BETWEEN ? AND ?
                         ORDER BY trip, vehicle, ts""", (route, start, end)).fetchall()
    maps = live_mappers(db, route)
    if not maps:
        return rows
    out = []
    for r in rows:
        f = maps.get((r[1], r[6]))
        out.append(r if f is None else r[:5] + (round(f(r[5]), 1),) + r[6:])
    return out


def load_level(occupancy, load, capacity):
    """0 = seats available, 1 = standing room only, 2 = full; None if not reported.
    Uses the feed's category; failing that, passengers against capacity (an estimate)."""
    o = (occupancy or "").replace("_", "").lower()
    if o in ("full", "crushedstandingroomonly", "notacceptingpassengers"):
        return 2
    if o in ("standingavailable", "standingroomonly"):
        return 1
    if o in ("seatsavailable", "manyseatsavailable", "fewseatsavailable", "empty"):
        return 0
    if load is not None and capacity:
        r = load / capacity
        return 0 if r < 0.5 else 1 if r < 0.85 else 2
    return None


def clean(rows):
    """Group into strings and drop erroneous updates."""
    groups = {}
    for r in rows:
        groups.setdefault((r[2], r[3]), []).append(r)
    strings = []
    for (trip, vehicle), pts in groups.items():
        seg, occ, cnt, high, last_load = [], [], [], None, None
        for r in pts:
            ts, dist = r[4], r[5]
            if seg and ts - seg[-1][0] > MAX_GAP_SECONDS:
                strings.append((trip, vehicle, r[1], r[7], seg, occ, last_load, cnt))
                seg, occ, cnt, high, last_load = [], [], [], None, None
            if high is not None and dist < high - BACKSLIDE_METERS:
                continue                      # bus "jumped back": GPS noise
            if seg and ts == seg[-1][0]:
                continue
            seg.append((ts, max(dist, high or dist)))
            extra = r[10:13] if len(r) > 12 else (None, None, None)
            occ.append(load_level(*extra))
            cnt.append(extra[1])
            if extra[0] or extra[1] is not None:
                last_load = [extra[0], extra[1], extra[2]]
            high = max(high or dist, dist)
        strings.append((trip, vehicle, pts[0][1], pts[0][7], seg, occ, last_load, cnt))
    return [{"trip": t, "vehicle": v.split("_", 1)[-1], "dir": d, "dest": dest, "pts": s,
             "occ": o if any(x is not None for x in o) else None, "load": ll,
             "cnt": c if any(x is not None for x in c) else None}
            for t, v, d, dest, s, o, ll, c in strings if len(s) >= 3]


# ---------------------------------------------------------------- schedule

def utc_naive(t):
    """UTC date and time for Unix time t, without a time zone attached."""
    return datetime.fromtimestamp(t, timezone.utc).replace(tzinfo=None)


def is_eastern_dst(d):
    """US Eastern daylight time is in effect at local midnight on day d."""
    mar1, nov1 = date(d.year, 3, 1), date(d.year, 11, 1)
    second_sunday_march = mar1 + timedelta(days=(6 - mar1.weekday()) % 7 + 7)
    first_sunday_nov = nov1 + timedelta(days=(6 - nov1.weekday()) % 7)
    return second_sunday_march < d <= first_sunday_nov


def ny_midnight(d):
    """Unix time of 12:00 AM New York time on day d."""
    return (d - date(1970, 1, 1)).days * 86400 + (4 if is_eastern_dst(d) else 5) * 3600


def strip_agency(ref):
    """"MTA NYCT_CA_B6-Weekday-..." -> "CA_B6-Weekday-..." (the GTFS trip_id)."""
    return ref.split("_", 1)[1] if "_" in ref else ref


def schedule_for(db, route, start, end):
    """Scheduled trips overlapping [start, end], each marked ran True/False, or None
    when it can't be judged (still under way, or the collector wasn't running)."""
    if not os.path.exists(SCHEDULE_DB):
        return None, None
    sdb = sqlite3.connect(f"file:{SCHEDULE_DB}?mode=ro", uri=True)
    try:
        trips, pattern_dists, main_stops = [], {}, {}
        d = utc_naive(start).date() - timedelta(days=2)
        last = utc_naive(end).date()
        while d <= last:
            mid, key = ny_midnight(d), int(d.strftime("%Y%m%d"))
            for trip_id, direction, headsign, pid, t0, t1, offsets in sdb.execute("""
                    SELECT t.trip_id, t.direction, t.headsign, t.pid, t.t0, t.t1, t.offsets
                    FROM trips t JOIN service_dates s ON s.svc = t.svc AND s.date = ?
                    WHERE t.route = ? AND t.t0 <= ? AND t.t1 >= ?""",
                    (key, route, end - mid, start - mid)):
                if pid not in pattern_dists:
                    ps = sdb.execute("SELECT stop_id, dist FROM pattern_stops WHERE pid=? ORDER BY seq",
                                     (pid,)).fetchall()
                    if direction not in main_stops:
                        main_stops[direction] = {bare_stop(s["id"]): s["dist"]
                                                 for s in stop_list(db, route, direction)}
                    ms = main_stops[direction]
                    f = make_mapper([(dd, ms[bare_stop(sid)]) for sid, dd in ps if bare_stop(sid) in ms])
                    pattern_dists[pid] = [round(f(dd), 1) if f else dd for _, dd in ps]
                dists = pattern_dists[pid]
                offs = [int(o) for o in offsets.split(",")]
                pts = [[mid + t0 + o, dist] for o, dist in zip(offs, dists)]
                trips.append({"trip": trip_id, "dir": direction, "dest": headsign,
                              "start": mid + t0, "end": mid + t1, "pts": pts})
            d += timedelta(days=1)
    finally:
        sdb.close()

    # Which of them did a bus actually run? Match on the trip ID in the live feed.
    ran = set()
    for (trip,) in db.execute("SELECT DISTINCT trip FROM positions WHERE route=? AND ts BETWEEN ? AND ?",
                              (route, start - 3 * 3600, end + 3600)):
        ran.add(trip)
        ran.add(strip_agency(trip))
    watched = {b for (b,) in db.execute("SELECT bucket FROM heartbeat WHERE bucket BETWEEN ? AND ?",
                                        ((start - 4 * 3600) // 600, (end + 3600) // 600))}
    now = time.time()
    for tr in trips:
        if tr["trip"] in ran:
            tr["ran"] = True
        elif tr["end"] > now - 600:
            tr["ran"] = None          # not finished yet (plus 10 minutes' grace)
        elif all(b in watched for b in range(tr["start"] // 600, tr["end"] // 600 + 1)):
            tr["ran"] = False
        else:
            tr["ran"] = None          # collector wasn't running for part of the trip

    note = None
    judged = [t for t in trips if t["ran"] is not None]
    if len(judged) >= 5 and sum(t["ran"] for t in judged) < 0.3 * len(judged):
        # Almost nothing matched: the live trip IDs don't line up with this
        # schedule (usually because the schedule is out of date). Don't guess.
        for t in trips:
            if t["ran"] is False:
                t["ran"] = None
        note = ("Live trips don't match this schedule’s trip IDs for this route, so missing "
                "trips can’t be identified. The schedule may be out of date.")
    return trips, note


def lanes_for(route):
    """Bus lane stretches along the route's most common shape in each direction,
    or None if the schedule file has no bus lane data."""
    if not os.path.exists(SCHEDULE_DB):
        return None
    sdb = sqlite3.connect(f"file:{SCHEDULE_DB}?mode=ro", uri=True)
    try:
        if not sdb.execute("SELECT 1 FROM sqlite_master WHERE name='lanes'").fetchone() or \
                not sdb.execute("SELECT 1 FROM lanes LIMIT 1").fetchone():
            return None
        out = {}
        for direction in (0, 1):
            row = sdb.execute("""SELECT p.shape FROM trips t JOIN patterns p ON p.pid = t.pid
                                 WHERE t.route = ? AND t.direction = ?
                                 GROUP BY p.shape ORDER BY COUNT(*) DESC LIMIT 1""",
                              (route, direction)).fetchone()
            out[str(direction)] = [] if not row else [
                {"d0": d0, "d1": d1, "kind": kind, "hours": hours, "days": days}
                for d0, d1, kind, hours, days in sdb.execute(
                    "SELECT d0, d1, kind, hours, days FROM lanes WHERE shape=? ORDER BY d0", (row[0],))]
        return out
    finally:
        sdb.close()


# ---------------------------------------------------------------- problem areas

PERIODS = [  # (key, phrase, start minute, end minute), New York time
    ("overnight", "overnight", 0, 360),
    ("am", "in the morning rush", 360, 600),
    ("midday", "midday", 600, 900),
    ("pm", "in the afternoon rush", 900, 1140),
    ("evening", "in the evening", 1140, 1440),
]
PROBLEM_CACHE_SECONDS = 1800
_problem_cache = {}


def ny_local(t):
    """(New York date, minute of day) for Unix time t."""
    d = utc_naive(t - 5 * 3600).date()
    local = t - (4 if is_eastern_dst(d) else 5) * 3600
    return utc_naive(local).date(), (local % 86400) // 60


def period_of(minute):
    return next(p[0] for p in PERIODS if p[2] <= minute < p[3])


def crossing_time(pts, dist):
    """When a string first reaches dist, interpolated; None if it doesn't cross
    it, or if readings around the crossing are more than 5 minutes apart."""
    if not pts or pts[0][1] >= dist or pts[-1][1] < dist:
        return None
    for (t0, d0), (t1, d1) in zip(pts, pts[1:]):
        if d1 >= dist:
            if t1 - t0 > 300:
                return None
            return t0 + (dist - d0) / (d1 - d0) * (t1 - t0) if d1 > d0 else t0
    return None


def consistent(obs, test, min_per_day):
    """obs: [(day, value)]. The test must hold overall and on at least 60% of the
    days that have enough observations. Returns (flagged days, judged days) or None."""
    if not test([v for _, v in obs]):
        return None
    by_day = {}
    for day, v in obs:
        by_day.setdefault(day, []).append(v)
    judged = [vals for vals in by_day.values() if len(vals) >= min_per_day]
    if not judged:
        return None
    flagged = sum(1 for vals in judged if test(vals))
    return (flagged, len(judged)) if flagged >= max(1, math.ceil(0.6 * len(judged))) else None


def find_problems(db, route):
    """Stretches of each direction where, across all stored days, buses are
    consistently slow, often delayed, bunched or leaving long gaps."""
    cached = _problem_cache.get(route)
    if cached and time.time() - cached[0] < PROBLEM_CACHE_SECONDS:
        return cached[1]
    now = int(time.time())
    trips = clean(raw_positions(db, route, now - 7 * 86400, now))
    watched = {b for (b,) in db.execute("SELECT bucket FROM heartbeat WHERE bucket >= ?",
                                        ((now - 7 * 86400) // 600,))}
    days_seen = {ny_local(p[0])[0] for tr in trips for p in tr["pts"][:1]}
    out = {"days": len(days_seen)}
    for direction in (0, 1):
        stops = stop_list(db, route, direction)
        out[str(direction)] = []
        if len(stops) < 4:
            continue
        bounds = [s["dist"] for s in stops]
        names = [s["name"] for s in stops]
        travel, passes = {}, {}
        for tr in trips:
            if tr["dir"] != direction:
                continue
            cs = crossings(tr["pts"], bounds)
            for k, t in enumerate(cs):
                if t is not None:
                    passes.setdefault(k, []).append(t)
            for k in range(len(bounds) - 1):
                a, b = cs[k], cs[k + 1]
                if a is not None and b is not None and b > a and bounds[k + 1] - bounds[k] >= 80:
                    day, minute = ny_local(a)
                    travel.setdefault((k, period_of(minute)), []).append((day, b - a))

        # The route's overall speed for each time of day, as the yardstick for "slow".
        totals = {}
        for (k, per), obs in travel.items():
            t = totals.setdefault(per, [0.0, 0.0])
            t[0] += (bounds[k + 1] - bounds[k]) * len(obs)
            t[1] += sum(v for _, v in obs)
        ref = {per: d / t for per, (d, t) in totals.items() if t > 0}

        found = []
        for (k, per), obs in travel.items():
            if len(obs) < 10 or per not in ref:
                continue
            length = bounds[k + 1] - bounds[k]
            slow = consistent(obs, lambda v: length / statistics.median(v) <= 0.6 * ref[per], 5)
            if slow:
                speed = length / statistics.median([v for _, v in obs])
                found.append({"kind": "slow", "k0": k, "k1": k + 1, "per": per, "days": slow,
                              "sev": min(1.0, (1 - speed / ref[per]) / 0.6),
                              "len": length, "time": statistics.median([v for _, v in obs]),
                              "ref": ref[per]})

            def unreliable(v):
                v = sorted(v)
                med, p90 = statistics.median(v), v[int(0.9 * (len(v) - 1))]
                return p90 >= 2 * med and p90 - med >= 90
            late = consistent(obs, unreliable, 5)
            if late:
                v = sorted(x for _, x in obs)
                med, p90 = statistics.median(v), v[int(0.9 * (len(v) - 1))]
                found.append({"kind": "delays", "k0": k, "k1": k + 1, "per": per, "days": late,
                              "sev": min(1.0, (p90 / med - 1) / 3), "med": med, "p90": p90})

        # Headways at each stop (skipping the first two, where buses are just starting
        # out), only across stretches of time when the collector was running.
        for k, ts in passes.items():
            if k < 2 or k >= len(bounds):
                continue
            ts.sort()
            by_per = {}
            for a, b in zip(ts, ts[1:]):
                h = b - a
                if h <= 0 or h > 7200:
                    continue
                if not all(bk in watched for bk in range(int(a) // 600, int(b) // 600 + 1)):
                    continue
                day, minute = ny_local(a)
                by_per.setdefault(period_of(minute), []).append((day, h))
            for per, obs in by_per.items():
                if len(obs) < 10:
                    continue
                typical = statistics.median([h for _, h in obs])
                if typical < 240:
                    continue          # buses every few minutes: bunching is hard to define
                share_close = lambda v: sum(h < 0.3 * typical for h in v) / len(v)
                share_long = lambda v: sum(h > 2 * typical and h - typical >= 300 for h in v) / len(v)
                bunch = consistent(obs, lambda v: share_close(v) >= 0.25, 5)
                if bunch:
                    rate = share_close([h for _, h in obs])
                    found.append({"kind": "bunching", "k0": k - 0.5, "k1": k + 0.5, "per": per,
                                  "days": bunch, "sev": min(1.0, rate / 0.5), "rate": rate})
                gaps = consistent(obs, lambda v: share_long(v) >= 0.2, 5)
                if gaps:
                    rate = share_long([h for _, h in obs])
                    found.append({"kind": "gaps", "k0": k - 0.5, "k1": k + 0.5, "per": per,
                                  "days": gaps, "sev": min(1.0, rate / 0.4), "rate": rate,
                                  "typical": typical})

        # Bunching that rarely gets fixed: of the times buses bunched, few were spaced
        # out again before the end of the line.
        mg = management(trips, direction, bounds, names, full=False)
        if mg:
            by_per = {}
            for e in mg["events"]:
                if e["outcome"] == "unknown":
                    continue
                day, minute = ny_local(e["t0"])
                by_per.setdefault(period_of(minute), []).append(
                    (day, (e["outcome"] in ("recovered", "short-turn", "spaced by another bus"), e["k0"])))
            for per, obs in by_per.items():
                if len(obs) < 8:
                    continue
                rate = lambda v: sum(fixed for fixed, _ in v) / len(v)
                rarely = consistent(obs, lambda v: rate(v) < 0.3, 3)
                if rarely:
                    k0 = int(statistics.median([k for _, (_, k) in obs]))
                    r = rate([v for _, v in obs])
                    found.append({"kind": "unmanaged", "k0": k0, "k1": len(bounds) - 1, "per": per,
                                  "days": rarely, "sev": min(1.0, 1 - r), "rate": r, "count": len(obs),
                                  "start_name": names[k0]})

        # Join neighbouring stretches with the same problem at the same time of day.
        found.sort(key=lambda f: (f["kind"], f["per"], f["k0"]))
        merged = []
        for f in found:
            m = merged[-1] if merged else None
            if m and m["kind"] == f["kind"] and m["per"] == f["per"] and f["k0"] <= m["k1"]:
                m["k1"] = max(m["k1"], f["k1"])
                m["sev"] = max(m["sev"], f["sev"])
                m["days"] = max(m["days"], f["days"])
                for key in ("len", "time"):
                    if key in f:
                        m[key] += f[key]
                for key in ("rate",):
                    if key in f:
                        m[key] = max(m[key], f[key])
                if "p90" in f:
                    m["med"], m["p90"] = m["med"] + f["med"], m["p90"] + f["p90"]
            else:
                merged.append(dict(f))

        def at(kpos):      # distance at a stop index, or halfway between two stops
            lo = int(math.floor(kpos))
            lo = max(0, min(lo, len(bounds) - 1))
            hi = min(lo + 1, len(bounds) - 1)
            return bounds[lo] + (kpos - lo) * (bounds[hi] - bounds[lo])

        for f in merged:
            per = next(p for p in PERIODS if p[0] == f["per"])
            a, b = names[max(0, math.ceil(f["k0"]))], names[min(len(names) - 1, math.floor(f["k1"]))]
            where = f"at {a}" if a == b else f"between {a} and {b}"
            flagged, judged = f["days"]
            days_txt = f"{flagged} of {judged} days" if judged > 1 else "1 day so far"
            if f["kind"] == "slow":
                text = (f"Slow {where} {per[1]}: buses average {f['len'] / f['time'] * 2.23694:.1f} mph here, "
                        f"vs {f['ref'] * 2.23694:.1f} mph across the route ({days_txt}).")
            elif f["kind"] == "delays":
                text = (f"Frequent delays {where} {per[1]}: this usually takes {f['med'] / 60:.0f} min, "
                        f"but 1 in 10 trips takes {f['p90'] / 60:.0f} min or more ({days_txt}).")
            elif f["kind"] == "unmanaged":
                text = (f"Bunching rarely fixed {per[1]}: buses bunched {f['count']} times, usually from around "
                        f"{f['start_name']}, and only {f['rate'] * 100:.0f}% were spaced out again before the "
                        f"end of the line ({days_txt}).")
            elif f["kind"] == "bunching":
                text = (f"Bunching {where} {per[1]}: {f['rate'] * 100:.0f}% of buses arrive right behind "
                        f"the bus ahead ({days_txt}).")
            else:
                text = (f"Long gaps {where} {per[1]}: {f['rate'] * 100:.0f}% of waits between buses are "
                        f"more than double the usual {f['typical'] / 60:.0f} min ({days_txt}).")
            out[str(direction)].append({"d0": at(f["k0"]), "d1": at(f["k1"]), "kind": f["kind"],
                                        "hours": f"{per[2]}-{per[3]}", "days": 7,
                                        "sev": round(f["sev"], 2), "text": text})
        out[str(direction)].sort(key=lambda f: -f["sev"])
    _problem_cache[route] = (time.time(), out)
    return out


# ---------------------------------------------------------------- service management

BUNCHED = 0.3        # gap below this share of the usual gap = bunched
RECOVERED = 0.6      # gap back above this share = spaced out again
SIGN_WORDS = ("NOT IN SERVICE", "DROP OFF", "DROP-OFF", "LIMITED", "LTD", "EXPRESS", "NIS")


def crossings(pts, bounds, max_gap=300):
    """When a string first reaches each distance in bounds (ascending), in one
    pass; None where it doesn't cross, or readings around it are more than
    max_gap seconds apart (5 minutes unless asked otherwise)."""
    out = [None] * len(bounds)
    if len(pts) < 2:
        return out
    j = 0
    for k, dist in enumerate(bounds):
        if pts[0][1] >= dist or pts[-1][1] < dist:
            continue
        while j + 1 < len(pts) and pts[j + 1][1] < dist:
            j += 1
        if j + 1 >= len(pts):
            break
        (t0, d0), (t1, d1) = pts[j], pts[j + 1]
        if t1 - t0 <= max_gap:
            out[k] = t0 + (dist - d0) / (d1 - d0) * (t1 - t0) if d1 > d0 else t0
    return out


def dist_at(pts, t):
    """Where a string was at time t (interpolated)."""
    for (t0, d0), (t1, d1) in zip(pts, pts[1:]):
        if t0 <= t <= t1:
            return d0 + (d1 - d0) * ((t - t0) / (t1 - t0) if t1 > t0 else 0)
    return pts[0][1] if t < pts[0][0] else pts[-1][1]


def mins_txt(sec):
    return f"{max(0, round(sec / 60))} min"


def management(trips, direction, bounds, names, other_bounds=None, sched_ids=None,
               sched_ends=None, extra_ok=False, status=None, signs=None, full=True, checks=None,
               sched_pts=None):
    """Bunching events in one direction, how each ended, and interventions around
    them. full=False skips the window-only extras (markers, passes, short-turns)."""
    T = [t for t in trips if t["dir"] == direction]
    n = len(bounds)
    if n < 5 or len(T) < 2:
        return None
    first, last = bounds[0], bounds[-1]
    cs = [crossings(t["pts"], bounds) for t in T]

    # Usual gap at each stop, by time of day.
    per_stop, typ = [], {}
    for k in range(n):
        ts = sorted((c[k], i) for i, c in enumerate(cs) if c[k] is not None)
        per_stop.append(ts)
        gaps = {}
        for (ta, _), (tb, _) in zip(ts, ts[1:]):
            if 0 < tb - ta < 3 * 3600:
                gaps.setdefault(period_of(ny_local(ta)[1]), []).append(tb - ta)
        for per, g in gaps.items():
            if len(g) >= 4:
                typ[(k, per)] = statistics.median(g)

    def usual(k, t):
        g = typ.get((k, period_of(ny_local(t)[1])))
        return g if g and g >= 240 else None

    markers, actions = [], []          # actions: (time, trip index, kind, short description)
    label = lambda i: f"Bus {T[i]['vehicle']}"

    # Holds: stationary 2+ minutes at a stop mid-route while close behind another bus,
    # and the bus ahead kept moving. If the bus ahead was stuck too, something on the
    # route (traffic, an incident) is holding them up, not a dispatcher.
    speeds = [(t["pts"][-1][1] - t["pts"][0][1]) / (t["pts"][-1][0] - t["pts"][0][0])
              for t in T if t["pts"][-1][0] - t["pts"][0][0] >= 600]
    usual_speed = statistics.median(speeds) if speeds else 3.6      # meters per second
    holds = 0
    all_waits = {}                     # trip index -> [(start, end, where)], for the stuck-together check
    for i, tr in enumerate(T):
        p = tr["pts"]
        pieces, a = [], 0
        while a < len(p) - 1:
            b = a
            while b + 1 < len(p) and p[b + 1][1] - p[a][1] < 30:
                b += 1
            if b > a and p[b][0] - p[a][0] >= 60:
                pieces.append([a, b])
            a = max(a, b) + 1
        joined = []
        for a, b in pieces:
            if joined and p[a][0] - p[joined[-1][1]][0] <= 180 and p[a][1] - p[joined[-1][1]][1] <= 150:
                joined[-1][1] = b
            else:
                joined.append([a, b])
        all_waits[i] = [(p[a][0], p[b][0], p[b][1]) for a, b in joined if p[b][0] - p[a][0] >= 90]
    for i, tr in enumerate(T):
        p, st = tr["pts"], (status or {}).get((tr["trip"], tr["vehicle"]), {})
        # Stationary pieces of a minute or more, joined into one wait when a bus stops, creeps
        # up a little (no more than 150 m in no more than 3 minutes: to the stop, or forward in
        # a queue) and stops again.
        pieces, a = [], 0
        while a < len(p) - 1:
            b = a
            while b + 1 < len(p) and p[b + 1][1] - p[a][1] < 30:
                b += 1
            if b > a and p[b][0] - p[a][0] >= 60:
                pieces.append([a, b])
            a = max(a, b) + 1
        waits = []
        for a, b in pieces:
            if waits and p[a][0] - p[waits[-1][1]][0] <= 180 and p[a][1] - p[waits[-1][1]][1] <= 150:
                waits[-1][1] = b
            else:
                waits.append([a, b])
        for a, b in waits:
            dur = p[b][0] - p[a][0]
            if dur < 120:
                continue
            here = p[b][1]                                  # where it ended up waiting
            k = min(range(n), key=lambda kk: abs(bounds[kk] - here))
            layover = any(("layover" in st.get(pt[0], "") or "prevTrip" in st.get(pt[0], ""))
                          for pt in p[a:b + 1])
            why, kind, g, before, after, lead_moved, behind = None, None, None, None, None, None, None
            stretch_info = None
            if not 2 <= k <= n - 3:
                why = "at or next to the end of the line"
            elif abs(bounds[k] - here) > 150:
                why = f"not at a stop ({abs(bounds[k] - here):.0f} m from {names[k]})"
            elif layover:
                why = "the bus reported a layover"
            else:
                g = usual(k, p[a][0])
                ahead = [(t, j) for t, j in per_stop[k] if j != i and t <= p[a][0]]
                later = [t for t, j in per_stop[k] if j != i and t > p[a][0]]
                if ahead:
                    lp = T[ahead[-1][1]]["pts"]
                    if lp[-1][0] >= p[b][0] or lp[-1][1] >= last - 200:   # tracked through the wait
                        lead_moved = dist_at(lp, p[b][0]) - dist_at(lp, p[a][0])
                    before, after = p[a][0] - ahead[-1][0], p[b][0] - ahead[-1][0]
                if later:
                    behind = later[0] - p[a][0]                 # how far back the next bus was
                # Other buses stopped within 300 m, overlapping this wait or ending within 2 minutes
                # before it began: a blockage catches several buses at once; a hold is one bus.
                stuck_with = sorted({T[j]["vehicle"] for j, ws in all_waits.items() if j != i
                                     for (oa, ob, ow) in ws
                                     if abs(ow - here) <= 300 and ob >= p[a][0] - 120 and oa <= p[b][0]})
                # A habitually slow spot (traffic, a busy transfer): if 30%+ of the other buses
                # passing here also stopped 90+ seconds nearby at some point, a wait only counts
                # as a hold if it's at least twice the typical stop here.
                slow_spot = None
                others = {}
                for j, ws in all_waits.items():
                    if j != i:
                        for (oa, ob, ow) in ws:
                            if abs(ow - here) <= 300:
                                others[j] = max(others.get(j, 0), ob - oa)
                passing = len({j for _, j in per_stop[k] if j != i})
                # And where buses crawl rather than stop: compare this bus's time through the
                # 600 m around the wait with other buses' typical time through it. A hold has
                # to make it at least 2 minutes and 1.75 times slower than typical.
                slow_stretch = None
                z0, z1 = max(first, here - 300), min(last, here + 300)

                def at(pts, dist):              # like crossing_time, but a long wait doesn't void it
                    if not pts or pts[0][1] >= dist or pts[-1][1] < dist:
                        return None
                    for (t0, d0), (t1, d1) in zip(pts, pts[1:]):
                        if d1 >= dist:
                            return t0 + (dist - d0) / (d1 - d0) * (t1 - t0) if d1 > d0 else t0

                def through(pts):
                    ta, tb = at(pts, z0), at(pts, z1)
                    return tb - ta if ta is not None and tb is not None and tb > ta else None
                mine = through(p)
                theirs = [x for j, o in enumerate(T) if j != i for x in [through(o["pts"])] if x is not None]
                if mine is not None and len(theirs) >= 3:
                    typical_through = statistics.median(theirs)
                    stretch_info = (typical_through, mine, len(theirs))
                    if mine - typical_through < 120 or mine < 1.75 * typical_through:
                        slow_stretch = (typical_through, mine, len(theirs))
                if len(others) >= max(2, 0.3 * passing):
                    typical = statistics.median(others.values())
                    if dur < 2 * typical:
                        slow_spot = (len(others), passing, typical)
                if not ahead:
                    why = "no bus seen passing this stop ahead of it"
                elif lead_moved is None:
                    why = "the bus ahead’s tracking dropped out, so it can’t be told whether the route was moving"
                elif lead_moved < 0.75 * usual_speed * dur:
                    why = (f"the bus ahead was held up too (moved {lead_moved:.0f} m; the route has to be moving "
                           f"near its usual pace, at least {0.75 * usual_speed * dur:.0f} m)")
                elif stuck_with:
                    why = (f"other buses were stopped near the same spot at the same time "
                           f"({', '.join('bus ' + v for v in stuck_with)}): looks like the route was blocked")
                elif slow_stretch:
                    why = (f"this stretch is slow for every bus: others typically take {mins_txt(slow_stretch[0])} "
                           f"to get through it ({slow_stretch[2]} buses), and this bus took {mins_txt(slow_stretch[1])}, "
                           f"not unusually long")
                elif slow_spot:
                    why = (f"buses often stop here: {slow_spot[0]} of {slow_spot[1]} other buses stopped 1.5+ min "
                           f"near this spot, typically {mins_txt(slow_spot[2])}, so a {mins_txt(dur)} wait isn’t "
                           f"unusual for it")
                else:
                    # The route was moving. Which kind of hold, if any, explains the wait?
                    sp = None
                    if sched_pts:
                        sp = sched_pts.get(tr["trip"], sched_pts.get(strip_agency(tr["trip"])))
                    due = crossing_time(sp, bounds[k]) if sp else None
                    if g and before < 0.5 * g:
                        kind = "spacing"
                    elif (behind is not None and before < behind - 120
                          and abs(after - (behind - dur)) < abs(before - behind)):
                        kind = "evening"
                    elif due is not None and due - p[a][0] >= 60:
                        kind = "schedule"
                    else:
                        kind = "wait"
            result = why or {"spacing": "HOLD (too close behind the bus ahead)",
                             "evening": "HOLD (evening out the gaps ahead and behind)",
                             "schedule": "HOLD (running early against the schedule)",
                             "wait": "LONG WAIT (route moving; not explained by spacing or schedule)"}[kind]
            if checks is not None:
                if kind:                         # a hold: show how the stretch comparison came out
                    if stretch_info is None:
                        result += " [time through this stretch: couldn’t be measured]"
                    else:
                        result += (f" [time through this stretch: {stretch_info[1] / 60:.1f} min, vs typically "
                                   f"{stretch_info[0] / 60:.1f} min from {stretch_info[2]} other buses]")
                checks.append({"dir": direction, "bus": tr["vehicle"], "t": p[a][0], "minutes": round(dur / 60, 1),
                               "stop": names[k], "result": result})
            if why:
                continue
            moved = f"The bus ahead kept moving, covering {lead_moved / 1609.34:.1f} mi, so the route wasn’t blocked."
            gap_txt = f"the gap to the bus ahead went from {mins_txt(before)} to {mins_txt(after)}"
            if kind == "wait":           # unexplained stops (traffic, a ramp, who knows): diagnostic only
                continue
            if kind == "spacing":
                reason = (f"while close behind the bus ahead; {gap_txt}, against a usual gap of {mins_txt(g)} here")
            elif kind == "evening":
                reason = (f"while {mins_txt(before)} behind the bus ahead but {mins_txt(behind)} ahead of the bus "
                          f"behind; holding evened out the two gaps")
            else:
                reason = (f"after arriving {mins_txt(due - p[a][0])} early against its schedule; it left "
                          f"{mins_txt(abs(p[b][0] - due))} {'after' if p[b][0] >= due else 'before'} its scheduled time")
            holds += 1
            actions.append((p[a][0], i, "hold", f"{label(i).lower()} held {mins_txt(dur)} at {names[k]}, {gap_txt}"))
            markers.append({"type": "hold", "t": p[a][0], "dist": here, "trip": tr["trip"],
                            "text": f"{label(i)} waited {mins_txt(dur)} at {names[k]} {reason}. {moved} "
                                    f"Consistent with a hold."})

    # Express or drop-off-only running: 3+ stops much faster than usual.
    # Typical travel time between stops, by time of day (buses run much faster at night).
    seg_by = {}
    for c in cs:
        for k in range(n - 1):
            if c[k] is not None and c[k + 1] is not None and c[k + 1] > c[k]:
                seg_by.setdefault((k, period_of(ny_local(c[k])[1])), []).append(c[k + 1] - c[k])
    seg_typ = {key: statistics.median(v) for key, v in seg_by.items() if len(v) >= 5}
    express = 0
    def seg_usual(k, t):
        return seg_typ.get((k, period_of(ny_local(t)[1])))
    for i, c in enumerate(cs):
        k = 0
        while k < n - 1:
            run_end, saved = k, 0.0
            while (run_end < n - 1 and c[run_end] is not None and c[run_end + 1] is not None
                   and seg_usual(run_end, c[run_end])
                   and c[run_end + 1] - c[run_end] < 0.6 * seg_usual(run_end, c[run_end])):
                saved += seg_usual(run_end, c[run_end]) - (c[run_end + 1] - c[run_end])
                run_end += 1
            # A bus right behind another runs fast because the bus ahead picked everyone up:
            # that's not express running. Only count a fast stretch when the bus had a
            # reasonable gap ahead (70%+ of the usual), as a late bus told to skip pickups does.
            ahead = [t for t, j in per_stop[k] if j != i and t < c[k]] if run_end - k >= 4 else []
            g_here = usual(k, c[k]) if ahead else None
            clear_ahead = bool(ahead) and g_here is not None and c[k] - ahead[-1] >= 0.7 * g_here
            if run_end - k >= 4 and saved >= 120 and clear_ahead:
                express += 1
                actions.append((c[k], i, "express",
                                f"{label(i).lower()} ran express or drop-off only from {names[k]} to {names[run_end]}"))
                behind = [t for t, j in per_stop[k] if t > c[k]]
                behind2 = [t for t, j in per_stop[run_end] if t > c[run_end]]
                gap_txt = (f" The gap to the bus behind went from {mins_txt(behind[0] - c[k])} to "
                           f"{mins_txt(behind2[0] - c[run_end])}." if behind and behind2 else "")
                markers.append({"type": "express", "t": c[k], "dist": bounds[k], "trip": T[i]["trip"],
                                "t1": c[run_end], "dist1": bounds[run_end],
                                "text": f"{label(i)} ran {mins_txt(saved)} faster than usual from {names[k]} to "
                                        f"{names[run_end]}, consistent with running express or drop-off only.{gap_txt}"})
                k = run_end
            else:
                k += 1

    # Sign changes mid-trip, e.g. to NOT IN SERVICE or DROP OFF ONLY.
    for i, tr in enumerate(T):
        for t, new in (signs or {}).get((tr["trip"], tr["vehicle"]), []):
            if any(w in new.upper() for w in SIGN_WORDS) and tr["pts"][0][0] <= t <= tr["pts"][-1][0]:
                actions.append((t, i, "sign", f"{label(i).lower()} changed its sign to “{new}”"))
                markers.append({"type": "sign", "t": t, "dist": dist_at(tr["pts"], t), "trip": tr["trip"],
                                "text": f"{label(i)} changed its sign to “{new}” partway through the trip."})

    # Passes: follow each pair of buses along the route. A pass is when one was clearly
    # ahead (30+ seconds) at some stop and the other is clearly ahead at a later stop,
    # however many stops apart; the marker goes where they actually swapped. Buses running
    # side by side and swapping back and forth by a few seconds are never clearly ahead,
    # so that GPS jitter doesn't count.
    passes = 0
    if full:
        for ia in range(len(T)):
            for ib in range(ia + 1, len(T)):
                common = [k for k in range(n) if cs[ia][k] is not None and cs[ib][k] is not None]
                if len(common) < 2:
                    continue
                prev_conf, prev_k = 0, None
                for k in common:
                    d = cs[ib][k] - cs[ia][k]          # positive: bus a passed this stop first
                    conf = 1 if d >= 30 else -1 if d <= -30 else 0
                    if conf and prev_conf and conf != prev_conf:
                        # Where between the two confident stops did the order flip?
                        span = [kk for kk in common if prev_k <= kk <= k]
                        ks = next((span[x] for x in range(1, len(span))
                                   if (cs[ib][span[x]] - cs[ia][span[x]]) * prev_conf <= 0), k)
                        kp = span[max(0, span.index(ks) - 1)]
                        ahead, behind = (ib, ia) if conf < 0 else (ia, ib)   # who's ahead now
                        t = (cs[ia][ks] + cs[ib][ks]) / 2
                        passes += 1
                        actions.extend([(t, ia, "pass", ""), (t, ib, "pass", "")])
                        where = (f"between {names[kp]} and {names[ks]}" if kp != ks else f"at {names[ks]}")
                        markers.append({"type": "pass", "t": t, "dist": (bounds[kp] + bounds[ks]) / 2,
                                        "trip": T[ahead]["trip"],
                                        "text": f"{label(ahead)} passed {label(behind).lower()} {where}."})
                    if conf:
                        prev_conf, prev_k = conf, k

    # Short-turns: a trip ends well short of the line's end, and the same bus soon
    # starts the other direction from about the same place.
    short_turned = set()
    if full and other_bounds:
        L, Lo = last, other_bounds[-1]
        for i, tr in enumerate(T):
            end_t, end_d = tr["pts"][-1]
            if end_d > last - 500:
                continue
            if sched_ends and (tr["trip"] in sched_ends or strip_agency(tr["trip"]) in sched_ends):
                planned = sched_ends.get(tr["trip"], sched_ends.get(strip_agency(tr["trip"])))
                if planned <= end_d + 500:
                    continue                     # scheduled to end here: not an intervention
            for nxt in trips:
                if (nxt["vehicle"] == tr["vehicle"] and nxt["dir"] != direction
                        and 0 <= nxt["pts"][0][0] - end_t <= 1200
                        and nxt["pts"][0][1] > other_bounds[0] + 300
                        and abs(end_d / L - (1 - nxt["pts"][0][1] / Lo)) < 0.12):
                    short_turned.add(i)
                    k = min(range(n), key=lambda kk: abs(bounds[kk] - end_d))
                    actions.append((end_t, i, "short-turn", f"{label(i).lower()} turned back near {names[k]}"))
                    markers.append({"type": "short", "t": end_t, "dist": end_d, "trip": tr["trip"],
                                    "text": f"{label(i)} turned back near {names[k]} instead of continuing to the "
                                            f"end of the line, and started the other direction "
                                            f"{mins_txt(nxt['pts'][0][0] - end_t)} later."})
                    break

    # Added buses: live trips that aren't in the schedule.
    extra = 0
    if full and extra_ok and sched_ids is not None:
        for i, tr in enumerate(T):
            if tr["trip"] not in sched_ids and strip_agency(tr["trip"]) not in sched_ids:
                # The same bus just ended a trip short in the other direction: this is the
                # second half of a short-turn, already counted there, not an added bus.
                if other_bounds and any(
                        o["vehicle"] == tr["vehicle"] and o["dir"] != direction
                        and 0 <= tr["pts"][0][0] - o["pts"][-1][0] <= 1200
                        and o["pts"][-1][1] < other_bounds[-1] - 500 for o in trips):
                    continue
                extra += 1
                actions.append((tr["pts"][0][0], i, "extra", f"unscheduled {label(i).lower()} added"))
                markers.append({"type": "extra", "t": tr["pts"][0][0], "dist": tr["pts"][0][1], "trip": tr["trip"],
                                "text": f"{label(i)} is running a trip that isn’t in the schedule, "
                                        f"possibly added to fill a gap."})

    # Bunching events: follow each bus stop by stop behind the bus directly ahead.
    lead_at = []
    for k in range(n):
        m = {}
        for (ta, a), (tb, b) in zip(per_stop[k], per_stop[k][1:]):
            if 0 < tb - ta < 3 * 3600:
                m[b] = (a, tb - ta)
        lead_at.append(m)
    events = []
    for i in range(len(T)):
        ev = None
        ks = [k for k in range(n) if cs[i][k] is not None]
        for k in ks:
            g = usual(k, cs[i][k])
            if not g:
                continue
            la = lead_at[k].get(i)
            if ev is None:
                if la and k >= 2 and la[1] < BUNCHED * g:
                    ev = {"f": i, "l": la[0], "k0": k, "t0": cs[i][k]}
                continue
            outcome = None
            if la is None or la[0] != ev["l"]:
                lead_t = cs[ev["l"]][k]
                if lead_t is not None and lead_t > cs[i][k]:
                    outcome = "passed"
                elif lead_t is None:
                    outcome = "short-turn" if ev["l"] in short_turned else "unknown"
                else:
                    outcome = "spaced by another bus"
            elif la[1] >= RECOVERED * g:
                outcome = "recovered"
            if outcome:
                ev.update(k1=k, t1=cs[i][k], outcome=outcome)
                events.append(ev)
                ev = None
        if ev:
            k = ks[-1]
            ev.update(k1=k, t1=cs[i][k], outcome="persisted" if k >= n - 3 else
                      "short-turn" if i in short_turned else "unknown")
            events.append(ev)

    # Link each bunching event to the interventions involving either bus while it lasted
    # (passes aren't counted as fix attempts: they're an outcome, and often unplanned).
    # Response time runs from bunching to the first of them.
    for ev in events:
        tried = sorted((t, kind, desc) for t, j, kind, desc in actions
                       if kind != "pass" and j in (ev["f"], ev["l"]) and ev["t0"] - 60 <= t <= ev["t1"])
        ev["tried"] = tried
        ev["response"] = max(0, tried[0][0] - ev["t0"]) if tried else None

    out = {
        "events": [{"trip": T[e["f"]]["trip"], "vehicle": T[e["f"]]["vehicle"], "t0": e["t0"], "t1": e["t1"],
                    "k0": e["k0"], "k1": e["k1"], "outcome": e["outcome"],
                    "tried": [kind for _, kind, _ in e["tried"]],
                    "response": e["response"],
                    "recover": bounds[e["k1"]] - bounds[e["k0"]],
                    "text": f"{label(e['f'])} bunched behind {label(e['l']).lower()} from {names[e['k0']]}. "
                            + (("Intervention seen: " if len(e["tried"]) == 1 else "Interventions seen: ")
                               + "; ".join(d for _, _, d in e["tried"]) + ". " if e["tried"]
                               else "No intervention seen. ")
                            + "Result: "
                            + {"recovered": f"spaced out again by {names[e['k1']]}.",
                               "passed": f"the buses swapped order near {names[e['k1']]} but stayed close.",
                               "short-turn": f"split up near {names[e['k1']]} when one bus was turned back.",
                               "spaced by another bus": f"another bus came between them near {names[e['k1']]}.",
                               "persisted": "still bunched at the end of the line.",
                               "unknown": f"tracking ended near {names[e['k1']]}."}[e["outcome"]]}
                   for e in events],
        "markers": markers,
    }
    return out


FIXED = ("recovered", "short-turn", "spaced by another bus")


def mgmt_stats(events, markers):
    """Summary of the bunching events and intervention markers given (already
    trimmed to the chart window, so the numbers match what's drawn)."""
    judged = [e for e in events if e["outcome"] != "unknown"]
    resolved = [e for e in judged if e["outcome"] in FIXED]
    responses = [e["response"] for e in events if e["response"] is not None]
    count = lambda kind: sum(m["type"] == kind for m in markers)
    return {
        "events": len(events), "judged": len(judged), "resolved": len(resolved),
        "persisted": sum(e["outcome"] == "persisted" for e in events),
        "passed": sum(e["outcome"] == "passed" for e in events),
        "recover_dist": statistics.median([e["recover"] for e in resolved]) if resolved else None,
        "response": statistics.median(responses) if responses else None,
        "tried": sum(bool(e["tried"]) for e in events),
        "tried_judged": sum(bool(e["tried"]) for e in judged),
        "tried_fixed": sum(bool(e["tried"]) for e in resolved),
        "untried_judged": sum(not e["tried"] for e in judged),
        "untried_fixed": sum(not e["tried"] for e in resolved),
        "tried_kinds": {kind: sum(kind in e["tried"] for e in events)
                        for kind in ("hold", "express", "sign", "short-turn", "extra")},
        "holds": count("hold"), "express": count("express"), "passes": count("pass"),
        "short_turns": count("short"), "extra": count("extra"), "signs": count("sign"),
    }


def departures(trips, direction, bounds, sched, start, end):
    """Spacing and punctuality where buses pass the third stop, in the window."""
    if len(bounds) < 5:
        return None
    D = bounds[2]
    actual = sorted(t for t in (crossing_time(tr["pts"], D) for tr in trips if tr["dir"] == direction)
                    if t is not None and start <= t <= end)
    planned = {}
    for st in sched or []:
        if st["dir"] == direction:
            t = crossing_time(st["pts"], D)
            if t is not None:
                planned[st["trip"]] = t
    sched_times = sorted(t for t in planned.values() if start <= t <= end)
    spread = lambda ts: (statistics.pstdev([b - a for a, b in zip(ts, ts[1:])])
                         if len(ts) >= 4 else None)
    on_time, n = 0, 0
    for tr in trips:
        if tr["dir"] != direction:
            continue
        t = crossing_time(tr["pts"], D)
        s_t = planned.get(tr["trip"], planned.get(strip_agency(tr["trip"])))
        if t is not None and s_t is not None and start <= t <= end:
            n += 1
            on_time += -60 <= t - s_t <= 300
    return {"stop": D, "spread": spread(actual), "spread_sched": spread(sched_times),
            "on_time": on_time / n if n else None, "n": n}


def management_for(db, route, start, end, sched, sched_note, checks=None):
    """Interventions and bunching events for the chart window (with 2 hours of
    lead-in for context), by direction."""
    rows = raw_positions(db, route, start - 7200, end)
    # Same view as the chart: idling at terminals trimmed, buses that haven't pulled out left
    # off, so nothing gets a marker without a line to sit on.
    trips = trim_terminal_idle(db, route, clean(rows))
    status, signs, last_dest = {}, {}, {}
    for r in rows:
        key = (r[2], r[3].split("_", 1)[-1])
        if r[9]:
            status.setdefault(key, {})[r[4]] = r[9]
        if key in last_dest and r[7] and r[7] != last_dest[key]:
            signs.setdefault(key, []).append((r[4], r[7]))
        if r[7]:
            last_dest[key] = r[7]
    sched_ids = sched_ends = sched_pts = None
    extra_ok = False
    if sched is not None:
        sched_ids = {s["trip"] for s in sched}
        sched_ends = {s["trip"]: s["pts"][-1][1] for s in sched}
        sched_pts = {s["trip"]: s["pts"] for s in sched}
        extra_ok = not sched_note and len(sched) > 0
    out = {}
    for direction in (0, 1):
        stops = stop_list(db, route, direction)
        other = stop_list(db, route, 1 - direction)
        bounds = [s["dist"] for s in stops]
        res = management(trips, direction, bounds, [s["name"] for s in stops],
                         [s["dist"] for s in other] or None, sched_ids, sched_ends, extra_ok, status, signs,
                         checks=checks, sched_pts=sched_pts)
        if res:
            res["markers"] = [m for m in res["markers"] if start <= m["t"] <= end]
            res["events"] = [e for e in res["events"] if e["t1"] >= start and e["t0"] <= end]
            res["stats"] = mgmt_stats(res["events"], res["markers"])
            res["departures"] = departures(trips, direction, bounds, sched, start, end)
        out[str(direction)] = res
    return out


_dropped_cache = {}


def effectively_missed_trips(trips, sched, direction, bounds, start, end, want_covered=None):
    """Scheduled trips in one direction that ran, but whose slot riders saw as a long empty
    wait: at each stop, a gap between buses of 1.75-2.75 times the scheduled interval means
    riders effectively lost one bus (2.75-3.75 times: two, ...), charged to the scheduled
    trip(s) whose slot sits deepest in the gap. Counted when charged at 5+ stops in a row.
    Same rule as the dotted lines on the chart. None without enough stops or schedule, or
    when buses are scheduled every 4 minutes or less."""
    n = len(bounds)
    if n < 6:
        return None
    live = [t for t in trips if t["dir"] == direction]
    sch = [t for t in sched if t["dir"] == direction]
    keep = lambda v: v if v is not None and start <= v <= end else None
    # A bus that goes quiet (no position reports) and reappears further along within 15
    # minutes did pass the stops in between: don't let reporting dropouts look like gaps.
    lc = [[keep(v) for v in crossings(t["pts"], bounds, max_gap=MAX_GAP_SECONDS)] for t in live]
    sc = [[keep(v) for v in crossings(t["pts"], bounds)] for t in sch]
    # Each scheduled trip's own bus, if one ran it, by trip ID.
    own = {}
    for j, t in enumerate(live):
        own.setdefault(t["trip"], j)
        own.setdefault(strip_agency(t["trip"]), j)
    hw_at, all_gaps = [], []
    for k in range(n):
        ts = sorted(c[k] for c in sc if c[k] is not None)
        gaps = [b - a for a, b in zip(ts, ts[1:]) if 0 < b - a < 3 * 3600]
        all_gaps += gaps
        hw_at.append(statistics.median(gaps) if len(gaps) >= 2 else None)
    if not all_gaps or statistics.median(all_gaps) < 240:
        return None
    hw_all = statistics.median(all_gaps)
    # Follow each long gap as one event: the same two buses on either side of it, stop by
    # stop. Buses drift later along the route, so the scheduled slot sitting deepest in a
    # gap can change partway along; charging per stop would then count one lost bus two or
    # three times. Each event counts once (or once per bus lost, for very long gaps).
    events = {}                     # (bus before, bus after) -> [(k, lost, gap, hw, [slots, deepest first])]
    for k in range(n):
        act = sorted((c[k], j) for j, c in enumerate(lc) if c[k] is not None)
        due = [(c[k], i) for i, c in enumerate(sc) if c[k] is not None]
        s_times = sorted(t for t, _ in due)
        for (a1, ja), (a2, jb) in zip(act, act[1:]):
            gap = a2 - a1
            # The scheduled interval at this stop around the time of this wait (it changes
            # through the day: every 8 minutes midday might be every 15 in the evening).
            lo = max(0, bisect.bisect_right(s_times, a1) - 1)
            hi = bisect.bisect_left(s_times, a2)
            nearby = [y - x for x, y in zip(s_times[lo:hi + 1], s_times[lo + 1:hi + 2]) if 0 < y - x < 3 * 3600]
            hw = statistics.median(nearby) if nearby else (hw_at[k] or hw_all)
            lost = int(gap / hw + 0.25) - 1
            if lost < 1 or gap > 3 * 3600:
                continue
            # A trip whose own bus passed here within half an interval of its time served its
            # slot here, whatever the gaps around it: never charge it.
            def served(i):
                j = own.get(sch[i]["trip"])
                return j is not None and lc[j][k] is not None and abs(lc[j][k] - sc[i][k]) <= 0.5 * hw
            inside = sorted((d for d in due if a1 < d[0] < a2 and not served(d[1])),
                            key=lambda d: -min(d[0] - a1, a2 - d[0]))
            events.setdefault((ja, jb), []).append((k, lost, gap, hw, [i for _, i in inside]))
    charged = {}                    # trip index -> details of the event it was charged for
    for runs in events.values():
        # split into stretches of consecutive stops
        stretch = []
        for item in runs + [None]:
            if item is not None and (not stretch or item[0] == stretch[-1][0] + 1):
                stretch.append(item)
                continue
            if len(stretch) >= 5:
                lost_n = max(1, round(statistics.median(x[1] for x in stretch)))
                tally = {}
                for x in stretch:
                    for rank, i in enumerate(x[4][:x[1]]):
                        tally[i] = tally.get(i, 0) + 1
                # A trip no bus ran at all is clearly the missing one when it's in the gap;
                # otherwise, the slot that sat deepest in the gap most often along the stretch.
                for i in sorted(tally, key=lambda i: (sch[i].get("ran") is not False, -tally[i]))[:lost_n]:
                    if i not in charged:
                        charged[i] = {"k0": stretch[0][0], "k1": stretch[-1][0], "count": len(stretch),
                                      "gap": max(x[2] for x in stretch),
                                      "hw": statistics.median(x[3] for x in stretch)}
            stretch = [item] if item is not None else []
    missed = []
    for i, st in enumerate(sch):
        if i in charged:
            # Rider-based: counted whether no bus ran it at all or one ran far off schedule.
            missed.append(dict(charged[i], st=st, dropped=st.get("ran") is False))
        elif st.get("ran") is False and want_covered is not None:
            # No bus ran this trip ID, yet riders didn't lose its slot: another bus came
            # through within half a scheduled interval of when it was due. Note which.
            ks = [k for k in range(n) if sc[i][k] is not None]
            if ks:
                k = ks[len(ks) // 2]
                hw, due = hw_at[k] or hw_all, sc[i][k]
                near = [(abs(c[k] - due), j) for j, c in enumerate(lc) if c[k] is not None]
                if near and min(near)[0] <= 0.5 * hw:
                    j = min(near)[1]
                    want_covered.append({"st": st, "k": k, "live": live[j], "off": lc[j][k] - due})
    return missed


def effectively_dropped(trips, sched, direction, bounds, start, end):
    """How many trips were effectively missed (see effectively_missed_trips)."""
    found = effectively_missed_trips(trips, sched, direction, bounds, start, end)
    return None if found is None else len(found)


def effectively_missed_window(db, route, start, end):
    """Effectively missed trips to draw on a chart window, by direction: every slot riders
    experienced as missing, whether the trip had no bus or ran far off schedule (each
    missing bus counted once). Also, for dropped trips whose slot another bus covered,
    which bus and what it was running. Worked out with 3 hours of lead-in, so gaps that
    began before the window count; then everything that appears in the window is included."""
    lead = start - 3 * 3600
    sched, _ = schedule_for(db, route, lead, end)
    if not sched:
        return None
    live = clean(raw_positions(db, route, lead, end))
    by_id = {}
    for st in sched:
        by_id[st["trip"]] = st
    on_chart = lambda st: st["start"] <= end and st["end"] >= start
    out = {}
    for direction in (0, 1):
        stops = stop_list(db, route, direction)
        bounds = [s["dist"] for s in stops]
        covered = []
        found = effectively_missed_trips(live, sched, direction, bounds, lead, end, want_covered=covered)
        if found is None:
            out[str(direction)] = None
            continue
        cov = []
        for c in covered:
            if not on_chart(c["st"]):
                continue
            lv = c["live"]
            own = by_id.get(lv["trip"]) or by_id.get(strip_agency(lv["trip"]))
            own_due = crossing_time(own["pts"], bounds[c["k"]]) if own else None
            t = crossing_time(lv["pts"], bounds[c["k"]])
            cov.append({"trip": c["st"]["trip"], "bus": lv["vehicle"], "stop": stops[c["k"]]["name"],
                        "off": round(c["off"]),
                        "own_start": own["start"] if own else None,
                        "own_late": round(t - own_due) if own and own_due is not None and t is not None else None})
        out[str(direction)] = {
            "missed": [{"trip": m["st"]["trip"], "from": stops[m["k0"]]["name"], "to": stops[m["k1"]]["name"],
                        "gap": m["gap"], "hw": m["hw"], "dropped": m["dropped"]}
                       for m in found if on_chart(m["st"])],
            "covered": cov,
        }
    return out


def dropped_24h(db, route):
    """Scheduled trips in the past 24 hours (finished at least 10 minutes ago)
    by direction: how many ran, how many had no bus, how many couldn't be judged."""
    cached = _dropped_cache.get(route)
    if cached and time.time() - cached[0] < 600:
        return cached[1]
    now = int(time.time())
    trips, note = schedule_for(db, route, now - 86400, now)
    if trips is None:
        return None
    out = {"note": note}
    live = clean(raw_positions(db, route, now - 86400 - 7200, now))
    for direction in (0, 1):
        counts = {"ran": 0, "dropped": 0, "unknown": 0}
        bounds = [st["dist"] for st in stop_list(db, route, direction)]
        counts["effective"] = effectively_dropped(live, trips, direction, bounds, now - 86400, now)
        for t in trips:
            if t["dir"] != direction or t["start"] < now - 86400 or t["end"] > now - 600:
                continue
            counts["ran" if t["ran"] else "dropped" if t["ran"] is False else "unknown"] += 1
        out[str(direction)] = counts
    _dropped_cache[route] = (time.time(), out)
    return out


def trim_terminal_idle(db, route, trips):
    """For drawing only: cut the flat stretch where a bus sits at a terminal with its trip
    assigned, so each string starts when the bus pulls out and ends when it arrives. Any
    variant's terminal counts (a short trip starting mid-route too), within 400 m; a bus
    stuck elsewhere still shows. A bus that hasn't moved at all yet is left off."""
    maps = live_mappers(db, route)
    terms = {}
    for direction, pattern, lo_d, hi_d in db.execute(
            """SELECT direction, pattern, MIN(dist), MAX(dist) FROM stops WHERE route=?
               GROUP BY direction, pattern HAVING COUNT(*) >= 3""", (route,)):
        f = maps.get((direction, pattern))
        t = terms.setdefault(direction, ([], []))
        t[0].append(f(lo_d) if f else lo_d)
        t[1].append(f(hi_d) if f else hi_d)
    near = lambda d, places: any(abs(d - x) <= 400 for x in places)
    keep = []
    for tr in trips:
        p = tr["pts"]
        starts, ends = terms.get(tr["dir"], ([], []))
        if len(p) < 3 or not starts:
            keep.append(tr)
            continue
        lo, hi = 0, len(p)
        if near(p[0][1], starts):
            j = next((j for j, pt in enumerate(p) if pt[1] - p[0][1] >= 30), None)
            if j is None:
                continue                        # hasn't pulled out yet: nothing to draw
            lo = max(0, j - 1)                  # keep the last point before it pulled out
        if hi - lo >= 3 and near(p[-1][1], ends):
            j = next((j for j in range(len(p) - 1, lo - 1, -1) if p[-1][1] - p[j][1] >= 30), lo - 1)
            hi = j + 2                          # keep the first point after it arrived
        if hi - lo >= 2:
            tr["pts"] = p[lo:hi]
            if tr.get("occ"):
                tr["occ"] = tr["occ"][lo:hi]
            if tr.get("cnt"):
                tr["cnt"] = tr["cnt"][lo:hi]
        keep.append(tr)
    return keep


def attach_actual(db, route, sched, start, end):
    """For each scheduled trip that ran, note which bus ran it, when, and how early or
    late it was where it was first tracked and (if it reached the end of the line) where
    it was last tracked: even if that bus ran outside the chart's window."""
    if not sched:
        return
    live = trim_terminal_idle(db, route, clean(raw_positions(db, route, start - 3 * 3600, end + 3 * 3600)))
    by_id = {}
    for tr in live:
        for key in (tr["trip"], strip_agency(tr["trip"])):
            if key not in by_id or len(tr["pts"]) > len(by_id[key]["pts"]):
                by_id[key] = tr
    last_stop = {d: (lambda st: st[-1]["dist"] if st else None)(stop_list(db, route, d)) for d in (0, 1)}
    for st in sched:
        tr = by_id.get(st["trip"])
        if not tr or not st.get("ran"):
            continue
        p = tr["pts"]
        a, b = p[0][1] + 50, p[-1][1] - 50

        def late(dist):
            t, due = crossing_time(p, dist), crossing_time(st["pts"], dist)
            return round(t - due) if t is not None and due is not None else None
        finished = last_stop.get(tr["dir"]) is not None and p[-1][1] >= last_stop[tr["dir"]] - 400
        st.update(bus=tr["vehicle"], act0=p[0][0], act1=p[-1][0],
                  late0=late(a) if b > a else None,
                  late1=late(b) if b > a and finished else None)


def stringline(db, route, end, hours, problems=False, mgmt=False):
    start = end - int(hours * 3600)
    sched, note = schedule_for(db, route, start, end)
    attach_actual(db, route, sched, start, end)
    return {
        "route": route, "start": start, "end": end,
        "stops": {str(d): stop_list(db, route, d) for d in (0, 1)},
        "trips": trim_terminal_idle(db, route, clean(raw_positions(db, route, start, end))),
        "has_schedule": sched is not None,
        "sched": sched or [],
        "sched_note": note,
        "lanes": lanes_for(route),
        "problems": find_problems(db, route) if problems else None,
        "dropped24": dropped_24h(db, route),
        "eff": effectively_missed_window(db, route, start, end),
        "mgmt": management_for(db, route, start, end, sched, note) if mgmt else None,
    }


# ---------------------------------------------------------------- server

def make_handler(db_path, key=None):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def send(self, body, ctype, code=200, extra=None):
            data = body.encode() if isinstance(body, str) else body
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            for k, v in (extra or {}).items():
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(data)

        def do_GET(self):
            # Each request gets its own connection; sharing the collector's
            # connection across threads can stall or fail requests.
            db = sqlite3.connect(db_path, timeout=30)
            try:
                self.route_request(db)
            finally:
                db.close()

        def route_request(self, db):
            u = urllib.parse.urlparse(self.path)
            q = {k: v[0] for k, v in urllib.parse.parse_qs(u.query).items()}
            try:
                if u.path in ("/", "/stringline.htm", "/stringline.html"):
                    with open(os.path.join(HERE, "stringline.html"), "rb") as f:
                        return self.send(f.read(), "text/html; charset=utf-8")
                if u.path == "/api/routes":
                    return self.send(json.dumps(list_routes(db)), "application/json")
                if u.path == "/api/problems":
                    return self.send(json.dumps(find_problems(db, q["route"])), "application/json")
                if u.path in ("/api/stringline", "/api/csv"):
                    route = q["route"]
                    end = int(q.get("end") or time.time())
                    hours = max(0.5, min(24.0, float(q.get("hours", 3))))
                    if u.path == "/api/stringline":
                        fetch_route_stops(db, key, route)
                        return self.send(json.dumps(stringline(db, route, end, hours,
                                                               q.get("problems") == "1",
                                                               q.get("mgmt") == "1")),
                                         "application/json")
                    buf = io.StringIO()
                    w = csv.writer(buf)
                    w.writerow(["route", "direction", "trip", "vehicle", "time_utc",
                                "epoch", "dist_along_route_m", "pattern", "destination",
                                "next_stop", "bus_status", "occupancy", "passengers", "capacity"])
                    for r in raw_positions(db, route, end - int(hours * 3600), end):
                        w.writerow([r[0], r[1], r[2], r[3],
                                    utc_naive(r[4]).isoformat() + "Z",
                                    r[4], r[5], r[6], r[7], r[8], r[9] or "", r[10] or "",
                                    "" if r[11] is None else r[11], "" if r[12] is None else r[12]])
                    name = f"stringline_{route.replace('+', 'SBS')}_{end}.csv"
                    return self.send(buf.getvalue(), "text/csv",
                                     extra={"Content-Disposition": f'attachment; filename="{name}"'})
                self.send("Not found", "text/plain", 404)
            except KeyError as e:
                self.send(f"Missing parameter {e}", "text/plain", 400)
            except Exception as e:
                self.send(f"Error: {e}", "text/plain", 500)
    return Handler


def explain_holds(db, route, end_text, hours):
    now = int(time.time())
    if not end_text:
        end = now
    else:
        if "T" in end_text:
            day_txt, clock = end_text.split("T")
            day = date.fromisoformat(day_txt)
        else:
            day, clock = ny_local(now)[0], end_text
        hh, mm = (int(x) for x in clock.split(":")[:2])
        end = ny_midnight(day) + hh * 3600 + mm * 60
    start = end - int(hours * 3600)
    sched, note = schedule_for(db, route, start, end)
    checks = []
    management_for(db, route, start, end, sched, note, checks=checks)
    checks = [c for c in checks if start <= c["t"] <= end]
    fmt = lambda t: utc_naive(t - (4 if is_eastern_dst(ny_local(t)[0]) else 5) * 3600).strftime("%H:%M")
    print(f"{route}, {fmt(start)}-{fmt(end)} New York time: {len(checks)} stops of 2+ minutes mid-route")
    for c in sorted(checks, key=lambda c: (c["dir"], c["t"])):
        print(f"  dir {c['dir']}  {fmt(c['t'])}  bus {c['bus']:<6} {c['minutes']:>4} min at {c['stop']}: {c['result']}")


def main():
    global SCHEDULE_DB
    ap = argparse.ArgumentParser(description="MTA bus stringlines")
    ap.add_argument("--key", default=os.environ.get("MTA_BUSTIME_KEY"),
                    help="Bus Time API key (or set MTA_BUSTIME_KEY)")
    ap.add_argument("--db", default=os.path.join(HERE, "busstring.sqlite"))
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--routes", help="comma-separated routes to store, e.g. B63,M15+,Q44+")
    ap.add_argument("--keep-days", type=float, default=0,
                    help="delete data older than this many days (0 = keep everything)")
    ap.add_argument("--schedule", default=SCHEDULE_DB,
                    help="schedule file made by gtfs_import.py")
    ap.add_argument("--why-holds", metavar="ROUTE",
                    help="list every 2+ minute mid-route stop on ROUTE and why it was or wasn't a hold, "
                         "then exit (use with --end and --hours)")
    ap.add_argument("--end", help="window end for --why-holds, e.g. 09:05 (today, New York time) "
                                  "or 2026-11-05T09:05; default now")
    ap.add_argument("--hours", type=float, default=1, help="window length for --why-holds (default 1)")
    ap.add_argument("--serve-only", action="store_true", help="don't poll the feed")
    args = ap.parse_args()

    SCHEDULE_DB = args.schedule
    db = connect(args.db)
    if args.why_holds:
        explain_holds(db, args.why_holds, args.end, args.hours)
        return
    with db:  # fill the route list from data collected before this version
        db.execute("""INSERT OR IGNORE INTO lines
                      SELECT DISTINCT route, '' FROM positions""")
    if not args.serve_only:
        if not args.key:
            sys.exit("Set MTA_BUSTIME_KEY or pass --key "
                     "(free key: https://register.developer.obanyc.com/)")
        routes = set(args.routes.split(",")) if args.routes else None
        threading.Thread(target=collector_loop, args=(db, args.key, routes, args.keep_days),
                         daemon=True).start()

    print(f"Open http://localhost:{args.port}/  (Ctrl+C to stop)")
    ThreadingHTTPServer(("127.0.0.1", args.port), make_handler(args.db, args.key)).serve_forever()


if __name__ == "__main__":
    main()

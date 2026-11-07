#!/usr/bin/env python3
"""
Network bus service report, built on busstring.py's data and analysis.

Two steps:

  1. summarize: work out every measure for each route, direction, day and hour,
     and store them in a small summaries file. Standard library only, so it can
     also run nightly on the server to build long-term history.

       python3 bus_report.py summarize --db archive.sqlite --schedule schedule.sqlite \\
           --days 2026-11-04,2026-11-05,2026-11-06 --routes brooklyn --out summaries.sqlite

  2. html: turn the summaries into an interactive report page (no extra installs):
     summary, findings, a sortable table of every route, and each route's details. With
     --db (the raw positions), each of the worst routes gets a stringline of its worst
     two hours.

       python3 bus_report.py html --summaries summaries.sqlite --db archive.sqlite \\
           --schedule schedule.sqlite --routes brooklyn --out report.html

     (pdf makes a printable version instead; it needs matplotlib and reportlab.)

Every measure is inferred from where buses were and when; see the report's
Methods page for definitions and limits.
"""
import argparse
import json
import math
import os
import re
import sqlite3
import statistics
import sys
import time
from datetime import date, timedelta

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import busstring as b  # noqa: E402

AREAS = {
    "brooklyn": re.compile(r"^(B\d|BM\d)", re.I),        # B and BM routes (not Bx: that's the Bronx)
    "bronx": re.compile(r"^(BX\d|BXM\d)", re.I),
    "manhattan": re.compile(r"^M\d", re.I),
    "queens": re.compile(r"^(Q\d|QM\d)", re.I),
    "staten island": re.compile(r"^(S\d|SIM\d)", re.I),
    "all": re.compile(r"."),
}
PEAK_HOURS = set(range(6, 10)) | set(range(15, 19))       # wait assessment: +3 min peak, +5 off-peak

# Every per-hour count we keep. Sums add up across hours, days, directions and routes.
FIELDS = [
    "sched", "ran", "dropped", "unjudged", "covered", "eff", "eff_dropped",
    "sa1", "sa2", "ss1", "ss2", "wa_ok", "wa_n", "hw_n", "bunched_n", "long_n",
    "events", "judged", "resolved", "persisted", "passed", "tried", "tried_judged",
    "tried_fixed", "untried_judged", "untried_fixed",
    "holds", "shorts", "express", "extra", "signs",
    "rt_act", "rt_sched", "rt_n", "sp_dist", "sp_time",
    "crowd_known", "crowd_s", "gl_crowd", "gl_known", "gn_crowd", "gn_known",
    "buses", "buses_load", "lost", "slots", "seen",
]


def route_type(route):
    r = route.upper()
    if re.match(r"^(BM|BXM|QM|SIM|X)\d", r):
        return "Express"
    if r.endswith("+"):
        return "Select Bus Service"
    return "Local"


def hour_of(t):
    return b.ny_local(int(t))[1] // 60


# ---------------------------------------------------------------- summarize

def summarize_route_day(db, route, day, watched_all):
    """Per-hour counts for each direction of one route on one New York day."""
    d0 = b.ny_midnight(day)
    d1 = d0 + 86400
    lead = d0 - 3 * 3600
    in_day = lambda t: t is not None and d0 <= t < d1
    watched = {k for k in watched_all if d0 // 600 <= k < d1 // 600}
    coverage = len(watched) / 144 if watched_all else None
    ok_span = (lambda a, c: True) if not watched_all else \
        (lambda a, c: all(k in watched_all for k in range(int(a) // 600, int(c) // 600 + 1)))

    live = b.clean(b.raw_positions(db, route, lead, d1))
    if not live:
        return []
    sched_wide, note = b.schedule_for(db, route, lead, d1)
    sched_day, _ = b.schedule_for(db, route, d0, d1)
    sched_wide, sched_day = sched_wide or [], sched_day or []
    mg = b.management_for(db, route, d0, d1, sched_day, note)
    by_id = {}
    for st in sched_wide:
        by_id[st["trip"]] = st

    rows = []
    for direction in (0, 1):
        stops = b.stop_list(db, route, direction)
        bounds = [s["dist"] for s in stops]
        n = len(bounds)
        trips = [t for t in live if t["dir"] == direction]
        if n < 6 or len(trips) < 2:
            continue
        H = {h: dict.fromkeys(FIELDS, 0) for h in range(24)}
        responses = {h: [] for h in range(24)}
        add = lambda t, key, v=1: H[hour_of(t)].__setitem__(key, H[hour_of(t)][key] + v)

        # Trips: scheduled, ran, dropped (by scheduled start).
        sd = [st for st in sched_wide if st["dir"] == direction]
        for st in sd:
            if not in_day(st["start"]):
                continue
            add(st["start"], "sched")
            if st.get("ran") is True:
                add(st["start"], "ran")
            elif st.get("ran") is False:
                add(st["start"], "dropped")
            else:
                add(st["start"], "unjudged")

        # Effectively missed (rider-based), and dropped trips another bus covered.
        covered = []
        found = b.effectively_missed_trips(live, sched_wide, direction, bounds, lead, d1,
                                           want_covered=covered) or []
        for m in found:
            if in_day(m["st"]["start"]):
                add(m["st"]["start"], "eff")
                if m["dropped"]:
                    add(m["st"]["start"], "eff_dropped")
        for c in covered:
            if in_day(c["st"]["start"]):
                add(c["st"]["start"], "covered")

        # Waits: actual and scheduled gaps between buses at every stop.
        lc = [b.crossings(t["pts"], bounds, max_gap=b.MAX_GAP_SECONDS) for t in trips]
        seen_ok = b.well_seen([[v if v is not None and lead <= v < d1 else None for v in c] for c in lc], n)
        sc = [b.crossings(st["pts"], bounds) for st in sd]
        mid = n // 2
        sched_hw_mid = []
        for k in range(n):
            s_times = sorted(c[k] for c in sc if c[k] is not None and lead <= c[k] < d1)
            s_gaps = [(a, c - a) for a, c in zip(s_times, s_times[1:]) if 0 < c - a < 3 * 3600]
            per_hour = {}
            for a, g in s_gaps:
                per_hour.setdefault(hour_of(a), []).append(g)
                if in_day(a) and seen_ok[k]:       # same stops on both sides of the comparison
                    add(a, "ss1", g)
                    add(a, "ss2", g * g)
            hw_hour = {h: statistics.median(v) for h, v in per_hour.items()}
            if k == mid:
                sched_hw_mid = [g for a, g in s_gaps if in_day(a) and 7 <= hour_of(a) < 19]
            if not seen_ok[k]:
                continue            # too few buses seen at this stop to trust its gaps
            a_times = sorted((c[k], i) for i, c in enumerate(lc) if c[k] is not None and lead <= c[k] < d1)
            for (a, ia), (c, ic) in zip(a_times, a_times[1:]):
                g = c - a
                if not in_day(a) or not 0 < g < 3 * 3600 or not ok_span(a, c):
                    continue
                add(a, "sa1", g)
                add(a, "sa2", g * g)
                hw = hw_hour.get(hour_of(a))
                if not hw:
                    continue
                add(a, "hw_n")
                add(a, "wa_n")
                add(a, "wa_ok", int(g <= hw + (180 if hour_of(a) in PEAK_HOURS else 300)))
                if hw >= 240:
                    add(a, "bunched_n", int(g < 0.3 * hw))
                add(a, "long_n", int(g > 2 * hw))
                # Crowding after a long gap vs a normal one, at the middle of the route.
                if k == mid and trips[ic].get("occ"):
                    pts, occ = trips[ic]["pts"], trips[ic]["occ"]
                    j = max([x for x in range(len(pts)) if pts[x][0] <= c] or [0])
                    lvl = next((occ[x] for x in range(j, -1, -1) if occ[x] is not None), None)
                    if lvl is not None:
                        if g > 1.5 * hw:
                            add(c, "gl_known")
                            add(c, "gl_crowd", int(lvl >= 1))
                        elif 0.5 * hw <= g <= 1.25 * hw:
                            add(c, "gn_known")
                            add(c, "gn_crowd", int(lvl >= 1))

        # Effectively missed, simply: at three well-observed stops in the middle of the route
        # (about 30%, 50% and 70% of the way along), every gap of 1.75 times the scheduled
        # interval at that time is one lost bus (2.75 times: two, ...). Averaged over the three
        # stops, against the scheduled buses due there. Checkable against the headway labels.
        good = [k for k in range(n) if seen_ok[k]]
        checks = sorted({good[int(f * (len(good) - 1))] for f in (0.3, 0.5, 0.7)}) if good else []
        for k in checks:
            s_times = sorted(c[k] for c in sc if c[k] is not None and lead <= c[k] < d1 + 3 * 3600)
            for t in s_times:
                if in_day(t) and ok_span(t, t):
                    add(t, "slots", 1 / len(checks))
            a_times = sorted(c[k] for c in lc if c[k] is not None and lead <= c[k] < d1)
            for t in a_times:
                if in_day(t) and ok_span(t, t):
                    add(t, "seen", 1 / len(checks))
            for a, c in zip(a_times, a_times[1:]):
                g = c - a
                if not in_day(a) or not 0 < g < 3 * 3600 or not ok_span(a, c):
                    continue
                lo = max(0, b.bisect.bisect_right(s_times, a) - 1)
                hi = b.bisect.bisect_left(s_times, c)
                near = [y - x for x, y in zip(s_times[lo:hi + 1], s_times[lo + 1:hi + 2]) if 0 < y - x < 3 * 3600]
                if not near:
                    continue
                hw = statistics.median(near)
                lost = int(g / hw + 0.25) - 1
                if lost > 0:
                    add(a, "lost", lost / len(checks))

        # Run time against schedule, speed, crowding, buses reporting loads.
        first, last = bounds[0], bounds[-1]
        for tr in trips:
            p = tr["pts"]
            if not in_day(p[0][0]):
                continue
            add(p[0][0], "buses")
            if tr.get("occ"):
                add(p[0][0], "buses_load")
                for i in range(len(p) - 1):
                    lvl, dt = tr["occ"][i], min(300, p[i + 1][0] - p[i][0])
                    if lvl is not None and dt > 0 and in_day(p[i][0]):
                        add(p[i][0], "crowd_known", dt)
                        if lvl >= 1:
                            add(p[i][0], "crowd_s", dt)
            a, c = max(first, p[0][1]) + 50, min(last, p[-1][1]) - 50
            if c - a < 0.4 * (last - first):
                continue
            ta, tc = b.crossing_time(p, a), b.crossing_time(p, c)
            if ta is None or tc is None or tc <= ta:
                continue
            add(ta, "sp_dist", c - a)
            add(ta, "sp_time", tc - ta)
            st = next((by_id[x] for tid in tr.get("trips", [tr["trip"]]) for x in (tid, b.strip_agency(tid))
                       if x in by_id), None)
            if st:
                sa, scc = b.crossing_time(st["pts"], a), b.crossing_time(st["pts"], c)
                if sa is not None and scc is not None and scc > sa:
                    add(ta, "rt_act", tc - ta)
                    add(ta, "rt_sched", scc - sa)
                    add(ta, "rt_n")

        # Bunching events and interventions (inferred).
        m = (mg or {}).get(str(direction))
        if m:
            fixed = ("recovered", "short-turn", "spaced by another bus")
            for e in m["events"]:
                if not in_day(e["t0"]):
                    continue
                t = e["t0"]
                add(t, "events")
                known = e["outcome"] != "unknown"
                ok = e["outcome"] in fixed
                tried = bool(e["tried"])
                add(t, "judged", int(known))
                add(t, "resolved", int(ok))
                add(t, "persisted", int(e["outcome"] == "persisted"))
                add(t, "passed", int(e["outcome"] == "passed"))
                add(t, "tried", int(tried))
                if known:
                    add(t, "tried_judged" if tried else "untried_judged")
                    if ok:
                        add(t, "tried_fixed" if tried else "untried_fixed")
                if e.get("response") is not None:
                    responses[hour_of(t)].append(round(e["response"]))
            kinds = {"hold": "holds", "short": "shorts", "express": "express", "extra": "extra", "sign": "signs"}
            for mk in m["markers"]:
                if mk["type"] in kinds and in_day(mk["t"]):
                    add(mk["t"], kinds[mk["type"]])
            dep = m.get("departures") or {}
        else:
            dep = {}

        hours = {h: dict(v, responses=responses[h]) for h, v in H.items() if any(v.values()) or responses[h]}
        rows.append({
            "route": route, "direction": direction, "day": day.isoformat(),
            "dest": next((t["dest"] for t in trips if t.get("dest")), ""),
            "first_stop": stops[0]["name"], "last_stop": stops[-1]["name"],
            "coverage": coverage, "sched_note": note,
            "hw_mid": statistics.median(sched_hw_mid) if sched_hw_mid else None,
            "dep": {k: dep.get(k) for k in ("spread", "spread_sched", "on_time", "n")},
            "hours": hours,
        })
    return rows


def summarize(args):
    b.SCHEDULE_DB = args.schedule
    db = b.connect(args.db)
    out = sqlite3.connect(args.out)
    out.execute("""CREATE TABLE IF NOT EXISTS summaries (route TEXT, direction INTEGER, day TEXT,
                   data TEXT, made TEXT, PRIMARY KEY (route, direction, day))""")
    area = AREAS[args.routes.lower()] if args.routes.lower() in AREAS else re.compile(args.routes)
    routes = [r for r in b.list_routes(db) if area.search(r)]
    days = [date.fromisoformat(d) for d in args.days.split(",")] if args.days else \
           [b.ny_local(int(time.time()))[0] - timedelta(days=1)]
    # The collector's "I was running" record isn't cleared along with old positions, so in a
    # saved archive it can claim times whose positions are long gone. Only count 10-minute
    # spans that actually have position data as covered. This goes in a private temporary
    # table that takes the place of the real one for this run only, so the database is never
    # written to or locked (the live collector keeps running undisturbed).
    db.execute("""CREATE TEMP TABLE heartbeat AS SELECT bucket FROM main.heartbeat
                  WHERE bucket IN (SELECT DISTINCT ts / 600 FROM main.positions)""")
    watched = {k for (k,) in db.execute("SELECT bucket FROM heartbeat")}
    print(f"Summarizing {len(routes)} routes for {', '.join(d.isoformat() for d in days)}.", flush=True)
    started = time.time()
    for i, route in enumerate(routes, 1):
        for day in days:
            try:
                rows = summarize_route_day(db, route, day, watched)
            except Exception as e:                       # one bad route shouldn't stop the run
                print(f"  {route} {day}: skipped ({e})", flush=True)
                continue
            for r in rows:
                out.execute("INSERT OR REPLACE INTO summaries VALUES (?,?,?,?,?)",
                            (route, r["direction"], r["day"], json.dumps(r), time.strftime("%Y-%m-%d %H:%M")))
        out.commit()
        if i % 10 == 0 or i == len(routes):
            print(f"  {i} of {len(routes)} routes done ({time.time() - started:.0f} s)", flush=True)
    print(f"Wrote {args.out}.")


# ---------------------------------------------------------------- measures

def blank():
    d = dict.fromkeys(FIELDS, 0)
    d["responses"] = []
    return d


def add_into(acc, hour):
    for k in FIELDS:
        acc[k] += hour.get(k, 0)
    acc["responses"] += hour.get("responses", [])


def collect(rows, hours=None):
    """Sum per-hour counts over rows, optionally only for some hours of the day."""
    acc = blank()
    for r in rows:
        for h, v in r["hours"].items():
            if hours is None or int(h) in hours:
                add_into(acc, v)
    return acc


def ratio(a, c):
    return a / c if c else None


def measures(acc):
    """Readable measures from summed counts. None where there isn't enough data."""
    judged = acc["ran"] + acc["dropped"]
    wait_a = acc["sa2"] / (2 * acc["sa1"]) if acc["sa1"] else None
    wait_s = acc["ss2"] / (2 * acc["ss1"]) if acc["ss1"] else None
    resp = acc["responses"]
    return {
        "scheduled": acc["sched"], "judged": judged,
        "delivered": ratio(acc["ran"], judged), "dropped": ratio(acc["dropped"], judged),
        "dropped_n": acc["dropped"], "covered_n": acc["covered"],
        "eff": ratio(acc["lost"], acc["slots"]), "eff_n": round(acc["lost"]),
        "eff_ran_n": max(0, round(acc["lost"] - (acc["dropped"] - acc["covered"]))),
        # Losing a share f of buses means waits of at least 1 + 2f times scheduled; flag
        # anything that claims more loss than the measured waits allow.
        "wait_ratio": wait_a / wait_s if wait_a and wait_s else None,
        "implied_ratio": 1 + 2 * acc["lost"] / acc["slots"] if acc["slots"] else None,
        "wait_actual": wait_a / 60 if wait_a else None, "wait_sched": wait_s / 60 if wait_s else None,
        "excess": (wait_a - wait_s) / 60 if wait_a and wait_s else None,
        "wait_assess": ratio(acc["wa_ok"], acc["wa_n"]),
        "bunched": ratio(acc["bunched_n"], acc["hw_n"]), "long_gaps": ratio(acc["long_n"], acc["hw_n"]),
        "events": acc["events"], "events_per_100": 100 * acc["events"] / acc["ran"] if acc["ran"] else None,
        "recovery": ratio(acc["resolved"], acc["judged"]),
        "tried_share": ratio(acc["tried"], acc["events"]),
        "tried_success": ratio(acc["tried_fixed"], acc["tried_judged"]),
        "untried_success": ratio(acc["untried_fixed"], acc["untried_judged"]),
        "interventions": acc["holds"] + acc["shorts"] + acc["express"] + acc["extra"],
        "holds": acc["holds"], "shorts": acc["shorts"], "express_runs": acc["express"], "extra": acc["extra"],
        "response_min": statistics.median(resp) / 60 if resp else None,
        "runtime": ratio(acc["rt_act"], acc["rt_sched"]),
        "speed_mph": acc["sp_dist"] / acc["sp_time"] * 2.23694 if acc["sp_time"] else None,
        "crowded": ratio(acc["crowd_s"], acc["crowd_known"]),
        "crowd_after_long": ratio(acc["gl_crowd"], acc["gl_known"]) if acc["gl_known"] >= 10 else None,
        "crowd_after_normal": ratio(acc["gn_crowd"], acc["gn_known"]) if acc["gn_known"] >= 10 else None,
        "load_share": ratio(acc["buses_load"], acc["buses"]),
        "match_rate": ratio(acc["ran"], judged),
        "bus_ratio": ratio(acc["seen"], acc["slots"]),
        "consistent": None if not (acc["slots"] and wait_a and wait_s) else
                      (1 + 2 * acc["lost"] / acc["slots"]) <= wait_a / wait_s + 0.15,
    }


# ---------------------------------------------------------------- report

def pct(x, digits=0):
    return "n/a" if x is None else f"{x * 100:.{digits}f}%"


def mins(x, digits=1):
    return "n/a" if x is None else f"{x:.{digits}f} min"


def load_rows(path, area):
    con = sqlite3.connect(path)
    rows = [json.loads(d) for (d,) in con.execute("SELECT data FROM summaries ORDER BY route, day, direction")]
    return [r for r in rows if area.search(r["route"])]


def pdf(args):
    try:
        import matplotlib  # noqa: F401
        import reportlab   # noqa: F401
    except ImportError:
        sys.exit("The PDF step needs matplotlib and reportlab:\n"
                 "  python3 -m venv ~/bus-report-env && ~/bus-report-env/bin/pip install matplotlib reportlab\n"
                 "then run this with ~/bus-report-env/bin/python instead of python3.")
    area_name = args.routes.lower()
    area = AREAS[area_name] if area_name in AREAS else re.compile(args.routes)
    rows = load_rows(args.summaries, area)
    if not rows:
        sys.exit("No summaries for those routes. Run the summarize step first.")
    build(args, rows, area_name)


# ---------------------------------------------------------------- PDF report

DAY_NAMES = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
PERIOD_HOURS = {p[0]: set(range(p[2] // 60, p[3] // 60)) for p in b.PERIODS}
PERIOD_LABEL = {"overnight": "overnight (midnight-6 AM)", "am": "morning rush (6-10 AM)",
                "midday": "midday (10 AM-3 PM)", "pm": "afternoon rush (3-7 PM)", "evening": "evening (7 PM-midnight)"}
PERIOD_SHORT = {"overnight": "Overnight", "am": "AM rush", "midday": "Midday", "pm": "PM rush", "evening": "Evening"}
INK, MUTED, RED, BLUE, GRID = "#1d1f22", "#6b7078", "#c62828", "#2f5bd3", "#e3e5e8"


def solid_periods(rows, M, collect, share=0.08):
    """Measures by time of day, keeping only times with at least `share` of the waiting-time data."""
    total = collect(rows)["hw_n"] or 1
    out = {}
    for p in ("overnight", "am", "midday", "pm", "evening"):
        acc = collect(rows, PERIOD_HOURS[p])
        if acc["hw_n"] >= share * total:
            m = M(acc)
            if m["excess"] is not None:
                out[p] = m
    return out


def nice_day(iso):
    d = date.fromisoformat(iso)
    return f"{DAY_NAMES[d.weekday()]} {d.strftime('%b')} {d.day}"


def clock(t):
    day, m = b.ny_local(int(t))
    h, mm = divmod(m, 60)
    return f"{h % 12 or 12}:{mm:02d} {'AM' if h < 12 else 'PM'}"


def short_names(names):
    """'DE KALB AV/IRVING AV' after another DE KALB AV stop becomes 'IRVING AV' (as on the site)."""
    out, street = [], None
    for nm in names:
        cut = nm.find("/")
        on = nm[:cut].strip() if cut > 0 else None
        out.append(nm[cut + 1:].strip() if on and on == street else nm)
        street = on
    return out


def route_rows(rows):
    by = {}
    for r in rows:
        by.setdefault(r["route"], []).append(r)
    return by


def dep_on_time(rs):
    n = sum((r["dep"].get("n") or 0) for r in rs)
    if not n:
        return None, None, None
    on = sum((r["dep"].get("on_time") or 0) * (r["dep"].get("n") or 0) for r in rs) / n
    sp = [r["dep"]["spread"] for r in rs if r["dep"].get("spread") is not None]
    ss = [r["dep"]["spread_sched"] for r in rs if r["dep"].get("spread_sched") is not None]
    return on, (statistics.mean(sp) if sp else None), (statistics.mean(ss) if ss else None)


def worst_window(rs):
    """(excess, row, start hour) of the 2 hours with the largest excess wait for this route.
    Infrequent routes have little waiting data in any two hours, so the bar for how much is
    needed drops step by step until something qualifies."""
    for need in (3600, 1200, 300):
        found = worst_window_with(rs, need)
        if found:
            return found
    return None


def worst_window_with(rs, need):
    best = None
    for r in rs:
        hrs = {int(h): v for h, v in r["hours"].items()}
        for h in range(5, 23):
            v = [hrs.get(h), hrs.get(h + 1)]
            sa1 = sum(x["sa1"] for x in v if x); sa2 = sum(x["sa2"] for x in v if x)
            ss1 = sum(x["ss1"] for x in v if x); ss2 = sum(x["ss2"] for x in v if x)
            if sa1 < need or ss1 < need:            # need enough waiting time to judge
                continue
            ex = sa2 / (2 * sa1) - ss2 / (2 * ss1)
            if best is None or ex > best[0]:
                best = (ex, r, h)
    return best


def figure_png(fig, plt):
    import io
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=200, bbox_inches="tight")
    plt.close(fig)
    buf.seek(0)
    return buf


def stringline_chart(db, plt, route, row, hour):
    """A stringline of one direction of a route for two hours, as on the site."""
    day = date.fromisoformat(row["day"])
    start = b.ny_midnight(day) + hour * 3600
    end = start + 7200
    data = b.stringline(db, route, end, 2)
    d = row["direction"]
    stops = data["stops"][str(d)]
    if len(stops) < 2:
        return None, None
    fig, ax = plt.subplots(figsize=(7.4, 3.7))
    L = stops[-1]["dist"]
    eff = (data.get("eff") or {}).get(str(d)) or {"missed": []}
    eff_ids = {m["trip"] for m in eff["missed"] if not m["dropped"]}
    for st in data["sched"]:
        if st["dir"] != d:
            continue
        xs, ys = [p[0] for p in st["pts"]], [p[1] for p in st["pts"]]
        if st.get("ran") is False:
            ax.plot(xs, ys, color=RED, lw=1.1, ls=(0, (4, 3)), zorder=2)
        elif st["trip"] in eff_ids:
            ax.plot(xs, ys, color=RED, lw=1.5, ls=(0, (1, 2.2)), zorder=2)
        else:
            ax.plot(xs, ys, color="#b8bec7", lw=0.7, zorder=1)
    for tr in data["trips"]:
        if tr["dir"] != d:
            continue
        ax.plot([p[0] for p in tr["pts"]], [p[1] for p in tr["pts"]], color=BLUE, lw=1.3, zorder=3)
    ax.set_xlim(start, end)
    ax.set_ylim(L * 1.01, -L * 0.01)
    # stop labels, thinned to fit, with the street named once per run along it
    names = short_names([s["name"] for s in stops])
    last_y, ticks, labels = -1e9, [], []
    gap = L / 30
    for s_, nm in zip(stops, names):
        ax.axhline(s_["dist"], color=GRID, lw=0.4, zorder=0)
        if s_["dist"] - last_y >= gap:
            ticks.append(s_["dist"]); labels.append(nm[:26]); last_y = s_["dist"]
    ax.set_yticks(ticks)
    ax.set_yticklabels(labels, fontsize=6.2, color=MUTED)
    xt = list(range(int(start), int(end) + 1, 900))
    ax.set_xticks(xt)
    ax.set_xticklabels([clock(t) for t in xt], fontsize=7, color=MUTED)
    for t in xt:
        ax.axvline(t, color=GRID, lw=0.5, zorder=0)
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.tick_params(length=0)
    from matplotlib.lines import Line2D
    ax.legend(handles=[Line2D([], [], color=BLUE, lw=1.3, label="Bus"),
                       Line2D([], [], color="#b8bec7", lw=0.8, label="Scheduled trip"),
                       Line2D([], [], color=RED, lw=1.1, ls=(0, (4, 3)), label="Dropped"),
                       Line2D([], [], color=RED, lw=1.5, ls=(0, (1, 2.2)), label="Effectively missed")],
              loc="upper center", bbox_to_anchor=(0.5, -0.07), ncol=4, fontsize=7, frameon=False)
    caption = (f"{route} to {row['dest'] or row['last_stop']}, {nice_day(row['day'])}, "
               f"{clock(start)} to {clock(end)}")
    return fig, caption


def findings(rows, by_route, M, collect, route_type):
    """Borough-wide observations, each only if the data supports it."""
    out = []
    allm = M(collect(rows))
    per = solid_periods(rows, M, collect)
    if len(per) >= 2:
        worst = max(per, key=lambda p: per[p]["excess"])
        best = min(per, key=lambda p: per[p]["excess"])
        w = per[worst]
        out.append(f"<b>Waits were worst in the {PERIOD_LABEL[worst]}.</b> Riders waited {mins(w['wait_actual'])} "
                   f"on average against {mins(w['wait_sched'])} scheduled, {mins(w['excess'])} extra, compared with "
                   f"{mins(per[best]['excess'])} extra in the {PERIOD_LABEL[best]}.")
    if allm["eff"] is not None and allm["judged"]:
        lost, dropped = allm["eff_n"], allm["dropped_n"]
        if lost > 1.3 * dropped:
            out.append(f"<b>Most lost service wasn't cancelled trips.</b> At mid-route stops, riders effectively lost "
                       f"about {lost:,} buses ({pct(allm['eff'], 1)} of those scheduled), against {dropped:,} trips "
                       f"dropped outright: most lost service came from bunching and lateness.")
        else:
            out.append(f"<b>Cancelled trips drove most lost service.</b> Riders effectively lost about {lost:,} buses "
                       f"({pct(allm['eff'], 1)}), close to the {dropped:,} trips dropped outright.")
        if allm.get("consistent") is False:
            out.append(f"<b>Check:</b> losing {pct(allm['eff'])} of buses implies waits at least "
                       f"{allm['implied_ratio']:.2f} times scheduled, but measured waits were {allm['wait_ratio']:.2f} "
                       f"times. Treat effectively missed with caution.")
    if allm["events"] >= 20 and allm["tried_share"] is not None:
        s = (f"<b>Bunching was rarely managed.</b>" if allm["tried_share"] < 0.25 else "<b>Bunching often drew a response.</b>")
        s += (f" There were {allm['events']:,} bunching events; {pct(allm['tried_share'])} had a visible intervention "
              f"(a hold, short-turn, express run or added bus).")
        if allm["tried_success"] is not None and allm["untried_success"] is not None:
            s += (f" With one, buses were spaced out again {pct(allm['tried_success'])} of the time; without, "
                  f"{pct(allm['untried_success'])}.")
        out.append(s)
    if allm["crowd_after_long"] is not None and allm["crowd_after_normal"] is not None:
        a, c = allm["crowd_after_long"], allm["crowd_after_normal"]
        if a > c * 1.2:
            out.append(f"<b>Long gaps meant crowded buses.</b> On buses reporting loads, {pct(a)} of buses arriving "
                       f"after a long gap were standing room only or full, against {pct(c)} after a normal gap.")
    more, fewer = [], []
    for route, rs in by_route.items():
        m = M(collect(rs))
        if m["bus_ratio"] is not None and m["judged"] >= 50:
            if m["bus_ratio"] >= 1.10:
                more.append((m["bus_ratio"], route))
            elif m["bus_ratio"] <= 0.90:
                fewer.append((m["bus_ratio"], route))
    if more or fewer:
        s = "<b>Buses run against schedule.</b>"
        if more:
            s += (" More buses than scheduled ran on " + ", ".join(f"{r} ({x * 100:.0f}%)" for x, r in sorted(more, reverse=True)[:6]) +
                  ": extra buses shorten average waits even where long gaps happen.")
        if fewer:
            s += (" Fewer than scheduled ran on " + ", ".join(f"{r} ({x * 100:.0f}%)" for x, r in sorted(fewer)[:6]) + ".")
        out.append(s)
    types = {}
    for route, rs in by_route.items():
        types.setdefault(route_type(route), []).extend(rs)
    tm = {t: M(collect(rs)) for t, rs in types.items()}
    tm = {t: m for t, m in tm.items() if m["excess"] is not None and m["judged"] >= 50}
    if "Local" in tm and "Select Bus Service" in tm:
        l, sbs = tm["Local"], tm["Select Bus Service"]
        out.append(f"<b>Select Bus Service vs local.</b> SBS riders waited {mins(sbs['excess'])} extra on average, "
                   f"local riders {mins(l['excess'])}; {pct(sbs['bunched'])} of SBS buses arrived bunched, "
                   f"against {pct(l['bunched'])} of local buses.")
    # departures from the terminal vs bunching, across routes
    pairs = []
    for route, rs in by_route.items():
        on, sp, ss = dep_on_time(rs)
        m = M(collect(rs))
        if sp is not None and m["bunched"] is not None:
            pairs.append((sp, m["bunched"]))
    if len(pairs) >= 8:
        xs, ys = zip(*pairs)
        if statistics.pstdev(xs) > 0 and statistics.pstdev(ys) > 0:
            r = statistics.correlation(xs, ys) if hasattr(statistics, "correlation") else None
            if r is not None and r >= 0.4:
                out.append(f"<b>Uneven starts, more bunching.</b> Routes whose buses left the start of the line at "
                           f"uneven intervals bunched more (correlation {r:.2f} across {len(pairs)} routes): spacing "
                           f"problems begin at the terminal.")
    days = {}
    for r in rows:
        days.setdefault(r["day"], []).append(r)
    dm = {d: M(collect(rs)) for d, rs in days.items()}
    dm = {d: m for d, m in dm.items() if m["excess"] is not None}
    if len(dm) >= 2:
        w, bst = max(dm, key=lambda d: dm[d]["excess"]), min(dm, key=lambda d: dm[d]["excess"])
        if dm[w]["excess"] - dm[bst]["excess"] >= 0.5:
            out.append(f"<b>{nice_day(w)} was the worst day,</b> with {mins(dm[w]['excess'])} of extra waiting "
                       f"against {mins(dm[bst]['excess'])} on {nice_day(bst)}.")
    slow = [rt for rt, rs in by_route.items() if (M(collect(rs))["runtime"] or 0) >= 1.10]
    timed = [rt for rt, rs in by_route.items() if M(collect(rs))["runtime"] is not None]
    if len(timed) >= 5 and slow:
        out.append(f"<b>Schedules too tight on some routes.</b> {len(slow)} of {len(timed)} routes ran at least 10% "
                   f"slower than scheduled end to end, which by itself makes buses late and bunching more likely.")
    return out


def explain(route, rs, boro, M, collect):
    """Why a route ranks among the worst: where it stands out from the borough."""
    m = M(collect(rs))
    parts = []
    checks = [
        ("eff", True, lambda v, w: f"riders effectively lost {pct(v)} of scheduled trips (borough {pct(w)})"),
        ("dropped", True, lambda v, w: f"{pct(v)} of trips were dropped (borough {pct(w)})"),
        ("long_gaps", True, lambda v, w: f"{pct(v)} of waits were more than double the scheduled gap (borough {pct(w)})"),
        ("bunched", True, lambda v, w: f"{pct(v)} of buses arrived bunched (borough {pct(w)})"),
        ("recovery", False, lambda v, w: f"only {pct(v)} of bunched buses were spaced out again (borough {pct(w)})"),
        ("runtime", True, lambda v, w: f"trips took {(v - 1) * 100:+.0f}% against schedule (borough {(w - 1) * 100:+.0f}%)"),
        ("crowded", True, lambda v, w: f"buses were standing room only or full {pct(v)} of the time (borough {pct(w)})"),
    ]
    scored = []
    for key, high_bad, text in checks:
        v, w = m.get(key), boro.get(key)
        if v is None or w is None or w <= 0 or v <= 0:
            continue
        if key == "runtime":
            badness = (v - 1) - (w - 1)
            if badness < 0.05:
                continue
            score = 1 + badness * 5
        else:
            score = v / w if high_bad else w / v
            if score < 1.3:
                continue
        scored.append((score, text(v, w)))
    scored.sort(reverse=True)
    parts = [t for _, t in scored[:3]]
    per = solid_periods(rs, M, collect)
    text = f"Riders waited {mins(m['wait_actual'])} on average against {mins(m['wait_sched'])} scheduled."
    if parts:
        text += " Compared with the rest of the borough, " + "; ".join(parts) + "."
    if per:
        wp = max(per, key=lambda p: per[p]["excess"])
        text += (f" Worst in the {PERIOD_LABEL[wp]}: {mins(per[wp]['wait_actual'])} average wait against "
                 f"{mins(per[wp]['wait_sched'])} scheduled.")
    return text


def build(args, rows, area_name):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import letter
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.lib.units import inch
    from reportlab.platypus import (Image, KeepTogether, PageBreak, Paragraph, SimpleDocTemplate, Spacer,
                                    Table, TableStyle)
    plt.rcParams.update({"font.family": "DejaVu Sans", "axes.edgecolor": GRID, "axes.labelcolor": INK,
                         "xtick.color": MUTED, "ytick.color": MUTED})
    M = measures
    by_route = route_rows(rows)
    days = sorted({r["day"] for r in rows})
    area_title = area_name.title() if area_name in AREAS else args.routes
    title = args.title or f"{area_title} bus service report"
    period_txt = (nice_day(days[0]) if len(days) == 1 else f"{nice_day(days[0])} to {nice_day(days[-1])}") + \
                 f", {date.fromisoformat(days[-1]).year}"
    boro = M(collect(rows))
    coverage = [r["coverage"] for r in rows if r.get("coverage") is not None]
    cov_by_day = {}
    for r in rows:
        if r.get("coverage") is not None:
            cov_by_day.setdefault(r["day"], r["coverage"])

    ss = getSampleStyleSheet()
    H1 = ParagraphStyle("H1", parent=ss["Heading1"], fontName="Helvetica-Bold", fontSize=17, spaceAfter=4, textColor=INK)
    H2 = ParagraphStyle("H2", parent=ss["Heading2"], fontName="Helvetica-Bold", fontSize=12.5, spaceBefore=8,
                        spaceAfter=4, textColor=INK)
    H3 = ParagraphStyle("H3", parent=ss["Heading3"], fontName="Helvetica-Bold", fontSize=10.5, spaceBefore=6,
                        spaceAfter=2, textColor=INK)
    BODY = ParagraphStyle("B", parent=ss["BodyText"], fontName="Helvetica", fontSize=9.2, leading=12.4, textColor=INK)
    SMALL = ParagraphStyle("S", parent=BODY, fontSize=7.8, leading=10, textColor=MUTED)
    BUL = ParagraphStyle("BL", parent=BODY, leftIndent=11, bulletIndent=2, spaceAfter=3)
    CELL = ParagraphStyle("C", parent=BODY, fontSize=8.4, leading=10.2)
    CELLB = ParagraphStyle("CB", parent=CELL, fontName="Helvetica-Bold")
    story = []

    def table(data, widths, header=True, zebra=True):
        t = Table(data, colWidths=widths, repeatRows=1 if header else 0)
        style = [("FONT", (0, 0), (-1, -1), "Helvetica", 8.4), ("VALIGN", (0, 0), (-1, -1), "TOP"),
                 ("TEXTCOLOR", (0, 0), (-1, -1), colors.HexColor(INK)),
                 ("LINEBELOW", (0, 0), (-1, -1), 0.4, colors.HexColor(GRID)),
                 ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3)]
        if header:
            style += [("FONT", (0, 0), (-1, 0), "Helvetica-Bold", 8.2),
                      ("TEXTCOLOR", (0, 0), (-1, 0), colors.HexColor(MUTED)),
                      ("LINEBELOW", (0, 0), (-1, 0), 0.8, colors.HexColor(MUTED))]
        t.setStyle(TableStyle(style))
        return t

    # ---- page 1: summary
    story.append(Paragraph(title, H1))
    story.append(Paragraph(f"{period_txt}. {len(by_route)} routes. Bus data covers "
                           f"{pct(statistics.mean(coverage)) if coverage else 'n/a'} of the time.", SMALL))
    story.append(Spacer(1, 8))
    head = [
        ["Service delivered", f"{pct(boro['delivered'], 1)} of {boro['judged']:,} scheduled trips ran"],
        ["Dropped trips", f"{boro['dropped_n']:,} ({pct(boro['dropped'], 1)}), "
                          f"{boro['covered_n']:,} with another bus covering the slot"],
        ["Effectively missed trips", f"{boro['eff_n']:,} ({pct(boro['eff'], 1)}): slots riders experienced as missing"],
        ["Average wait, actual vs scheduled", f"{mins(boro['wait_actual'])} vs {mins(boro['wait_sched'])} "
                                              f"({mins(boro['excess'])} extra)"],
        ["Wait assessment", f"{pct(boro['wait_assess'])} of gaps within 3 min (rush) or 5 min (other times) of schedule"],
        ["Buses arriving bunched", f"{pct(boro['bunched'], 1)}; waits over double the scheduled gap: {pct(boro['long_gaps'], 1)}"],
        ["Bunching events", f"{boro['events']:,} ({boro['events_per_100']:.1f} per 100 trips); "
                            f"{pct(boro['recovery'])} spaced out again" if boro["events_per_100"] is not None else "n/a"],
        ["Management action", f"{pct(boro['tried_share'])} of bunching events had a visible intervention; "
                              f"{boro['holds']:,} holds, {boro['shorts']:,} short-turns, {boro['express_runs']:,} express runs"],
        ["Run time vs schedule", "n/a" if boro["runtime"] is None else f"{(boro['runtime'] - 1) * 100:+.1f}%; "
                                 f"average speed {boro['speed_mph']:.1f} mph" if boro["speed_mph"] else "n/a"],
        ["Crowding", "n/a" if boro["crowded"] is None else f"standing room only or full {pct(boro['crowded'])} of the time, "
                     f"on the {pct(boro['load_share'])} of buses reporting loads"],
    ]
    story.append(table([[Paragraph(a, CELLB), Paragraph(c, CELL)] for a, c in head], [1.95 * inch, 5.35 * inch],
                       header=False))
    story.append(Paragraph("Key findings", H2))
    fs = findings(rows, by_route, M, collect, route_type)
    for f in fs[:5]:
        story.append(Paragraph(f, BUL, bulletText="•"))

    # rank routes by excess wait (minimum data needed)
    ranked = []
    for route, rs in by_route.items():
        m = M(collect(rs))
        if m["excess"] is not None and m["judged"] >= 20:
            ranked.append((m["excess"], route, m))
    ranked.sort(reverse=True)
    worst = ranked[:10]
    if worst:
        story.append(Paragraph("Worst service", H2))
        story.append(Paragraph("Ranked by excess wait: how many minutes longer riders waited on average than the "
                               "schedule implies. " + ", ".join(f"<b>{r}</b> (+{e:.1f} min)" for e, r, _ in worst[:5]) +
                               ". Details follow.", BODY))
    story.append(PageBreak())

    # ---- worst 10
    story.append(Paragraph(f"The 10 routes with the worst service", H1))
    story.append(Paragraph("Excess wait is the extra time riders waited, on average, compared with what the schedule "
                           "implies for someone arriving at a stop at a random moment. Uneven gaps raise it even when "
                           "the right number of buses run.", SMALL))
    story.append(Spacer(1, 6))
    data = [["#", "Route", "Type", "Avg wait (sched)", "Excess", "Eff. missed", "Bunched", "Spaced out again"]]
    for i, (e, route, m) in enumerate(worst, 1):
        data.append([str(i), route, route_type(route).replace("Select Bus Service", "SBS"),
                     f"{m['wait_actual']:.1f} ({m['wait_sched']:.1f})", f"+{e:.1f} min", pct(m["eff"]),
                     pct(m["bunched"]), pct(m["recovery"])])
    story.append(table(data, [0.3 * inch, 0.6 * inch, 0.6 * inch, 1.2 * inch, 0.8 * inch, 0.9 * inch, 0.8 * inch,
                              1.2 * inch]))
    story.append(Spacer(1, 6))
    for i, (e, route, m) in enumerate(worst, 1):
        story.append(KeepTogether([Paragraph(f"{i}. {route} ({route_type(route)})", H3),
                                   Paragraph(explain(route, by_route[route], boro, M, collect), BODY)]))
    story.append(PageBreak())

    # ---- the worst service, drawn
    if args.db and worst:
        b.SCHEDULE_DB = args.schedule
        db = b.connect(args.db)
        story.append(Paragraph("The worst service, as stringlines", H1))
        story.append(Paragraph("Each chart shows the two hours with the largest excess wait for one of the worst routes. "
                               "Time runs left to right and the route runs top to bottom; each blue line is a bus. Grey "
                               "lines are the schedule; red dashes are dropped trips and red dots effectively missed "
                               "ones. Lines bunched together with wide empty spaces between them are what riders "
                               "experienced as long waits followed by several buses at once.", SMALL))
        drawn = 0
        for e, route, m in worst:
            if drawn >= 4:
                break
            ww = worst_window(by_route[route])
            if not ww:
                continue
            ex, row, hour = ww
            try:
                fig, cap = stringline_chart(db, plt, route, row, hour)
            except Exception as err:             # a chart that can't be drawn shouldn't stop the report
                print(f"  chart for {route} skipped ({err})")
                continue
            if fig is None:
                continue
            img = Image(figure_png(fig, plt), width=7.0 * inch, height=3.55 * inch)
            hrs = {int(h): v for h, v in row["hours"].items()}
            v = [hrs.get(hour), hrs.get(hour + 1)]
            sa = sum(x["sa2"] for x in v if x) / (2 * sum(x["sa1"] for x in v if x)) / 60
            sch = sum(x["ss2"] for x in v if x) / (2 * sum(x["ss1"] for x in v if x)) / 60
            story.append(KeepTogether([Spacer(1, 6), Paragraph(cap, H3), img,
                                       Paragraph(f"Average wait {sa:.1f} min against {sch:.1f} scheduled in these two "
                                                 f"hours ({ex / 60:+.1f} min).", SMALL)]))
            drawn += 1
        story.append(PageBreak())

    # ---- borough-wide trends
    story.append(Paragraph(f"{area_title}-wide trends", H1))
    for f in fs:
        story.append(Paragraph(f, BUL, bulletText="•"))
    # chart 1: waits by time of day
    pm_ = solid_periods(rows, M, collect, share=0.05)
    have = [p for p in ("overnight", "am", "midday", "pm", "evening") if p in pm_]
    if have:
        fig, ax = plt.subplots(figsize=(7.3, 2.6))
        xs = range(len(have))
        ax.bar([x - 0.2 for x in xs], [pm_[p]["wait_sched"] for p in have], 0.4, color="#b8bec7", label="Scheduled")
        ax.bar([x + 0.2 for x in xs], [pm_[p]["wait_actual"] for p in have], 0.4, color=BLUE, label="Actual")
        for x, p in zip(xs, have):
            ax.text(x + 0.2, pm_[p]["wait_actual"] + 0.2, f"+{pm_[p]['excess']:.1f}", ha="center", fontsize=7.5, color=RED)
        ax.set_xticks(list(xs)); ax.set_xticklabels([PERIOD_SHORT[p] for p in have], fontsize=8)
        ax.set_ylim(0, max(pm_[p]["wait_actual"] for p in have) * 1.3)
        ax.set_ylabel("Average wait (min)", fontsize=8); ax.legend(fontsize=7.5, frameon=False, ncol=2, loc="upper left")
        ax.spines[["top", "right"]].set_visible(False); ax.tick_params(labelsize=7.5)
        ax.set_title("Average wait by time of day: actual vs scheduled (red: extra minutes)", fontsize=9, loc="left")
        story.append(Image(figure_png(fig, plt), width=7.3 * inch, height=2.6 * inch))
    # chart 2: lost service by time of day
    if have:
        fig, ax = plt.subplots(figsize=(7.3, 2.4))
        xs = range(len(have))
        dg = [pm_[p]["eff_n"] - pm_[p]["eff_ran_n"] for p in have]
        rl = [pm_[p]["eff_ran_n"] for p in have]
        cv = [pm_[p]["covered_n"] for p in have]
        ax.bar(xs, dg, color=RED, label="Dropped, leaving a gap")
        ax.bar(xs, rl, bottom=dg, color="#f2a1a1", label="Ran, but late or bunched")
        ax.bar(xs, cv, bottom=[a + c for a, c in zip(dg, rl)], color="#d9dce1", label="Dropped, slot covered (not lost)")
        ax.set_xticks(list(xs)); ax.set_xticklabels([PERIOD_SHORT[p] for p in have], fontsize=8)
        ax.set_ylabel("Trips", fontsize=8); ax.legend(fontsize=7, frameon=False, ncol=3, loc="upper left")
        ax.spines[["top", "right"]].set_visible(False); ax.tick_params(labelsize=7.5)
        ax.set_title("Service riders effectively lost, by time of day", fontsize=9, loc="left")
        story.append(Image(figure_png(fig, plt), width=7.3 * inch, height=2.4 * inch))
    # chart 3: bunching vs recovery, by route
    pts = []
    for route, rs in by_route.items():
        m = M(collect(rs))
        if m["bunched"] is not None and m["recovery"] is not None and m["events"] >= 5:
            pts.append((m["bunched"] * 100, m["recovery"] * 100, route))
    if len(pts) >= 4:
        fig, ax = plt.subplots(figsize=(7.3, 3.0))
        ax.scatter([p[0] for p in pts], [p[1] for p in pts], s=16, color=BLUE, alpha=0.75)
        worst_names = {r for _, r, _ in worst[:5]}
        for x, y, r in pts:
            if r in worst_names or x == max(p[0] for p in pts):
                ax.annotate(r, (x, y), fontsize=7, xytext=(3, 3), textcoords="offset points", color=INK)
        ax.set_xlabel("Buses arriving bunched (%)", fontsize=8); ax.set_ylabel("Bunched buses spaced out again (%)", fontsize=8)
        ax.spines[["top", "right"]].set_visible(False); ax.tick_params(labelsize=7.5)
        ax.set_title("Bunching and recovery by route: lower right is worst", fontsize=9, loc="left")
        story.append(Image(figure_png(fig, plt), width=7.3 * inch, height=3.0 * inch))
    # table: by route type and by day
    groups = {}
    for route, rs in by_route.items():
        groups.setdefault(route_type(route), []).extend(rs)
    data = [["", "Delivered", "Eff. missed", "Avg wait (sched)", "Excess", "Bunched", "Run time vs sched"]]
    def line(label, rs):
        m = M(collect(rs))
        return [label, pct(m["delivered"], 1), pct(m["eff"], 1),
                "n/a" if m["wait_actual"] is None else f"{m['wait_actual']:.1f} ({m['wait_sched']:.1f})",
                mins(m["excess"]), pct(m["bunched"], 1),
                "n/a" if m["runtime"] is None else f"{(m['runtime'] - 1) * 100:+.1f}%"]
    for t, rs in sorted(groups.items()):
        data.append(line(t, rs))
    by_day = {}
    for r in rows:
        by_day.setdefault(r["day"], []).append(r)
    for d, rs in sorted(by_day.items()):
        data.append(line(nice_day(d), rs))
    data.append(line(f"All {area_title}", rows))
    story.append(Paragraph("By type of route and by day", H2))
    story.append(table(data, [1.5 * inch, 0.8 * inch, 0.85 * inch, 1.2 * inch, 0.75 * inch, 0.75 * inch, 1.2 * inch]))
    story.append(PageBreak())

    # ---- methods and data quality
    story.append(Paragraph("How this was measured", H1))
    meth = [
        ("Data", "Bus positions from the MTA Bus Time feed, recorded every 30 seconds; schedules from the MTA's "
                 "quarterly GTFS files. Everything is inferred from where buses were and when."),
        ("Service delivered and dropped trips", "A scheduled trip counts as run if any bus reported its trip ID, "
                 "and as dropped if none did while the collector was running. A dropped trip's slot counts as covered "
                 "if another bus passed within half a scheduled interval of when it was due."),
        ("Effectively missed", "At each stop, a gap between buses of 1.75 times the scheduled interval or more means "
                 "riders lost a bus; the loss is charged to the scheduled trip whose slot sits deepest in the gap. A "
                 "trip charged at 5 or more stops in a row counts once, whether no bus ran it or one ran far off "
                 "schedule. A trip whose own bus passed within half an interval of its time is never charged."),
        ("Average wait", "For a rider arriving at a random moment, the average wait is the sum of each gap squared "
                 "divided by twice the total time, so uneven gaps raise it. It is computed at every stop for actual "
                 "and scheduled gaps; excess wait is the difference."),
        ("Wait assessment", "The share of gaps between buses no more than 3 minutes (6-10 AM and 3-7 PM) or "
                 "5 minutes (other times) longer than the scheduled gap, similar to the MTA's own measure."),
        ("Bunching", "A bus arriving less than 30% of the scheduled gap behind the bus ahead, on routes scheduled "
                 "more than every 4 minutes. A bunching event ends when the gap is back above 60% (spaced out again), "
                 "the buses swap order, or the line ends."),
        ("Interventions", "Holds, short-turns, express or drop-off-only running and unscheduled trips inferred from "
                 "bus movements, with checks against traffic and habitually slow spots. They are consistent with "
                 "management action, not confirmed records of it."),
        ("Run time, speed and crowding", "Run time compares each bus with its own scheduled trip over the stretch it "
                 "was tracked. Crowding is the share of time, on buses reporting loads, at standing room only or full."),
    ]
    for h, t in meth:
        story.append(Paragraph(f"<b>{h}.</b> {t}", BODY))
        story.append(Spacer(1, 3))
    story.append(Paragraph("Data quality", H2))
    dq = [["Day", "Bus data covers", "Scheduled trips judged", "Buses reporting loads"]]
    for d, rs in sorted(by_day.items()):
        m = M(collect(rs))
        dq.append([nice_day(d), pct(cov_by_day.get(d)), f"{m['judged']:,}", pct(m["load_share"])])
    story.append(table(dq, [1.6 * inch, 1.5 * inch, 1.8 * inch, 1.6 * inch]))
    notes = [r["route"] for r in rows if r.get("sched_note")]
    thin = sorted(set(by_route) - {r for _, r, _ in ranked})
    extra = []
    if notes:
        extra.append(f"Live trip IDs didn't match the schedule on {', '.join(sorted(set(notes)))}, so dropped and "
                     f"missed trips there couldn't be judged.")
    if thin:
        extra.append(f"Too little data to rank: {', '.join(thin)}.")
    extra.append("Wednesday's data may begin partway through the day: the collector keeps a rolling three days, and "
                 "older data had already been cleared when this was saved." if days and days[0] == "2026-11-04" else "")
    for t in extra:
        if t:
            story.append(Spacer(1, 4))
            story.append(Paragraph(t, SMALL))

    def footer(canvas, doc_):
        canvas.saveState()
        canvas.setFont("Helvetica", 7.2)
        canvas.setFillColor(colors.HexColor(MUTED))
        canvas.drawString(0.6 * inch, 0.45 * inch, f"{title}, {period_txt}. Data: MTA Bus Time and GTFS. "
                                                   "Not affiliated with the MTA.")
        canvas.drawRightString(letter[0] - 0.6 * inch, 0.45 * inch, f"Page {doc_.page}")
        canvas.restoreState()

    doc = SimpleDocTemplate(args.out, pagesize=letter, leftMargin=0.6 * inch, rightMargin=0.6 * inch,
                            topMargin=0.55 * inch, bottomMargin=0.7 * inch, title=title, author="bus stringlines")
    doc.build(story, onFirstPage=footer, onLaterPages=footer)
    print(f"Wrote {args.out}.")


# ---------------------------------------------------------------- interactive HTML report

def esc(s):
    return (str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;"))


def svg_stringline(db, route, row, hour):
    """A stringline of one direction for two hours, as an inline SVG (no extra libraries)."""
    day = date.fromisoformat(row["day"])
    start = b.ny_midnight(day) + hour * 3600
    end = start + 7200
    data = b.stringline(db, route, end, 2)
    d = row["direction"]
    stops = data["stops"][str(d)]
    if len(stops) < 2:
        return None
    W, H, left, right, top, bottom = 920, 400, 190, 12, 10, 26
    L = stops[-1]["dist"] or 1
    X = lambda t: left + (t - start) / 7200 * (W - left - right)
    Y = lambda dist: top + max(0, min(1, dist / L)) * (H - top - bottom)
    pts_attr = lambda pts: " ".join(f"{X(t):.1f},{Y(dd):.1f}" for t, dd in pts)
    out = [f'<svg viewBox="0 0 {W} {H}" width="100%" style="max-width:{W}px" font-family="sans-serif">']
    names = short_names([s["name"] for s in stops])
    last = -1e9
    for s_, nm in zip(stops, names):
        y = Y(s_["dist"])
        out.append(f'<line x1="{left}" x2="{W - right}" y1="{y:.1f}" y2="{y:.1f}" stroke="#eceef1"/>')
        if y - last >= 10:
            out.append(f'<text x="{left - 5}" y="{y + 3:.1f}" font-size="8.5" text-anchor="end" fill="#6b7078">{esc(nm[:30])}</text>')
            last = y
    for t in range(int(start), int(end) + 1, 900):
        out.append(f'<line x1="{X(t):.1f}" x2="{X(t):.1f}" y1="{top}" y2="{H - bottom}" stroke="#e3e5e8"/>'
                   f'<text x="{X(t):.1f}" y="{H - 8}" font-size="9" text-anchor="middle" fill="#6b7078">{clock(t)}</text>')
    out.append(f'<clipPath id="c{route.replace("+", "S")}{d}"><rect x="{left}" y="0" width="{W - left - right}" height="{H}"/></clipPath>'
               f'<g clip-path="url(#c{route.replace("+", "S")}{d})" fill="none">')
    eff = (data.get("eff") or {}).get(str(d)) or {"missed": []}
    eff_ids = {m["trip"] for m in eff["missed"] if not m["dropped"]}
    for st in data["sched"]:
        if st["dir"] != d:
            continue
        if st.get("ran") is False:
            style = 'stroke="#c62828" stroke-width="1.3" stroke-dasharray="5 4"'
        elif st["trip"] in eff_ids:
            style = 'stroke="#c62828" stroke-width="1.8" stroke-dasharray="1.5 3.5" stroke-linecap="round"'
        else:
            style = 'stroke="#b8bec7" stroke-width="0.8"'
        out.append(f'<polyline points="{pts_attr(st["pts"])}" {style}/>')
    for tr in data["trips"]:
        if tr["dir"] == d:
            out.append(f'<polyline points="{pts_attr(tr["pts"])}" stroke="#2f5bd3" stroke-width="1.5">'
                       f'<title>Bus {esc(tr["vehicle"])}</title></polyline>')
    out.append("</g></svg>")
    return "".join(out)


def html_report(args):
    area_name = args.routes.lower()
    area = AREAS[area_name] if area_name in AREAS else re.compile(args.routes)
    rows = load_rows(args.summaries, area)
    if not rows:
        sys.exit("No summaries for those routes. Run the summarize step first.")
    M = measures
    by_route = route_rows(rows)
    days = sorted({r["day"] for r in rows})
    area_title = area_name.title() if area_name in AREAS else args.routes
    boro = M(collect(rows))
    order = ("overnight", "am", "midday", "pm", "evening")

    routes = []
    for route, rs in sorted(by_route.items(), key=lambda kv: b.route_sort_key(kv[0])):
        m = M(collect(rs))
        on, sp, ssp = dep_on_time(rs)
        per = solid_periods(rs, M, collect, share=0.05)
        by_day = {}
        for r in rs:
            by_day.setdefault(r["day"], []).append(r)
        routes.append({
            "route": route, "type": route_type(route), "m": m, "dep_on": on,
            "dests": sorted({r["dest"] for r in rs if r.get("dest")}),
            "periods": {p: per[p] for p in order if p in per},
            "days": {d: M(collect(x)) for d, x in sorted(by_day.items())},
            "explain": explain(route, rs, boro, M, collect) if m["excess"] is not None else "",
        })
    ranked = sorted([r for r in routes if r["m"]["excess"] is not None and r["m"]["judged"] >= 20],
                    key=lambda r: -r["m"]["excess"])
    if args.db:
        b.SCHEDULE_DB = args.schedule
        db = b.connect(args.db)
        targets = ranked[:args.charts] if args.charts else routes
        print(f"Drawing stringlines for {len(targets)} routes.", flush=True)
        for r in targets:
            ww = worst_window(by_route[r["route"]])
            if not ww:
                continue
            ex, row, hour = ww
            try:
                svg = svg_stringline(db, r["route"], row, hour)
            except Exception as err:
                print(f"  chart for {r['route']} skipped ({err})")
                continue
            if svg:
                hrs = {int(h): v for h, v in row["hours"].items()}
                v = [hrs.get(hour), hrs.get(hour + 1)]
                sa = sum(x["sa2"] for x in v if x) / (2 * sum(x["sa1"] for x in v if x)) / 60
                sch = sum(x["ss2"] for x in v if x) / (2 * sum(x["ss1"] for x in v if x)) / 60
                r["chart"] = {"svg": svg, "title": f"To {row['dest'] or row['last_stop']}, {nice_day(row['day'])}, "
                                                   f"{clock(b.ny_midnight(date.fromisoformat(row['day'])) + hour * 3600)} "
                                                   f"to {clock(b.ny_midnight(date.fromisoformat(row['day'])) + (hour + 2) * 3600)}",
                              "note": f"Average wait {sa:.1f} min against {sch:.1f} scheduled ({ex / 60:+.1f} min)."}
    per_all = solid_periods(rows, M, collect, share=0.05)
    by_day_all = {}
    for r in rows:
        by_day_all.setdefault(r["day"], []).append(r)
    payload = {
        "title": args.title or f"{area_title} bus service",
        "period": (nice_day(days[0]) + (f" to {nice_day(days[-1])}" if len(days) > 1 else "")),
        "boro": boro, "findings": findings(rows, by_route, M, collect, route_type),
        "periods": {p: per_all[p] for p in order if p in per_all},
        "days": {d: M(collect(x)) for d, x in sorted(by_day_all.items())},
        "routes": routes, "worst": [r["route"] for r in ranked[:10]],
        "coverage": {d: next((r["coverage"] for r in x if r.get("coverage") is not None), None)
                     for d, x in sorted(by_day_all.items())},
        "labels": {"period": PERIOD_SHORT, "day": {d: nice_day(d) for d in days}},
    }
    html = HTML_TEMPLATE.replace("/*DATA*/", json.dumps(payload).replace("</", "<\\/"))
    with open(args.out, "w") as f:
        f.write(html)
    print(f"Wrote {args.out}. Open it in your browser.")


HTML_TEMPLATE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Bus service report</title>
<style>
  body { font: 14px/1.45 -apple-system, "Helvetica Neue", Arial, sans-serif; color: #1d1f22; margin: 0; background: #fff; }
  main { max-width: 1250px; margin: 0 auto; padding: 20px 16px 60px; }
  h1 { font-size: 22px; margin: 0 0 2px; } h2 { font-size: 17px; margin: 26px 0 8px; } h3 { margin: 18px 0 6px; font-size: 15px; }
  .muted { color: #6b7078; } .small { font-size: 12px; }
  table { border-collapse: collapse; font-size: 12.5px; }
  th, td { padding: 4px 8px; border-bottom: 1px solid #e6e8eb; text-align: right; white-space: nowrap; }
  th:first-child, td:first-child, th.l, td.l { text-align: left; }
  thead th { position: sticky; top: 0; background: #fff; cursor: pointer; color: #6b7078; font-weight: 600; user-select: none; }
  thead th.sorted { color: #1d1f22; }
  tbody tr { cursor: pointer; } tbody tr:hover { background: #f4f6f8; } tr.sel { background: #e8eefc !important; }
  .worst td:first-child { font-weight: 700; color: #c62828; }
  .summary td { text-align: left; white-space: normal; } .summary td:first-child { font-weight: 600; width: 230px; }
  .summary i { color: #6b7078; font-weight: 600; font-style: normal; text-transform: uppercase; font-size: 11px; letter-spacing: .04em; }
  .wrap { overflow-x: auto; } ul { padding-left: 20px; } li { margin: 4px 0; }
  .bars { display: flex; gap: 22px; align-items: flex-end; height: 170px; margin: 10px 0 4px; }
  .bar { display: flex; flex-direction: column; align-items: center; font-size: 11px; color: #6b7078; }
  .bar .pair { display: flex; gap: 3px; align-items: flex-end; height: 140px; }
  .bar .s { width: 22px; background: #b8bec7; } .bar .a { width: 22px; background: #2f5bd3; }
  #detail { border-top: 2px solid #1d1f22; margin-top: 24px; padding-top: 6px; }
  .bad { color: #c62828; font-weight: 600; }
</style></head><body><main>
<div id="errors" style="color:#c62828;white-space:pre-wrap;font:12px monospace"></div>
<script>
window.onerror = (msg, src, line, col) => {
  document.getElementById("errors").textContent += `Error: ${msg} (line ${line}, column ${col})\n`;
};
</script>
<h1 id="title"></h1><div id="sub" class="muted"></div>
<h2>Summary</h2><table class="summary" id="summary"></table>
<h2>Key findings</h2><ul id="findings"></ul>
<h2>By time of day</h2>
<div class="bars" id="bars"></div><div class="small muted">Grey: scheduled average wait. Blue: actual. Extra minutes above each pair.</div>
<div class="wrap"><table id="ptable"></table></div>
<h2>By day</h2><div class="wrap"><table id="dtable"></table></div>
<h2>Routes</h2>
<div class="small muted">Click a column to sort, a route for details. The 10 routes with the worst excess wait are in red.
"Check" flags routes whose effectively missed count implies longer waits than were measured.</div>
<div class="wrap"><table id="rtable"><thead></thead><tbody></tbody></table></div>
<div id="detail" hidden></div>
</main>
<script>
const D = /*DATA*/;
const section = (name, fn) => { try { fn(); } catch (e) {
  document.getElementById("errors").textContent += `Error in ${name}: ${e.message}\n${(e.stack || "").split("\n").slice(0, 3).join("\n")}\n`; } };
const $ = id => document.getElementById(id);
const pct = (x, d = 0) => x == null ? "–" : (x * 100).toFixed(d) + "%";
const min = (x, d = 1) => x == null ? "–" : x.toFixed(d);
const sgn = x => x == null ? "–" : (x >= 0 ? "+" : "") + x.toFixed(1);
const rt = x => x == null ? "–" : sgn((x - 1) * 100) + "%";
section("summary", () => {
$("title").textContent = D.title; $("sub").textContent = D.period + ". " + D.routes.length + " routes. Bus data coverage by day: " +
  Object.entries(D.coverage).map(([d, c]) => D.labels.day[d] + " " + pct(c)).join(", ") + ".";
const B = D.boro;
const sum = [
  ["<i>Solid measures</i>", ""],
  ["Service delivered", `${pct(B.delivered, 1)} of ${B.judged.toLocaleString()} scheduled trips ran`],
  ["Dropped trips", `${B.dropped_n.toLocaleString()} (${pct(B.dropped, 1)}), ${B.covered_n.toLocaleString()} with another bus covering the slot`],
  ["Average wait, actual vs scheduled", `${min(B.wait_actual)} vs ${min(B.wait_sched)} min (${sgn(B.excess)} min)`],
  ["Wait assessment", `${pct(B.wait_assess)} of gaps within 3 min (rush) / 5 min (other) of schedule`],
  ["Long gaps", `${pct(B.long_gaps, 1)} of waits over double the scheduled gap`],
  ["Buses run vs scheduled", `${pct(B.bus_ratio)} of scheduled buses passed the mid-route stops (more than 100% means extra buses ran)`],
  ["Run time vs schedule", `${rt(B.runtime)}; average speed ${min(B.speed_mph)} mph`],
  ["<i>Experimental measures</i>", ""],
  ["Effectively missed", `about ${B.eff_n.toLocaleString()} buses (${pct(B.eff, 1)} of scheduled): long gaps at three mid-route stops per route` +
    (B.consistent === false ? ` <span class="bad">Check failed: implies waits at least ${B.implied_ratio.toFixed(2)}× scheduled; measured ${B.wait_ratio.toFixed(2)}×</span>` :
     B.consistent ? ` <span class="muted">(consistent with measured waits)</span>` : "")],
  ["Bunching", `${pct(B.bunched, 1)} of buses arrived bunched`],
  ["Bunching events", `${B.events.toLocaleString()} (${min(B.events_per_100)} per 100 trips); ${pct(B.recovery)} spaced out again`],
  ["Management action", `${pct(B.tried_share)} of events had a visible intervention (with: ${pct(B.tried_success)} spaced out again; without: ${pct(B.untried_success)}). ${B.holds} holds, ${B.shorts} short-turns, ${B.express_runs} express runs, ${B.extra} added trips; median response ${min(B.response_min)} min`],
  ["Crowding", `standing room only or full ${pct(B.crowded)} of the time on the ${pct(B.load_share)} of buses reporting loads`],
];
$("summary").innerHTML = sum.map(([a, b]) => `<tr><td>${a}</td><td>${b}</td></tr>`).join("");
$("findings").innerHTML = D.findings.map(f => `<li>${f}</li>`).join("") || "<li>Not enough data for findings.</li>";
});

const COLS = [
  ["Route", r => r.route, "l"], ["Type", r => r.type, "l"],
  ["Delivered", r => r.m.delivered, "p1"], ["Buses vs sched", r => r.m.bus_ratio, "p"], ["Dropped", r => r.m.dropped, "p1"], ["Eff. missed", r => r.m.eff, "p1"],
  ["Avg wait", r => r.m.wait_actual, "m"], ["Sched", r => r.m.wait_sched, "m"], ["Excess", r => r.m.excess, "s"],
  ["Wait assess.", r => r.m.wait_assess, "p"], ["Bunched", r => r.m.bunched, "p1"], ["Long gaps", r => r.m.long_gaps, "p1"],
  ["Events/100", r => r.m.events_per_100, "m"], ["Spaced out", r => r.m.recovery, "p"], ["Intervened", r => r.m.tried_share, "p"],
  ["Run time", r => r.m.runtime, "rt"], ["Speed", r => r.m.speed_mph, "m"], ["Crowded", r => r.m.crowded, "p"],
  ["Trips judged", r => r.m.judged, "n"],
  ["Check", r => r.m.consistent === false ? 0 : r.m.consistent ? 1 : null, "chk"],
];
const fmt = (v, k) => k === "l" ? v : k === "p" ? pct(v) : k === "p1" ? pct(v, 1) : k === "m" ? min(v) :
  k === "s" ? sgn(v) : k === "rt" ? rt(v) :
  k === "chk" ? (v === 0 ? '<span class="bad" title="Effectively missed implies longer waits than were measured">⚠ check</span>' : v === 1 ? "ok" : "–") :
  (v ?? "–").toLocaleString();
function rowsTable(el, head, items, cells) {
  el.innerHTML = `<thead><tr>${head.map(h => `<th class="${h[2] === "l" ? "l" : ""}">${h[0]}</th>`).join("")}</tr></thead>` +
    `<tbody>${items.map(it => `<tr>${cells(it).map((c, i) => `<td class="${head[i][2] === "l" ? "l" : ""}">${c}</td>`).join("")}</tr>`).join("")}</tbody>`;
}
const MCOLS = COLS.slice(2);
const mrow = (label, m) => [label, ...MCOLS.map(c => fmt(c[1]({ m }), c[2]))];
section("time of day and day tables", () => {
rowsTable($("ptable"), [["", null, "l"], ...MCOLS], Object.entries(D.periods), ([p, m]) => mrow(D.labels.period[p], m));
rowsTable($("dtable"), [["", null, "l"], ...MCOLS], Object.entries(D.days), ([d, m]) => mrow(D.labels.day[d], m));
});
$("ptable").querySelectorAll("tbody tr, thead th").forEach(e => e.style.cursor = "default");
$("dtable").querySelectorAll("tbody tr, thead th").forEach(e => e.style.cursor = "default");
// bars: average wait by time of day
section("time of day chart", () => {
const per = Object.entries(D.periods), topWait = Math.max(...per.map(([, m]) => m.wait_actual || 0), 1);
$("bars").innerHTML = per.map(([p, m]) => `<div class="bar"><div class="small bad">${sgn(m.excess)}</div><div class="pair">
  <div class="s" style="height:${(m.wait_sched || 0) / topWait * 135}px" title="Scheduled ${min(m.wait_sched)} min"></div>
  <div class="a" style="height:${(m.wait_actual || 0) / topWait * 135}px" title="Actual ${min(m.wait_actual)} min"></div></div>
  <div>${D.labels.period[p]}</div></div>`).join("");
});

// routes table, sortable
let sortCol = 7, sortDir = -1;
const worst = new Set(D.worst);
// B1, B2, B3 ... B100, with B44+ (SBS) right after B44, and BM routes after the B routes.
function routeCmp(a, b) {
  const key = r => { const m = r.match(/^([A-Za-z]+)(\d+)(.*)$/); return m ? [m[1].toUpperCase(), +m[2], m[3]] : [r, 0, ""]; };
  const [p, n, s] = key(a), [q, o, t] = key(b);
  return p < q ? -1 : p > q ? 1 : n !== o ? n - o : s < t ? -1 : s > t ? 1 : 0;
}
function drawRoutes() {
  const head = $("rtable").tHead, body = $("rtable").tBodies[0];
  head.innerHTML = `<tr>${COLS.map((c, i) => `<th class="${c[2] === "l" ? "l" : ""} ${i === sortCol ? "sorted" : ""}" data-i="${i}">${c[0]}${i === sortCol ? (sortDir < 0 ? " ▼" : " ▲") : ""}</th>`).join("")}</tr>`;
  const items = D.routes.slice().sort((a, b) => {
    if (sortCol === 0) return routeCmp(a.route, b.route) * sortDir;
    const x = COLS[sortCol][1](a), y = COLS[sortCol][1](b);
    if (x == null) return 1; if (y == null) return -1;
    return (x < y ? -1 : x > y ? 1 : 0) * sortDir;
  });
  body.innerHTML = items.map(r => `<tr data-r="${r.route}" class="${worst.has(r.route) ? "worst" : ""}">${COLS.map(c =>
    `<td class="${c[2] === "l" ? "l" : ""}">${fmt(c[1](r), c[2])}</td>`).join("")}</tr>`).join("");
  head.querySelectorAll("th").forEach(th => th.onclick = () => {
    const i = +th.dataset.i; sortDir = i === sortCol ? -sortDir : (COLS[i][2] === "l" ? 1 : -1); sortCol = i; drawRoutes(); });
  body.querySelectorAll("tr").forEach(tr => tr.onclick = () => showRoute(tr.dataset.r));
}
function showRoute(name) {
  const r = D.routes.find(x => x.route === name), el = $("detail");
  document.querySelectorAll("#rtable tbody tr").forEach(tr => tr.classList.toggle("sel", tr.dataset.r === name));
  let h = `<h2>${r.route} (${r.type})</h2><div class="muted small">${r.dests.join(" / ")}</div><p>${r.explain}</p>`;
  const d = r.m;
  h += `<p class="small">Trips: ${d.judged} judged, ${d.dropped_n} dropped (${d.covered_n} covered). Effectively missed: about
       ${d.eff_n} buses (${pct(d.eff, 1)})${d.consistent === false ? ` <span class="bad">— check failed: implies waits at least
       ${d.implied_ratio.toFixed(2)}× scheduled, measured ${d.wait_ratio.toFixed(2)}×</span>` : ""}. Bunching events: ${d.events}; ${pct(d.recovery)} spaced out again; ${pct(d.tried_share)} had an
       intervention (${d.holds} holds, ${d.shorts} short-turns, ${d.express_runs} express runs, ${d.extra} added trips).
       Departures on time at the start of the route: ${pct(r.dep_on)}. Buses reporting loads: ${pct(d.load_share)}.</p>`;
  if (r.chart) h += `<h3>Worst two hours: ${r.chart.title}</h3>${r.chart.svg}<div class="small muted">${r.chart.note}
       Blue: buses. Grey: schedule. Red dashes: dropped trips. Red dots: effectively missed.</div>`;
  else h += `<p class="small muted">No stringline: not enough bus and schedule data in any two-hour stretch to compare
       actual with scheduled waits.</p>`;
  el.innerHTML = h + `<h3>By time of day</h3><div class="wrap"><table id="dp"></table></div><h3>By day</h3><div class="wrap"><table id="dd"></table></div>`;
  rowsTable($("dp"), [["", null, "l"], ...MCOLS], Object.entries(r.periods), ([p, m]) => mrow(D.labels.period[p], m));
  rowsTable($("dd"), [["", null, "l"], ...MCOLS], Object.entries(r.days), ([dd, m]) => mrow(D.labels.day[dd], m));
  el.hidden = false; el.scrollIntoView({ behavior: "smooth", block: "start" });
}
section("routes table", drawRoutes);
</script></body></html>"""


def main():
    ap = argparse.ArgumentParser(description="Network bus service report")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("summarize", help="work out measures and store them in a summaries file")
    s.add_argument("--db", default=os.path.join(HERE, "busstring.sqlite"))
    s.add_argument("--schedule", default=os.path.join(HERE, "schedule.sqlite"))
    s.add_argument("--days", help="comma-separated New York dates, e.g. 2026-11-04,2026-11-05; default yesterday")
    s.add_argument("--routes", default="all", help="brooklyn, bronx, manhattan, queens, staten island, all, "
                                                   "or a pattern such as ^B41$")
    s.add_argument("--out", default=os.path.join(HERE, "summaries.sqlite"))
    h = sub.add_parser("html", help="make an interactive report page from a summaries file (no extra installs)")
    h.add_argument("--summaries", default=os.path.join(HERE, "summaries.sqlite"))
    h.add_argument("--db", help="raw positions database, for stringlines of each route's worst two hours")
    h.add_argument("--schedule", default=os.path.join(HERE, "schedule.sqlite"))
    h.add_argument("--routes", default="all")
    h.add_argument("--charts", type=int, default=0, help="only draw stringlines for this many of the worst routes "
                                                          "(default: every route)")
    h.add_argument("--title")
    h.add_argument("--out", default="bus-service-report.html")
    p = sub.add_parser("pdf", help="make the PDF report from a summaries file")
    p.add_argument("--summaries", default=os.path.join(HERE, "summaries.sqlite"))
    p.add_argument("--db", help="raw positions database, for the stringline charts of the worst service")
    p.add_argument("--schedule", default=os.path.join(HERE, "schedule.sqlite"))
    p.add_argument("--routes", default="all")
    p.add_argument("--title", help="report title")
    p.add_argument("--out", default="bus-service-report.pdf")
    args = ap.parse_args()
    {"summarize": summarize, "pdf": pdf, "html": html_report}[args.cmd](args)


if __name__ == "__main__":
    main()

# MTA bus stringlines

Stringline charts for New York City buses, built from the MTA's real-time Bus Time feed. Live at **[buses.airlineflyer.net](https://buses.airlineflyer.net)**.

A stringline is a time-and-distance chart: time runs left to right, stops run top to bottom, and each bus trip is a line moving diagonally across the chart. Steep lines are fast buses, flat lines are buses standing still, and lines that bunch together or spread apart show bunching and gaps in service at a glance. The idea and layout follow Paul-Vincent Bienvenue's [subway stringlines](https://pvibien.com/stringline.htm).

## What it shows

- **Stringlines for every route**, either direction, over any window up to 12 hours in the last few days.
- **The schedule** behind the live buses, with dropped trips (dashed red) and *effectively missed* trips (dotted red): trips whose slot riders experienced as a long empty wait, whether no bus ran them or one ran far off schedule.
- **Interventions inferred from bus movements:** holds (H), short-turns (T), express or drop-off-only running (E), unscheduled trips (+), plus passes (P). Purple shading follows a bus while it runs bunched behind the one ahead.
- **Passenger loading** (green, yellow, red) on buses that report it.
- **Bus lanes** along the route, shaded only while each lane is in effect.
- **Route stats** for the window: buses per hour and gaps against the schedule, run times, effectively missed and dropped trips, bunching events and how they ended, crowding.
- **Problem areas:** stretches where, across all stored days, buses are consistently slow, delayed, bunched, leave long gaps, or bunch without being spaced out again.
- Headway and run time labels, a CSV export of the raw positions behind any chart, and a layout that works on phones.

Everything about holds, bunching and effectively missed trips is inferred from where buses were and when. The feed doesn't say why a bus did something, so the site says "consistent with a hold" rather than "held."

## How it works

```
MTA Bus Time feed ──every 30 s──> busstring.py ──> SQLite ──> busstring.py (web server) ──> stringline.html
                                                     ↑
MTA bus schedules (GTFS) + NYC DOT bus lanes ──> gtfs_import.py ──> schedule.sqlite
```

| File | What it does |
|---|---|
| `busstring.py` | Polls the [MTA Bus Time SIRI feed](https://bt.mta.info/developers/siri/) for the whole fleet every 30 seconds, stores each bus's distance along its route, and serves the page and its data. All the analysis lives here. |
| `stringline.html` | The page: one self-contained file, no build step or libraries. |
| `gtfs_import.py` | Condenses the MTA's bus schedule files (and, optionally, NYC DOT's bus lane data) into one compact `schedule.sqlite`. Run it on any computer and copy the result to the server. |
| `busstring.service` | A systemd service that keeps the collector running on a Linux server. |
| `Caddyfile` | A [Caddy](https://caddyserver.com) setup that serves the site over HTTPS. Change the address to your own. |

Python 3.8+ standard library only; nothing to install.

## Run it on your own computer

1. Get a free MTA Bus Time API key at <https://register.developer.obanyc.com/>.
2. Download this repository and, in its folder, run:
   ```
   export MTA_BUSTIME_KEY=your-key
   python3 busstring.py
   ```
3. Open <http://127.0.0.1:8000>. Charts fill in as data arrives; give it 30 to 60 minutes.

Useful options (`python3 busstring.py --help` lists them all):

| Option | Use |
|---|---|
| `--routes B63,M15+,Q44+` | Store only these routes (Select Bus Service routes end in `+`). |
| `--keep-days 3` | Delete data older than 3 days; the default keeps everything. |
| `--port 8001` | Serve on another port. |
| `--serve-only` | Browse stored data without polling the feed. |
| `--why-holds B54 --end 14:45 --hours 1` | List every 2+ minute mid-route stop on a route in a window, and why each was or wasn't treated as a hold. |

Collecting the whole fleet downloads several megabytes every 30 seconds and adds very roughly 2 to 3 GB of data a day, so use `--routes` and `--keep-days` on small machines.

## Add the schedule and bus lanes

The schedule enables dropped and effectively missed trips, scheduled-versus-actual stats, holds against the schedule, and complete stop lists.

1. Download the MTA's bus GTFS files from the [MTA developer page](https://new.mta.info/developers): one zip per borough plus MTA Bus Company. Unzip each into its own folder inside a folder named `gtfs`, for example `gtfs/gtfs_b`, `gtfs/gtfs_m`.
2. Optional, for bus lanes: export NYC DOT's [Bus Lanes - Local Streets](https://data.cityofnewyork.us/d/ycrg-ses3) dataset as CSV and save it as `bus_lanes.csv` next to `gtfs_import.py`.
3. Run:
   ```
   python3 gtfs_import.py gtfs
   ```
   This writes `schedule.sqlite`. Put it next to `busstring.py`; no restart needed. Repeat when the MTA publishes a new schedule, usually quarterly. The MTA replaces the files about a week before each new schedule starts, and each set only covers its own quarter.

## Run it on a server around the clock

A small Ubuntu server works; the live site runs on a 1 GB DigitalOcean droplet keeping 3 days of history. Outline:

1. Install the software and create a limited account for the collector:
   ```
   apt update && apt install -y python3 caddy
   adduser --system --group --no-create-home busstring
   mkdir -p /opt/busstring
   ```
2. Copy `busstring.py`, `stringline.html`, `busstring.service` and (if you made one) `schedule.sqlite` into `/opt/busstring`, then `chown -R busstring:busstring /opt/busstring`.
3. Put your key in `/etc/busstring.env` as a single line, `MTA_BUSTIME_KEY=your-key`, and `chmod 600` it. The page never sees it.
4. Start the collector:
   ```
   cp /opt/busstring/busstring.service /etc/systemd/system/
   systemctl daemon-reload && systemctl enable --now busstring
   ```
5. Point a domain at the server, put it in place of the address in `Caddyfile`, copy that to `/etc/caddy/Caddyfile`, and `systemctl reload caddy`. Caddy gets the HTTPS certificate on its own.
6. Open ports 80 and 443 (and keep SSH): `ufw allow OpenSSH && ufw allow 80 && ufw allow 443 && ufw enable`.

On a 1 GB server, add a 1 GB swap file. After updating `busstring.py`, run `systemctl restart busstring`; updating `stringline.html` or `schedule.sqlite` needs no restart.

## How some of the numbers are judged

- **Bunching:** a bus arriving less than 30% of the usual gap behind the bus ahead; spaced out again means back above 60%. Skipped on routes running every 4 minutes or less.
- **Effectively missed:** at each stop, a gap between buses of 1.75 times the scheduled interval or more means riders lost a bus, charged to the scheduled trip whose slot sits deepest in that gap; a trip charged at 5 or more stops in a row was effectively missed. A dropped trip whose slot another bus covered isn't counted.
- **Holds:** a mid-route stop of 2+ minutes while the route kept moving (the bus ahead moving at near its usual pace, no other bus stuck at the same spot), and at least 2 minutes and 1.75 times slower through that stretch than buses usually are. Then it has to be explained: too close behind the bus ahead, evening out the gaps ahead and behind, or running early against the schedule.
- **Route variants:** trips starting or ending partway along a route are placed on the main route's scale through the stops they share.

These thresholds are judgment calls, tuned against real charts. They live near the top of the relevant functions in `busstring.py` if you want to change them.

## Data and credits

- Real-time bus data: [MTA Bus Time](https://bustime.mta.info). Schedules: [MTA GTFS](https://new.mta.info/developers). Bus lanes: NYC DOT via NYC Open Data. Check each source's terms of use if you publish a site. The MTA's data feeds are free to use, but its logos, maps and symbols need a license from the MTA.
- Stringline concept and layout: [pvibien.com/stringline.htm](https://pvibien.com/stringline.htm).
- Not affiliated with or endorsed by the MTA or NYC DOT.

## License

[MIT](LICENSE): use it, change it, fork it, publish it. Just keep the copyright notice.

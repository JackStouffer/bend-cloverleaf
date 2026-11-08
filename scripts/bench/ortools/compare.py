"""Compares the Bend planner's plan for one state with Google OR-Tools.

    python compare.py <state folder> <seconds>

The folder holds instance.bin from scripts/synth.mjs, times.bin from
`solver times`, and plan-planner.bin from `solver national`. OR-Tools gets the
same contractors, days, hours, zips and deadlines, and the same minutes between
every pair of points that the Bend solver used, so both plans are scored on
identical numbers. Each working day of each contractor is one vehicle, starting
and ending at home.

Two differences, both in OR-Tools' favour or neutral:
  - OR-Tools stays inside each contractor's zips. The Bend planner may go out of
    zip within the cap to save a deadline, and the report counts those stops.
  - OR-Tools minimises drive time only. The Bend planner also spreads work
    across contractors, which costs it some driving.

Leaving an appraisal off the routes costs far more than any drive, more again
if it's due inside the horizon, so OR-Tools places all it can first.
"""

import array
import json
import math
import sys
import time

from ortools.constraint_solver import pywrapcp, routing_enums_pb2

URGENT_PENALTY = 10_000_000
LATER_PENALTY = 1_000_000


def words(path):
    assert sys.byteorder == "little"
    a = array.array("I")
    with open(path, "rb") as f:
        a.frombytes(f.read())
    return a


def read_instance(path):
    w = words(path)
    i = 0

    def take(n=1):
        nonlocal i
        out = w[i : i + n]
        i += n
        return list(out)

    version, state, cap, first, days, crew_count, job_count = take(7)
    assert version == 1, "unknown instance format"
    crews = []
    for _ in range(crew_count):
        cid, lat, lon, max_minutes, mask, zip_count = take(6)
        zips = set(take(zip_count))
        work = [first + k for k in range(days) if mask & (1 << k)]
        crews.append({"id": cid, "max": max_minutes, "days": work, "zips": zips})
    jobs = []
    for _ in range(job_count):
        jid, lat, lon, zip_, due, minutes = take(6)
        jobs.append({"id": jid, "zip": zip_, "due": due, "minutes": minutes})
    return {"state": state, "cap": cap, "first": first, "last": first + days, "crews": crews, "jobs": jobs}


def read_times(path, n):
    w = words(path)
    assert w[0] == n, f"times.bin has {w[0]} points, the instance {n}"
    return [w[1 + r * n : 1 + (r + 1) * n] for r in range(n)]


def read_plan(path):
    w = list(words(path))
    i = 0
    routes = []
    for _ in range(w[i]):
        crew, day, minutes, count = w[i + 1 : i + 5]
        routes.append((crew, day, list(w[i + 5 : i + 5 + count])))
        i += 4 + count
    i += 1
    backlog = w[i + 1 : i + 1 + w[i]]
    i += 1 + w[i]
    exceptions = w[i + 1 : i + 1 + w[i]]
    return routes, list(backlog), list(exceptions)


def score(inst, t, routes):
    """routes: (crew index, day, [job index]) with stops in visit order."""
    crews, jobs = inst["crews"], inst["jobs"]
    c0 = len(crews)
    drive = 0
    week = [0] * len(crews)
    outside = 0
    placed = set()
    for c, day, stops in routes:
        at = c
        worked = 0
        for j in stops:
            worked += t[at][c0 + j] + jobs[j]["minutes"]
            drive += t[at][c0 + j]
            at = c0 + j
            placed.add(j)
            if jobs[j]["zip"] not in crews[c]["zips"]:
                outside += 1
        worked += t[at][c]
        drive += t[at][c]
        week[c] += worked
    urgent_missed = sum(1 for j, job in enumerate(jobs) if j not in placed and job["due"] < inst["last"])
    mean = sum(week) / len(week)
    sd = math.sqrt(sum((x - mean) ** 2 for x in week) / len(week))
    return {
        "placed": len(placed),
        "urgent_missed": urgent_missed,
        "drive": drive,
        "outside": outside,
        "week_mean": round(mean),
        "week_sd": round(sd),
        "week_peak": max(week),
    }


def bend_routes(inst, plan):
    crew_at = {c["id"]: i for i, c in enumerate(inst["crews"])}
    job_at = {j["id"]: i for i, j in enumerate(inst["jobs"])}
    return [(crew_at[c], d, [job_at[s] for s in stops]) for c, d, stops in plan[0]]


def solve(inst, t, seconds):
    crews, jobs = inst["crews"], inst["jobs"]
    c0 = len(crews)
    vehicles = [(c, d) for c, crew in enumerate(crews) for d in crew["days"]]
    homes = [c for c, _ in vehicles]
    manager = pywrapcp.RoutingIndexManager(c0 + len(jobs), len(vehicles), homes, homes)
    routing = pywrapcp.RoutingModel(manager)

    def drive(a, b):
        return t[manager.IndexToNode(a)][manager.IndexToNode(b)]

    def busy(a, b):
        na = manager.IndexToNode(a)
        service = jobs[na - c0]["minutes"] if na >= c0 else 0
        return service + t[na][manager.IndexToNode(b)]

    routing.SetArcCostEvaluatorOfAllVehicles(routing.RegisterTransitCallback(drive))
    routing.AddDimensionWithVehicleCapacity(
        routing.RegisterTransitCallback(busy), 0, [crews[c]["max"] for c, _ in vehicles], True, "time"
    )
    for j, job in enumerate(jobs):
        index = manager.NodeToIndex(c0 + j)
        allowed = [v for v, (c, d) in enumerate(vehicles) if d <= job["due"] and job["zip"] in crews[c]["zips"]]
        if allowed:
            routing.SetAllowedVehiclesForIndex(allowed, index)
        else:
            routing.solver().Add(routing.ActiveVar(index) == 0)
        routing.AddDisjunction([index], URGENT_PENALTY if job["due"] < inst["last"] else LATER_PENALTY)

    params = pywrapcp.DefaultRoutingSearchParameters()
    params.first_solution_strategy = routing_enums_pb2.FirstSolutionStrategy.PARALLEL_CHEAPEST_INSERTION
    params.local_search_metaheuristic = routing_enums_pb2.LocalSearchMetaheuristic.GUIDED_LOCAL_SEARCH
    params.time_limit.seconds = seconds
    t0 = time.time()
    solution = routing.SolveWithParameters(params)
    took = time.time() - t0
    if solution is None:
        raise SystemExit("OR-Tools found no solution")
    routes = []
    for v, (c, d) in enumerate(vehicles):
        stops = []
        index = solution.Value(routing.NextVar(routing.Start(v)))
        while not routing.IsEnd(index):
            stops.append(manager.IndexToNode(index) - c0)
            index = solution.Value(routing.NextVar(index))
        routes.append((c, d, stops))
    return routes, took


def main(folder, seconds):
    inst = read_instance(f"{folder}/instance.bin")
    t = read_times(f"{folder}/times.bin", len(inst["crews"]) + len(inst["jobs"]))
    ours = score(inst, t, bend_routes(inst, read_plan(f"{folder}/plan-planner.bin")))
    routes, took = solve(inst, t, int(seconds))
    theirs = score(inst, t, routes)
    theirs["seconds"] = round(took, 1)
    print(json.dumps({"state": folder.rstrip("/").split("/")[-1], "crews": len(inst["crews"]), "jobs": len(inst["jobs"]), "bend": ours, "ortools": theirs}))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    main(sys.argv[1], sys.argv[2])

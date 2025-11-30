"""
Experimental code for Wagner-Whitin Algorithm for Dynamic Lot Sizing
and
Economic Order Interval heuristic.
-----------------------------------------------
Runs instances to compare:
  (1) Optimality: WW vs EOI (cost ratio curve)
  (2) Performance: runtime WW vs runtime EOI (bar plot and text log)

Generated PNG plots and .txt are saved in the current directory 
with timestamps in filenames.

@auth  ieva daukantas
@created 2025 Nov 30th
"""

from typing import List, Tuple, Optional, Dict, Any
import math
import statistics
import random
import time
from datetime import datetime

import matplotlib.pyplot as plt
from tqdm import tqdm

# ================================================================
# Wagner–Whitin (WW) dynamic lot-sizing
# ================================================================


'''
Cost interval f(i,j) for Wagner–Whitin
'''
def ww_cost_interval(
    i: int,
    j: int,
    s: List[float],
    h: List[float],
    d: List[float],
) -> float:
    assert 0 <= i < j <= len(d), "Require 0 ≤ i < j ≤ n"
    total = s[i]  # setup cost at period i
    for t in range(i, j):  # t = i, …, j-1
        duration = (t - i + 1)
        total += h[t] * duration * d[t]
    return total

'''
Wagner–Whitin dynamic programming algorithm. 
Inputs: set up cost s, holding cost h and demand d
Returns: (F_n, F, pred)
 - F_n optimal total cost up to period n
 - F optimal cost up to period j (for j = 0..n)
 - pred predecessor index i that achieves the minimum for F[j]
'''
def ww_opt_cost(
    s: List[float],
    h: List[float],
    d: List[float],
) -> Tuple[float, List[float], List[Optional[int]]]:
    n = len(d)
    assert len(s) == n and len(h) == n, "s, h, d must have same length"

    F = [0.0] * (n + 1)  # F[j] = optimal cost up to period j (0..n)
    pred: List[Optional[int]] = [None] * (n + 1)

    for j in range(1, n + 1):
        best_cost = float("inf")
        best_i: Optional[int] = None
        for i in range(0, j):
            interval_cost = ww_cost_interval(i, j, s, h, d)
            candidate = F[i] + interval_cost
            if candidate < best_cost:
                best_cost = candidate
                best_i = i
        F[j] = best_cost
        pred[j] = best_i

    return F[n], F, pred


'''
Recover optimal order periods from the predecessor array produced by ww_opt_cost.
Returns the list of order periods in increasing order.
'''
def ww_reconstruct_orders(pred: List[Optional[int]]) -> List[int]:
    orders: List[int] = []
    j = len(pred) - 1
    while j is not None and j > 0:
        i = pred[j]
        if i is None:
            break
        orders.append(i)
        j = i
    orders.reverse()
    return orders


# ================================================================
# Economic Order Interval (EOI) heuristic
# ================================================================

'''
Average demand.
'''
def eoi_avg_demand(d: List[float]) -> float:
    if not d:
        return 0.0
    return statistics.fmean(d)

'''
Continuous Economic Order Interval (EOI).
'''
def eoi_continuous(
    s: float,
    h: float,
    d: List[float],
) -> float:
    bar_d = eoi_avg_demand(d)
    if h <= 0 or bar_d <= 0:
        raise ValueError("Require h > 0 and average demand > 0 for EOI.")
    return math.sqrt(2.0 * s / (h * bar_d))

'''
Finite-horizon feasible EOI interval on [1, n].
'''
def eoi_feasible_interval(
    s: float,
    h: float,
    d: List[float],
    round_to_int: bool = True,
) -> float:
    n = len(d)
    if n == 0:
        raise ValueError("Demand list is empty.")
    T_star = eoi_continuous(s, h, d)
    T_feas = max(1.0, min(T_star, float(n)))
    if round_to_int:
        return round(T_feas)
    return T_feas


# ================================================================
# Cost evaluation helpers
# ================================================================

'''
Compute total cost.
'''
def compute_cost_from_orders(
    orders: List[int],
    s: List[float],
    h: List[float],
    d: List[float],
) -> float:
    if not orders:
        return 0.0

    n = len(d)
    total = 0.0
    orders = sorted([o for o in orders if 0 <= o < n])
    extended = orders + [n]

    for idx in range(len(orders)):
        i = extended[idx]
        j = extended[idx + 1]
        total += ww_cost_interval(i, j, s, h, d)

    return total

'''
Build a finite-horizon policy from EOI:
      - compute integer interval T
      - order at 0, T, 2T, ...
'''
def eoi_order_periods(
    s: float,
    h: float,
    d: List[float],
) -> List[int]:
    n = len(d)
    if n == 0:
        return []
    T_int = int(eoi_feasible_interval(s, h, d, round_to_int=True))
    T_int = max(1, min(T_int, n))

    orders: List[int] = []
    t = 0
    while t < n:
        orders.append(t)
        t += T_int
    return orders


# ================================================================
# Experiment helpers
# ================================================================
'''
Random instance for horizon n, constant s,h over time.
'''
def random_instance(
    n: int,
    s_range=(100.0, 1000.0),
    h_range=(1.0, 10.0),
    d_range=(10.0, 300.0),
) -> Tuple[List[float], List[float], List[float]]:
    s0 = random.uniform(*s_range)
    h0 = random.uniform(*h_range)
    d = [random.uniform(*d_range) for _ in range(n)]
    s = [s0] * n
    h = [h0] * n
    return s, h, d


'''
Run many random instances and collect:
      - WW and EOI costs
      - WW and EOI runtimes
      - cost ratios EOI/WW    
'''
def run_ww_vs_eoi_experiments(
    n: int,
    num_instances: int = 1000, #10_000,
    seed: int = 0,
) -> Dict[str, Any]:
    
    random.seed(seed)

    ww_better = 0
    equal_cost = 0
    eoi_better = 0

    ww_times: List[float] = []
    eoi_times: List[float] = []

    ww_costs: List[float] = []
    eoi_costs: List[float] = []
    cost_ratios: List[float] = []

    for k in range(num_instances):
        # Progress print every 500 iterations
        if (k + 1) % 500 == 0:
        	print(f"Progress: {k + 1} / {num_instances}")

        s, h, d = random_instance(n)
        s_scalar = s[0]
        h_scalar = h[0]

        # WW
        t0 = time.perf_counter()
        ww_total, F, pred = ww_opt_cost(s, h, d)
        t1 = time.perf_counter()
        ww_times.append(t1 - t0)

        ww_orders = ww_reconstruct_orders(pred)
        ww_cost_check = compute_cost_from_orders(ww_orders, s, h, d)
        assert abs(ww_total - ww_cost_check) < 1e-6
        ww_costs.append(ww_total)

        # EOI
        t2 = time.perf_counter()
        eoi_orders = eoi_order_periods(s_scalar, h_scalar, d)
        eoi_total = compute_cost_from_orders(eoi_orders, s, h, d)
        t3 = time.perf_counter()
        eoi_times.append(t3 - t2)
        eoi_costs.append(eoi_total)

        if ww_total > 0:
            cost_ratio = eoi_total / ww_total
        else:
            cost_ratio = float("inf")
        cost_ratios.append(cost_ratio)

        if ww_total < eoi_total - 1e-6:
            ww_better += 1
        elif eoi_total < ww_total - 1e-6:
            eoi_better += 1
        else:
            equal_cost += 1

    return {
        "ww_times": ww_times,
        "eoi_times": eoi_times,
        "ww_costs": ww_costs,
        "eoi_costs": eoi_costs,
        "cost_ratios": cost_ratios,
        "ww_better": ww_better,
        "eoi_better": eoi_better,
        "equal_cost": equal_cost,
        "num_instances": num_instances,
        "n": n,
    }


# ================================================================
# Plotting 
# ================================================================
'''
Check hypothesis if that WW is more optimal than EOI:
    - Plot sorted cost ratios (EOI / WW) as a curve.
    - Add horizontal line at 1 (WW optimum).
'''
def plot_cost_optimality(results: Dict[str, Any], filename: str) -> None:
    cost_ratios = results["cost_ratios"]
    num_instances = results["num_instances"]
    n = results["n"]

    sorted_ratios = sorted(cost_ratios)
    x = list(range(1, num_instances + 1))

    plt.figure()
    plt.plot(x, sorted_ratios, label="EOI / WW cost ratio")
    plt.axhline(1.0, linestyle="--", label="WW optimality baseline")
    plt.xlabel("Instance (sorted by cost ratio)")
    plt.ylabel("Cost ratio (EOI / WW)")
    plt.title(f"Optimality comparison (n={n}, instances={num_instances})")
    plt.legend()
    plt.tight_layout()
    plt.savefig(filename, dpi=300)
    plt.close()

'''
Runtime comparison in a bar graph, show avg and std dev.
'''
def plot_runtime_efficiency(results: Dict[str, Any], filename: str) -> None:
    ww_times = results["ww_times"]
    eoi_times = results["eoi_times"]

    avg_ww = statistics.fmean(ww_times)
    avg_eoi = statistics.fmean(eoi_times)
    std_ww = statistics.pstdev(ww_times)
    std_eoi = statistics.pstdev(eoi_times)

    labels = ["WW", "EOI"]
    means = [avg_ww, avg_eoi]
    stds = [std_ww, std_eoi]

    # Place bars tightly around zero: [-offset, +offset]
    offset = 0.035 #0.05 #0.010# 0.08
    x = [-offset, offset]

    plt.figure(figsize=(4.2, 3.2))

    bar_width = 0.025 #0.04 #0.14  # slim bars, nearly touching
    colors = ["#777777", "#BBBBBB"]   # two greys
    hatches = ["//", ".."]            # WW = stripes, EOI = dots

    bars = plt.bar(
        x,
        means,
        yerr=stds,
        width=bar_width,
        capsize=4,
        color=colors,
        edgecolor="black",
        linewidth=0.3,#0.9,
    )

    # Apply hatching
    for bar, hatch in zip(bars, hatches):
        bar.set_hatch(hatch)

    # Expand y-limit so labels fit
    max_height = max(m + s for m, s in zip(means, stds))
    plt.ylim(0, max_height * 1.45)

    # Add avg/std labels above bars
    for i, bar in enumerate(bars):
        height = bar.get_height()
        std = stds[i]
        label = f"avg={height:.6f}s\nstd={std:.6f}s"
        plt.text(
            bar.get_x() + bar.get_width() / 2,
            height + std * 1.10,
            label,
            ha="center",
            va="bottom",
            fontsize=8.5,
        )

    # X-axis ticks right under each bar
    plt.xticks(x, labels, fontsize=10)
    plt.ylabel("Runtime (seconds)", fontsize=11)
    plt.title("Runtime comparison: WW vs EOI", fontsize=12)

    # Light horizontal grid for readability (CAV-ish)
    plt.grid(axis="y", linestyle=":", linewidth=0.5, alpha=0.6)
    for spine in ["top", "right"]:
        plt.gca().spines[spine].set_visible(False)

    plt.tight_layout()
    plt.savefig(filename, dpi=300)
    plt.close()

'''
Pretty-print time with automatic units:
      - < 1e-3 s  => microseconds (µs)
      - < 1 s     => milliseconds (ms)
      - otherwise => seconds (s)
'''
def format_time_units(seconds: float) -> str:
    if seconds < 1e-3:
        return f"{seconds * 1e6:.2f}  µs"
    elif seconds < 1.0:
        return f"{seconds * 1e3:.2f}  ms"
    else:
        return f"{seconds:.2f}   s"


def benchmark_speed_for_ns(
    ns: List[int],
    num_instances_per_n: int = 100,
    seed: int = 0,
) -> Dict[str, Any]:
    random.seed(seed)
    ww_avg_times: List[float] = []
    eoi_avg_times: List[float] = []

    print("Benchmarking speed for horizons:", ns)

    for n in tqdm(ns, desc="Horizons", unit="n"):
        ww_times_n: List[float] = []
        eoi_times_n: List[float] = []

        for _ in range(num_instances_per_n):
            s, h, d = random_instance(n)
            s_scalar = s[0]
            h_scalar = h[0]

            t0 = time.perf_counter()
            ww_total, F, pred = ww_opt_cost(s, h, d)
            t1 = time.perf_counter()
            ww_times_n.append(t1 - t0)

            t2 = time.perf_counter()
            eoi_orders = eoi_order_periods(s_scalar, h_scalar, d)
            _ = compute_cost_from_orders(eoi_orders, s, h, d)
            t3 = time.perf_counter()
            eoi_times_n.append(t3 - t2)

        ww_avg_times.append(statistics.fmean(ww_times_n))
        eoi_avg_times.append(statistics.fmean(eoi_times_n))

    return {
        "ns": ns,
        "ww_avg_times": ww_avg_times,
        "eoi_avg_times": eoi_avg_times,
        "num_instances_per_n": num_instances_per_n,
    }


'''
Print WW and EOI speed tables, save them to a txt file.
'''
def print_and_save_speed_table(
    speed_results: Dict[str, Any],
    filename: str,
) -> None:
    ns = speed_results["ns"]
    ww_avg_times = speed_results["ww_avg_times"]
    eoi_avg_times = speed_results["eoi_avg_times"]
    num_instances_per_n = speed_results["num_instances_per_n"]

    lines: List[str] = []

    header = (
        f"Speed (averaged over {num_instances_per_n} random instance(s) per n)\n"
        "-------------------------------------------------------------\n"
    )
    lines.append(header)

    # WW table
    lines.append("WW\n")
    lines.append("Periods (n)      Time\n")
    for n, t in zip(ns, ww_avg_times):
        lines.append(f"{n:<14d}=>  {format_time_units(t)}\n")
    lines.append("\n")

    # EOI table
    lines.append("EOI\n")
    lines.append("Periods (n)      Time\n")
    for n, t in zip(ns, eoi_avg_times):
        lines.append(f"{n:<14d}=>  {format_time_units(t)}\n")
    lines.append("\n")

    # Print to stdout
    print("".join(lines))

    # Save to file
    with open(filename, "w", encoding="utf-8") as f:
        f.writelines(lines)

'''
Plot runtime scaling of WW and EOI depending on horizon n.
Use avg runtimes (in seconds) from benchmark_speed_for_ns.
'''
def plot_speed_scaling(speed_results: Dict[str, Any], filename: str) -> None:
    ns = speed_results["ns"]
    ww_avg_times = speed_results["ww_avg_times"]
    eoi_avg_times = speed_results["eoi_avg_times"]

    plt.figure()
    plt.plot(ns, ww_avg_times, marker="o", label="WW")
    plt.plot(ns, eoi_avg_times, marker="s", label="EOI")
    plt.xlabel("Horizon n (periods)")
    plt.ylabel("Average runtime (seconds)")
    plt.xscale("log")
    plt.yscale("log")
    plt.title("Runtime scaling: WW vs EOI")
    plt.legend()
    plt.tight_layout()
    plt.savefig(filename, dpi=300)
    plt.close()



# ================================================================
# Small example + full experiment
# ================================================================

if __name__ == "__main__":
    # Simple demo instance
    print("Single instance demo")
    print("--------------------")
    demands = [100.0, 200.0, 150.0, 250.0]
    n_small = len(demands)
    setup_costs = [500.0] * n_small
    holding_costs = [2.0] * n_small

    F_n, F, pred = ww_opt_cost(setup_costs, holding_costs, demands)
    orders = ww_reconstruct_orders(pred)

    print("WW optimal total cost F(n):", F_n)
    print("WW order periods (0-based):", orders)

    s_scalar = setup_costs[0]
    h_scalar = holding_costs[0]
    T_star = eoi_continuous(s_scalar, h_scalar, demands)
    T_int = eoi_feasible_interval(s_scalar, h_scalar, demands, round_to_int=True)
    eoi_orders = eoi_order_periods(s_scalar, h_scalar, demands)
    eoi_cost = compute_cost_from_orders(eoi_orders, setup_costs, holding_costs, demands)

    print("EOI continuous T*:", T_star)
    print("EOI recommended integer T:", T_int)
    print("EOI order periods (0-based):", eoi_orders)
    print("EOI total cost:", eoi_cost)
    print()

    # Large experiment for cost optimality + runtime distributions
    print("Running 10 000-instance experiment...")
    n = 10
    num_instances = 1000 #10_000
    results = run_ww_vs_eoi_experiments(n=n, num_instances=num_instances, seed=42)

    ww_better = results["ww_better"]
    eoi_better = results["eoi_better"]
    equal_cost = results["equal_cost"]

    print("=== WW vs EOI statistics ===")
    print(f"Horizon n = {n}, instances = {num_instances}")
    print(f"WW strictly cheaper in   : {ww_better} instances")
    print(f"EOI strictly cheaper in  : {eoi_better} instances")
    print(f"Equal cost (≈ numerical) : {equal_cost} instances")
    print()
    
    # Timestamped filenames
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    cost_file = f"ww_eoi_cost_optimality_{ts}.png"
    runtime_file = f"ww_eoi_runtime_efficiency_{ts}.png"
    speed_txt_file = f"ww_eoi_speed_table_{ts}.txt"
    speed_png_file = f"ww_eoi_speed_scaling_{ts}.png"   # NEW
    
    plot_cost_optimality(results, filename=cost_file)
    plot_runtime_efficiency(results, filename=runtime_file)
    
    print("Saved plots:")
    print("  ", cost_file)
    print("  ", runtime_file)
    
    # ------------------------------------------------------------
    # Speed benchmark for different horizons n
    # ------------------------------------------------------------
    ns_to_test = [10, 100, 1000, 10000]
    print("\nBenchmarking speed for horizons:", ns_to_test)
    speed_results = benchmark_speed_for_ns(
        ns=ns_to_test,
        num_instances_per_n=100,
        seed=123,
        )
    
    print_and_save_speed_table(speed_results, filename=speed_txt_file)
    print("Saved speed table:")
    print("  ", speed_txt_file)
    
    # NEW: speed scaling plot
    plot_speed_scaling(speed_results, filename=speed_png_file)
    print("Saved speed scaling plot:")
    print("  ", speed_png_file)


    


import os
import glob
import time
import csv
from collections import deque
from threading import Timer
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

# ==========================================
# 0. CONFIGURATION & CSV SETUP
# ==========================================
CSV_FILE = "BMP_results.csv"
SOL_FOLDER = "solutions"

FIELDNAMES = [
    "Problem", "Num_ver", "Num_edge", "Solver", "Encoding",
    "UB", "Bandwidth", "Status",
    "Time_Gen", "Time_Solve", "Total_Time",
    "Num_clause", "Num_var"
]

def init_files():
    if not os.path.exists(CSV_FILE):
        with open(CSV_FILE, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=FIELDNAMES)
            writer.writeheader()
    if not os.path.exists(SOL_FOLDER):
        os.makedirs(SOL_FOLDER)

def get_existing_result(filename, solver, encoding):
    if not os.path.exists(CSV_FILE): return None
    with open(CSV_FILE, 'r', newline='') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if (row['Problem'] == filename and
                    row['Solver'] == solver and
                    row['Encoding'] == encoding):
                return row
    return None

def update_csv_result(new_data):
    rows = []
    updated = False
    if os.path.exists(CSV_FILE):
        with open(CSV_FILE, 'r', newline='') as f:
            reader = csv.DictReader(f)
            rows = list(reader)

    for row in rows:
        if (row['Problem'] == new_data['Problem'] and
                row['Solver'] == new_data['Solver'] and
                row['Encoding'] == new_data['Encoding']):
            row.update(new_data)
            updated = True
            break

    if not updated: rows.append(new_data)

    with open(CSV_FILE, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)

def save_solution_file(filename, solver, encoding, n, k, model):
    """
    Decodes the SAT model and saves the permutation to a file.
    """
    sol_name = f"{filename}_{encoding}_{solver}.sol"
    sol_path = os.path.join(SOL_FOLDER, sol_name)

    permutation = {}
    min_x = n * n + 1
    max_x = 2 * n * n

    for var in model:
        if var > 0: # Only True variables
            if min_x <= var <= max_x: # Strict check for X variables
                # Decode
                shifted = var - (n * n)
                # 1-based index math
                u = (shifted - 1) // n + 1
                pos = (shifted - 1) % n + 1
                permutation[u] = pos

    # Sort by Node ID for readability
    sorted_perm = dict(sorted(permutation.items()))

    try:
        with open(sol_path, 'w') as f:
            f.write(f"Problem: {filename}\n")
            f.write(f"Solver: {solver}\n")
            f.write(f"Encoding: {encoding}\n")
            f.write(f"Bandwidth: {k}\n")
            f.write("-" * 30 + "\n")
            f.write(f"{'Node':<10} | {'Position':<10}\n")
            f.write("-" * 30 + "\n")
            for u, pos in sorted_perm.items():
                f.write(f"{u:<10} | {pos:<10}\n")
        # print(f"[Saved] Solution saved to {sol_path}")
    except Exception as e:
        print(f"[Error] Could not save solution file: {e}")

# ==========================================
# 1. MTX Parser & Heuristic
# ==========================================
def read_mtx(file_path):
    n_rows = n_cols = data_start = 0
    with open(file_path, 'r') as f: lines = f.readlines()
    for i, line in enumerate(lines):
        if line.startswith('%'): continue
        parts = line.split()
        if len(parts) >= 2:
            n_rows, n_cols = int(parts[0]), int(parts[1])
            data_start = i + 1
            break
    n = max(n_rows, n_cols)
    adj = {i: set() for i in range(1, n + 1)}
    for line in lines[data_start:]:
        line = line.strip()
        if not line or line.startswith('%'): continue
        parts = line.split()
        try: u, v = int(parts[0]), int(parts[1])
        except: continue
        if u == v: continue
        adj[u].add(v); adj[v].add(u)
    return n, sum(len(v) for v in adj.values()) // 2, {k: sorted(list(v)) for k, v in adj.items()}

def calculate_bandwidth(adj, ordering):
    bw = 0
    for u in adj:
        for v in adj[u]:
            dist = abs(ordering[u] - ordering[v])
            if dist > bw: bw = dist
    return bw

def cuthill_mckee(n, adj):
    t_start = time.perf_counter()
    visited = set()
    result_order = []
    nodes_by_deg = sorted(adj.keys(), key=lambda x: len(adj[x]))

    while len(visited) < n:
        start = next((x for x in nodes_by_deg if x not in visited), None)
        if start is None: break

        q = deque([start])
        visited.add(start); result_order.append(start)
        while q:
            u = q.popleft()
            for v in sorted(adj[u], key=lambda x: len(adj[x])):
                if v not in visited:
                    visited.add(v); result_order.append(v); q.append(v)

    ordering = {node: i+1 for i, node in enumerate(result_order)}
    return calculate_bandwidth(adj, ordering), time.perf_counter() - t_start

# ==========================================
# 3. SAT Solver
# ==========================================
def check_sat(n, adj, k, enc_type, solver_name, time_limit):
    t_start = time.perf_counter()
    num_clause = 0
    num_var = 2 * n * n

    with Solver(name=solver_name) as solver:
        def getL(u, i):
            return (u - 1) * n + i

        def getX(u, i):
            return n * n + (u - 1) * n + i

        top_id = num_var

        t_vars_end = time.perf_counter()

        # 1. Constraints: Order encoding for L
        for u in range(1, n + 1):
            solver.add_clause([getL(u, n)]);
            num_clause += 1
            for i in range(1, n):
                solver.add_clause([-getL(u, i), getL(u, i + 1)]);
                num_clause += 1

        # 2. Constraints: Channeling X <-> L
        for u in range(1, n + 1):
            for i in range(1, n + 1):
                if i == 1:
                    solver.add_clause([-getX(u, 1), getL(u, 1)])
                    solver.add_clause([-getL(u, 1), getX(u, 1)])
                    num_clause += 2
                else:
                    solver.add_clause([-getX(u, i), getL(u, i)])
                    solver.add_clause([-getX(u, i), -getL(u, i - 1)])
                    solver.add_clause([-getL(u, i), getL(u, i - 1), getX(u, i)])
                    num_clause += 3

        # 3. Constraints: Exactly One
        for i in range(1, n + 1):
            lits = [getX(u, i) for u in range(1, n + 1)]
            cnf = CardEnc.equals(lits, bound=1, encoding=enc_type, top_id=top_id)
            solver.append_formula(cnf.clauses)
            num_clause += len(cnf.clauses)
            if cnf.nv > top_id: top_id = cnf.nv
            num_var = top_id

        # 4. Constraints: Bandwidth limit K
        for u in range(1, n + 1):
            if u in adj:
                for v in adj[u]:
                    if u < v:
                        for i in range(1, n + 1):
                            target = i + k
                            if target < n:
                                solver.add_clause([-getL(u, i), getL(v, target)])
                                solver.add_clause([-getL(v, i), getL(u, target)])
                                num_clause += 2

        t_clauses_end = time.perf_counter()

        model = None
        is_sat = False

        def interrupt(s):
            s.interrupt()

        timer = Timer(time_limit, interrupt, [solver])
        timer.start()

        try:
            is_sat = solver.solve_limited(expect_interrupt=True)
            if is_sat is True:
                model = solver.get_model()
        except:
            is_sat = None
        finally:
            timer.cancel()

        t_solve_end = time.perf_counter()

        return is_sat, model, num_var, num_clause, (t_vars_end - t_start), (t_clauses_end - t_vars_end), (
                    t_solve_end - t_clauses_end)

def solve_bandwidth(n, num_edges, adj, filename, encoding_method, solver_name, timeout):
    print(f"\n{'='*80}")
    print(f"PROCESSING: {filename} (N={n})")
    print(f"{'='*80}")

    existing = get_existing_result(filename, solver_name, encoding_method)
    start_k = n
    acc_gen = 0.0
    acc_sol = 0.0
    total_t = 0.0

    if existing:
        status = existing.get('Status', '')
        saved_bw = int(existing.get('Bandwidth', n))
        saved_ub = int(existing.get('UB', n))

        if status in ['OPTIMIZE', 'TIME_OUT']:
            print(f"[Info] Status is {status} (K={saved_bw}). Skipping.")
            return
        elif status == 'PENDING':
            print(f"[Info] Resuming PENDING from K={saved_bw - 1}...")
            start_k = saved_bw - 1
            try:
                acc_gen = float(existing.get('Time_Gen', 0))
                acc_sol = float(existing.get('Time_Solve', 0))
                total_t = float(existing.get('Total_Time', 0))
            except: pass
    else:
        # Heuristic
        ub, t_h = cuthill_mckee(n, adj)
        start_k = ub - 1
        total_t += t_h
        print(f"Heuristic UB: {ub} ({t_h:.4f}s)")

        update_csv_result({
            "Problem": filename, "Num_ver": n, "Num_edge": num_edges,
            "Solver": solver_name, "Encoding": encoding_method,
            "UB": ub, "Bandwidth": ub, "Status": "PENDING",
            "Time_Gen": 0, "Time_Solve": 0, "Total_Time": round(total_t, 4),
            "Num_clause": 0, "Num_var": 0
        })

    enc_map = { 'pairwise': EncType.pairwise, 'seqcounter': EncType.seqcounter, 'sortnet': EncType.sortnetwrk, 'totalizer': EncType.totalizer }
    sel_enc = enc_map.get(encoding_method, EncType.totalizer)

    print(f"{'K':<4} | {'Result':<9} | {'Vars':<7} | {'Clauses':<8} | {'T_Gen(s)':<8} | {'T_Solve(s)':<9}")
    print("-" * 80)

    best_k = start_k + 1

    for k in range(start_k, 0, -1):
        try:
            is_sat, model, n_v, n_c, t_v, t_c, t_s = check_sat(
                n, adj, k, sel_enc, solver_name, timeout
            )

            t_gen = t_v + t_c
            acc_gen += t_gen
            acc_sol += t_s
            total_t += (t_gen + t_s)

            if is_sat is None: # Timeout
                print(f"{k:<4} | {'TIMEOUT':<9} | {n_v:<7} | {n_c:<8} | {t_gen:<8.4f} | {t_s:<9.4f}")
                update_csv_result({
                    "Problem": filename, "Solver": solver_name, "Encoding": encoding_method,
                    "Bandwidth": best_k, "Status": "TIME_OUT",
                    "Time_Gen": round(acc_gen, 4), "Time_Solve": round(acc_sol, 4),
                    "Total_Time": round(total_t, 4), "Num_clause": n_c, "Num_var": n_v
                })
                break

            if is_sat:
                print(f"{k:<4} | {'SAT':<9} | {n_v:<7} | {n_c:<8} | {t_gen:<8.4f} | {t_s:<9.4f}")
                best_k = k
                save_solution_file(filename, solver_name, encoding_method, n, k, model)

                update_csv_result({
                    "Problem": filename, "Solver": solver_name, "Encoding": encoding_method,
                    "Bandwidth": best_k, "Status": "PENDING",
                    "Time_Gen": round(acc_gen, 4), "Time_Solve": round(acc_sol, 4),
                    "Total_Time": round(total_t, 4), "Num_clause": n_c, "Num_var": n_v
                })
            else:
                print(f"{k:<4} | {'UNSAT':<9} | {n_v:<7} | {n_c:<8} | {t_gen:<8.4f} | {t_s:<9.4f}")
                print(f">>> UNSAT. Optimal found: {best_k}")
                update_csv_result({
                    "Problem": filename, "Solver": solver_name, "Encoding": encoding_method,
                    "Bandwidth": best_k, "Status": "OPTIMIZE",
                    "Time_Gen": round(acc_gen, 4), "Time_Solve": round(acc_sol, 4),
                    "Total_Time": round(total_t, 4), "Num_clause": n_c, "Num_var": n_v
                })
                break

        except Exception as e:
            print(f"\n[Error] Solver failed: {e}")
            break

# ==========================================
# 4. Main Configuration
# ==========================================
def parse_range(u_in, n_files):
    u_in = str(u_in).lower().strip()
    if u_in == 'all': return list(range(n_files))
    if 'to' in u_in:
        try:
            s, e = map(int, u_in.split('to'))
            return list(range(max(0, s - 1), min(n_files, e)))
        except: return []
    if u_in.isdigit():
        i = int(u_in) - 1
        return [i] if 0 <= i < n_files else []
    return []


if __name__ == "__main__":
    init_files()
    folder = 'testcase'
    if not os.path.exists(folder): exit()
    files = sorted(glob.glob(os.path.join(folder, '*.mtx')))
    if not files: exit()

    print(f"Found {len(files)} files.")
    for i, f in enumerate(files): print(f"  [{i + 1}] {os.path.basename(f)}")

    # === CONFIG ===
    SELECTION = "1 to 32"
    ENCODING_LIST = ["totalizer", "sortnet", "pairwise", "seqcounter"]
    SOLVER = "glucose3"
    TIMEOUT = 1000.0
    # ==============

    idxs = parse_range(SELECTION, len(files))

    for encoding in ENCODING_LIST:
        print(f"\n{'#' * 60}")
        print(f"### STARTING BATCH FOR ENCODING: {encoding.upper()}")
        print(f"{'#' * 60}")

        for i in idxs:
            try:
                filename = os.path.basename(files[i])
                print(f"\n>>> Processing {filename} with ENCODING: {encoding}")
                n, e, adj = read_mtx(files[i])
                solve_bandwidth(n, e, adj, filename, encoding, SOLVER, TIMEOUT)

            except Exception as ex:
                print(f"Error with file {files[i]}: {ex}")
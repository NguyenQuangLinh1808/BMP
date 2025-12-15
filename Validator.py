import os
import glob
import sys

# ==========================================
# Helper Functions
# ==========================================
def read_mtx_simple(file_path):
    """Reads MTX and returns simple adjacency list."""
    adj = {}
    if not os.path.exists(file_path):
        return None

    with open(file_path, 'r') as f:
        lines = f.readlines()

    data_start = 0
    for i, line in enumerate(lines):
        if not line.startswith('%'):
            data_start = i + 1
            break

    for line in lines[data_start:]:
        parts = line.split()
        if not parts: continue
        try:
            u, v = int(parts[0]), int(parts[1])
            if u == v: continue

            if u not in adj: adj[u] = []
            if v not in adj: adj[v] = []
            adj[u].append(v)
            adj[v].append(u)
        except: pass
    return adj

def read_solution(sol_path):
    """Reads the generated .sol file."""
    mapping = {}
    claimed_bw = -1

    if not os.path.exists(sol_path):
        return -1, None

    with open(sol_path, 'r') as f:
        lines = f.readlines()

    for line in lines:
        line = line.strip()
        if line.startswith("Bandwidth:"):
            try:
                claimed_bw = int(line.split(":")[1].strip())
            except: pass
            continue

        if "|" in line and "Node" not in line:
            parts = line.split("|")
            try:
                u = int(parts[0].strip())
                pos = int(parts[1].strip())
                mapping[u] = pos
            except: pass
    return claimed_bw, mapping

def validate_single_file(mtx_path, sol_path):
    """
    Validates one solution file against its matrix.
    Returns: (is_valid, message, actual_bw, claimed_bw)
    """
    adj = read_mtx_simple(mtx_path)
    if adj is None:
        return False, "MTX file not found", 0, 0

    claimed_bw, mapping = read_solution(sol_path)

    if not mapping:
        return False, "Empty or invalid solution file", 0, 0

    # Check 1: Completeness
    # Note: Some sparse matrices might define nodes that have no edges.
    # We strictly check if nodes present in the edge list are mapped.
    missing_nodes = [u for u in adj if u not in mapping]
    if missing_nodes:
        return False, f"Missing {len(missing_nodes)} mapped nodes", 0, claimed_bw

    # Check 2: Uniqueness
    positions = list(mapping.values())
    if len(positions) != len(set(positions)):
        return False, "Duplicate positions detected", 0, claimed_bw

    # Check 3: Calculate Actual Bandwidth
    max_bw = 0
    for u in adj:
        for v in adj[u]:
            if u not in mapping or v not in mapping: continue
            dist = abs(mapping[u] - mapping[v])
            if dist > max_bw:
                max_bw = dist

    if max_bw <= claimed_bw:
        return True, "OK", max_bw, claimed_bw
    else:
        return False, f"Actual ({max_bw}) > Claimed ({claimed_bw})", max_bw, claimed_bw

# ==========================================
# Main Batch Validator
# ==========================================
def main():
    SOL_DIR = "solutions"
    CASE_DIR = "testcase"

    if not os.path.exists(SOL_DIR):
        print(f"Error: Solution directory '{SOL_DIR}' not found.")
        return

    # Find all solution files
    sol_files = sorted(glob.glob(os.path.join(SOL_DIR, "*.sol")))

    if not sol_files:
        print(f"No .sol files found in '{SOL_DIR}'.")
        return

    print(f"{'='*90}")
    print(f"{'Solution File':<40} | {'Status':<6} | {'Calc BW':<8} | {'Claim BW':<8} | {'Message'}")
    print(f"{'-'*90}")

    passed_count = 0
    failed_count = 0

    for sol_path in sol_files:
        sol_name = os.path.basename(sol_path)

        # Parse MTX filename from Solution filename
        # Format: {mtx_name}_{enc}_{solver}.sol
        # Logic: find index of ".mtx" and extract everything before it + ".mtx"
        if ".mtx" not in sol_name:
            print(f"{sol_name:<40} | {'SKIP':<6} | {'-':<8} | {'-':<8} | Unknown filename format")
            continue

        mtx_name_end = sol_name.find(".mtx") + 4
        mtx_name = sol_name[:mtx_name_end]
        mtx_path = os.path.join(CASE_DIR, mtx_name)

        # Validate
        is_valid, msg, actual_bw, claimed_bw = validate_single_file(mtx_path, sol_path)

        status = "PASS" if is_valid else "FAIL"
        if is_valid: passed_count += 1
        else: failed_count += 1

        print(f"{sol_name:<40} | {status:<6} | {actual_bw:<8} | {claimed_bw:<8} | {msg}")

    print(f"{'-'*90}")
    print(f"Summary: {passed_count} Passed, {failed_count} Failed, {len(sol_files)} Total.")
    print(f"{'='*90}")

if __name__ == "__main__":
    main()
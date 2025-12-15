#Use L(u, i) <= i + 1 to check exactly one label for each vertex
#Not use, run slow
import collections

from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType


def solve_bmp(n, edges, k):
    solver = Glucose3()
    def getL(u, i):
        return (u * n) + i + 1
    def ladder_logic():
        for u in range(n):
            for i in range(n - 1):
                solver.add_clause([-getL(u, i), getL(u, i + 1)])
            solver.add_clause([getL(u, n - 1)])
    def bandwidth():
        for u, v in edges:
            for i in range(n):
                if i + k < n:
                    solver.add_clause([-getL(u, i), getL(v, i + k)])
                    solver.add_clause([-getL(v, i), getL(u, i + k)])
    def exacly_one():
        for i in range(n):
            array = []
            for u in range(n):
                array.append(getL(u, i))
            cnf = CardEnc.equals(lits=array, bound=i + 1, top_id=solver.nof_vars(), encoding=EncType.totalizer)
            solver.append_formula(cnf.clauses)

    def solve_and_decode():
        if solver.solve():
            model = solver.get_model()
            solution = {}
            for u in range(n):
                for i in range(n):
                    if getL(u, i) in model:
                        solution[u] = i
                        break
            return solution
        else:
            return None
    ladder_logic()
    bandwidth()
    exacly_one()
    return solve_and_decode()

#Use X(u, i) = 1 to find exactly one vertex for each label
#Use this solution
def check_sat(n, adj, k, enc_type, solver_name):
    num_clause = 0
    num_var = 2 * n * n

    with Solver(name=solver_name) as solver:
        def getL(u, i):
            return (u - 1) * n + i

        def getX(u, i):
            return n * n + (u - 1) * n + i

        top_id = num_var

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


#Function find k
def reverse_cuthill_mckee(n, adj):
    visited = [False] * n
    rcm_order = []
    nodes_by_deg = sorted(range(n), key=lambda x: len(adj[x]))
    for start in nodes_by_deg:
        if visited[start]: continue
        q = collections.deque([start])
        visited[start] = True
        comp = []
        while q:
            u = q.popleft()
            comp.append(u)
            nbrs = sorted([v for v in adj[u] if not visited[v]], key=lambda x: len(adj[x]))
            for v in nbrs:
                visited[v] = True
                q.append(v)
        rcm_order.extend(comp[::-1])
    return rcm_order


def calculate_bandwidth(n, adj, order):
    pos = {node: i for i, node in enumerate(order)}
    bw = 0
    for u in range(n):
        for v in adj[u]:
            bw = max(bw, abs(pos[u] - pos[v]))
    return bw


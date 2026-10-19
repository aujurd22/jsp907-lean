"""Independent computational check of Theorem 4.1 (paper 2604.06609, Section 4).
Uses SAT (pysat) for colouring and explicit cycle enumeration for the chord bound."""
import itertools
from pysat.solvers import Cadical153

LETTERS = {'a': 0, 'b': 1, 'c': 2, 'd': 3, 'e': 4}


def build(m):
    verts, edges = [], []

    def add_block(name):
        base = len(verts)
        verts.extend(f"{name}[{L}]" for L in 'abcde')
        for k in range(5):
            edges.append((base + k, base + (k + 1) % 5))
        return base

    spine = {i: add_block(f"S{i}") for i in range(m + 1)}
    for i in range(m):
        edges.append((spine[i] + LETTERS['c'], spine[i + 1] + LETTERS['a']))
    leaves = []
    def add_leaf(i, x):
        base = add_block(f"L{i},{x}")
        leaves.append((i, x, base))
        edges.append((spine[i] + LETTERS[x], base + LETTERS[x]))
    for x in 'abde': add_leaf(0, x)
    for i in range(1, m):
        for x in 'bde': add_leaf(i, x)
    for x in 'bcde': add_leaf(m, x)
    v = len(verts); verts.append("v")
    for (i, x, base) in leaves:
        X = LETTERS[x]
        for Y in range(5):
            if Y != X:
                edges.append((v, base + Y))
    n = len(verts)
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    return n, adj, verts, edges


def colourable(n, adj, k):
    """SAT check: is the graph k-colourable?"""
    var = lambda v, c: v * k + c + 1
    clauses = []
    for v in range(n):
        clauses.append([var(v, c) for c in range(k)])
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                clauses.append([-var(v, c1), -var(v, c2)])
    for a in range(n):
        for b in adj[a]:
            if b > a:
                for c in range(k):
                    clauses.append([-var(a, c), -var(b, c)])
    with Cadical153(bootstrap_with=clauses) as s:
        return s.solve()


def k4_free(n, adj):
    for a in range(n):
        for b in adj[a]:
            if b <= a: continue
            for c in adj[a] & adj[b]:
                if c > b and (adj[a] & adj[b] & adj[c]):
                    return False
    return True


def degeneracy(n, adj, skip=None):
    alive = [set(s) for s in adj]
    if skip:
        a, b = skip
        alive[a].discard(b); alive[b].discard(a)
    removed = [False] * n
    deg = 0
    for _ in range(n):
        best, bd = -1, 10**9
        for i in range(n):
            if not removed[i] and len(alive[i]) < bd:
                best, bd = i, len(alive[i])
        deg = max(deg, bd)
        removed[best] = True
        for j in list(alive[best]):
            alive[j].discard(best)
    return deg


def all_cycles_through(n, adj, start, limit=200000):
    """Enumerate simple cycles containing `start` (as vertex sequences, start first)."""
    cycles = []
    path = [start]
    onpath = {start}
    def dfs(u, depth):
        if len(cycles) > limit:
            return
        for w in adj[u]:
            if w == start and depth >= 2:
                cycles.append(list(path))
            elif w not in onpath and w > start:  # canonical: only visit vertices > start
                onpath.add(w); path.append(w)
                dfs(w, depth + 1)
                path.pop(); onpath.discard(w)
    # allow visiting any vertex except start, but require start be the minimum? Not valid:
    # cycles through start need not have start minimal. Use onpath only.
    def dfs2(u, depth):
        if len(cycles) > limit: return
        for w in adj[u]:
            if w == start:
                if depth >= 2:
                    cycles.append(list(path))
            elif w not in onpath:
                onpath.add(w); path.append(w)
                dfs2(w, depth + 1)
                path.pop(); onpath.discard(w)
    dfs2(start, 0)
    return cycles


def chords_of(cycle, adj):
    cs = set(cycle)
    k = len(cycle)
    consec = set()
    for i in range(k):
        a, b = cycle[i], cycle[(i + 1) % k]
        consec.add((min(a, b), max(a, b)))
    cnt = 0
    for (a, b) in consec:
        pass
    # count edges inside cs that are not consecutive
    seen = set()
    for a in cs:
        for b in adj[a]:
            if b in cs and b > a:
                if (a, b) not in consec:
                    cnt += 1
    return cnt


def main():
    for m in range(1, 4):
        n, adj, verts, edges = build(m)
        print(f"m={m}: |V|={n} (exp {20*m+31})  |E|={len(edges)}  degrees={sorted(set(len(s) for s in adj))}")
        print(f"   K4-free: {k4_free(n, adj)}")
        print(f"   3-colourable: {colourable(n, adj, 3)} (expect False)   4-colourable: {colourable(n, adj, 4)} (expect True)")
        print(f"   degeneracy(G): {degeneracy(n, adj)}")
        bad = sum(1 for e in edges if degeneracy(n, adj, skip=e) > 2)
        print(f"   edges e with G-e NOT 2-degenerate: {bad} / {len(edges)}")
        # cycles through v
        v = n - 1
        cyc = all_cycles_through(n, adj, v)
        mx = max((chords_of(c, adj) for c in cyc), default=0)
        print(f"   cycles through v: {len(cyc)}   max chords: {mx} (expect <=10)")


if __name__ == '__main__':
    main()

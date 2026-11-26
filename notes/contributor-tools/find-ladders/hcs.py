"""Verify a gate list against a desk `HasCircuitSize n (fun x : Fin n → Bool => EXPR) s` statement and
emit the Lean proof (column replay, one kernel decide).

usage: hcs.py gaps.json GAP_ID witness.txt [out.lean] [--stmt-file f]
witness.txt: lines 'op a b' (0 AND, 1 OR, 2 NOT with b=-1); gate j writes wire n+j; output = last gate.
         A line 'out w' overrides the output wire.
Without out.lean: only verifies (exhaustively, in Python) and prints size and verdict.
"""
import json, re, sys, itertools

def load_stmt(gaps, gid):
    if gaps.endswith('.txt'):
        return open(gaps, encoding='utf-8').read().strip()
    g = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}[gid]
    return g['statement'].strip()

def parse(stmt):
    m = re.match(r'PEqualNP\.MetaComplexity\.HasCircuitSize (\d+) \(fun x : Fin \d+ → Bool => (.*)\) (\d+)$', stmt, re.S)
    if not m: raise SystemExit('unsupported statement shape')
    n, expr, s = int(m.group(1)), m.group(2), int(m.group(3))
    py = re.sub(r'\bx (\d+)', r'x[\1]', expr)
    py = py.replace('&&', ' and ').replace('||', ' or ').replace('!', ' not ')
    f = eval('lambda x: bool(' + py + ')')
    return n, f, s

def read_wit(fn):
    gates, out = [], None
    for line in open(fn):
        p = line.split()
        if len(p) == 3 and p[0] in ('0', '1', '2'):
            gates.append(tuple(int(t) for t in p))
        elif len(p) == 2 and p[0] == 'out':
            out = int(p[1])
    return gates, out

def run(n, gates, out, x):
    w = list(x)
    for o, a, b in gates:
        w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
    return w[out]

def main():
    gaps, gid, wit = sys.argv[1:4]
    outf = sys.argv[4] if len(sys.argv) > 4 else None
    stmt = load_stmt(gaps, gid)
    n, f, s = parse(stmt)
    gates, out = read_wit(wit)
    if out is None: out = n + len(gates) - 1
    for j, (o, a, b) in enumerate(gates):
        assert 0 <= a < n + j and (o == 2 or 0 <= b < n + j), ('gate reads a later wire', j)
    bad = sum(1 for x in itertools.product([False, True], repeat=n) if run(n, gates, out, x) != f(x))
    print(gid, 'n', n, 'gates', len(gates), 'bound', s, 'mismatches', bad, 'OK' if bad == 0 and len(gates) <= s else 'FAIL')
    if bad or len(gates) > s or not outf: return
    ops = {0: 'and', 1: 'or', 2: 'not'}
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
    name = gid.replace('-', '_')
    body = f"""import PEqualNP.Defs
import PEqualNP.Library.Helpers.ReplayCol

namespace PEqualNP.Outside.{name}

open PEqualNP.CircuitLowerBounds

/-- The witness circuit ({len(gates)} gates, found by SAT-based exact synthesis on the care rows of the
monotone part): gate `j` writes wire `{n} + j`. -/
def witness : Circuit :=
  ⟨[{gl}], {out}⟩

end PEqualNP.Outside.{name}

theorem PEqualNP.Outside.{name} : {stmt} :=
  PEqualNP.Library.Helpers.ReplayCol.hasCircuitSize_of_colReplay PEqualNP.Outside.{name}.witness
    (by decide +kernel)
"""
    open(outf, 'w', encoding='utf-8', newline='\n').write(body)
    print('wrote', outf)

main()

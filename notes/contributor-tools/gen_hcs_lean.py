"""Render a synth_sat witness as a Lean proof of a `HasCircuitSize n f s` gap
or a `RepSizeAtMost A s` gap (statement copied verbatim from the gap JSON).

usage: gen_hcs_lean.py gaps.json GAP_ID witness.txt out.lean
witness.txt: synth_sat output; lines 'op a b' (0 AND, 1 OR, 2 NOT with b=-1); output = last gate.
"""
import json, sys

def main():
    gaps, gid, wit, out = sys.argv[1:5]
    g = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}[gid]
    stmt = g['statement'].strip()
    gates = []
    for line in open(wit):
        p = line.split()
        if len(p) == 3 and p[0] in ('0', '1', '2'):
            gates.append(tuple(int(t) for t in p))
    ops = {0: 'and', 1: 'or', 2: 'not'}
    if stmt.startswith('PEqualNP.MetaComplexity.HasCircuitSize'):
        n = int(stmt.split()[1]); kind = 'hcs'
    elif stmt.startswith('PEqualNP.Represents.RepSizeAtMost'):
        kind = 'rep'; n = None
    else:
        raise SystemExit('unsupported statement shape')
    # inputs count: max wire index not produced by a gate
    first_gate_wire = None
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
    ninp = n if n is not None else int(sys.argv[5])
    outw = ninp + len(gates) - 1
    name = gid.replace('-', '_')
    if kind == 'hcs':
        proof = f"""  refine ⟨PEqualNP.Outside.{name}.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.{name}.witness]
  · decide +kernel"""
    else:
        proof = f"""  refine ⟨PEqualNP.Outside.{name}.witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.{name}.witness]
  · decide +kernel"""
    body = f"""import PEqualNP.Defs

namespace PEqualNP.Outside.{name}

open PEqualNP.CircuitLowerBounds

/-- The witness circuit, found by SAT-based exact synthesis: gate `j` writes wire `{ninp} + j`,
the output is the last gate. -/
def witness : Circuit :=
  ⟨[{gl}], {outw}⟩

end PEqualNP.Outside.{name}

theorem PEqualNP.Outside.{name} : {stmt} := by
{proof}
"""
    open(out, 'w', encoding='utf-8', newline='\n').write(body)

main()

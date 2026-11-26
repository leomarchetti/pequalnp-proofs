"""Render a found circuit (notsearch output) as a Lean proof of the exact gap statement.

usage: gen_lean.py gaps.json GAP_ID circuit.txt out.lean [--drop-not]
circuit.txt: lines 'op a b' (op 0 AND, 1 OR, 2 NOT with b=-1) after an optional FOUND line.
The output wire is the last gate. The proof is `decide` on the explicit witness.
--drop-not: test mode, removes the last two conjuncts (NOT conditions) to time the rest.
"""
import json, sys

def main():
    gaps, gid, circ, out = sys.argv[1:5]
    drop = '--drop-not' in sys.argv
    g = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}[gid]
    stmt = g['statement']
    gates = []
    for line in open(circ):
        p = line.split()
        if len(p) == 3 and p[0] in '012':
            op, a, b = int(p[0]), int(p[1]), int(p[2])
            gates.append((op, a, b))
    ops = {0: 'and', 1: 'or', 2: 'not'}
    gl = ', '.join(
        '⟨GateOp.%s, [%s]⟩' % (ops[op], str(a) if op == 2 else '%d, %d' % (a, b))
        for op, a, b in gates)
    out_wire = 5 + len(gates) - 1
    if drop:
        idx = stmt.index(' ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not →')
        stmt = stmt[:idx]
    name = gid.replace('-', '_')
    rest = 'by decide'
    body = f"""import PEqualNP.Defs

namespace PEqualNP.Outside.{name}

open PEqualNP.CircuitLowerBounds

/-- The witness circuit: gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[{gl}], {out_wire}⟩

end PEqualNP.Outside.{name}

theorem PEqualNP.Outside.{name} :
    {stmt} :=
  by
    refine ⟨PEqualNP.Outside.{name}.witness, ?_, ?_, {rest}⟩
    · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.{name}.witness]
    · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
      decide
"""
    open(out, 'w', encoding='utf-8', newline='\n').write(body)

main()

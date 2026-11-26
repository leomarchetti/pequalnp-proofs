"""Verify a gate list against a 4x4 'Represents' step and splice the proof into the desk skeleton.

usage: mk_rep.py GAP_NUM witness.txt skeleton.lean
Statement shape: ∃ C, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin 4 => (MASK : ℕ).testBit (4*u+v)) C
Inputs: wires 0..3 left one-hot, 4..7 right one-hot; output = last gate.
"""
import re, sys
num, wit, skel = sys.argv[1:4]
src = open(skel, encoding='utf-8').read()
m = re.search(r'size ≤ (\d+) ∧ PEqualNP\.Represents\.Represents \(fun u v : Fin 4 => \((\d+) : ℕ\)\.testBit', src)
s, mask = int(m.group(1)), int(m.group(2))
gates = [tuple(map(int, l.split())) for l in open(wit) if l.strip()]
out = 8 + len(gates) - 1
for u in range(4):
    for v in range(4):
        w = [i == u for i in range(4)] + [j == v for j in range(4)]
        for o, a, b in gates:
            w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
        assert w[out] == bool((mask >> (4 * u + v)) & 1), ('mismatch', u, v)
assert len(gates) <= s
ops = {0: 'and', 1: 'or', 2: 'not'}
gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
ns = 'PEqualNP.Outside.L_meta_%s.Helpers' % num
block = f"""namespace {ns}

open PEqualNP.CircuitLowerBounds

/-- A {len(gates)}-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex,
4..7 the right vertex, gate `j` writes wire `8 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[{gl}], {out}⟩

end {ns}

"""
proof = f"""  refine ⟨{ns}.witness, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, {ns}.witness]"""
i = src.index('theorem ')
src = src[:i] + block + src[i:]
assert src.rstrip().endswith('sorry')
src = src.rstrip()[:-len('sorry')].rstrip() + '\n' + proof + '\n'
src = src.replace(':= by\n\n', ':= by\n')
open(skel, 'w', encoding='utf-8', newline='\n').write(src)
print('OK', num, 'gates', len(gates), 'bound', s)

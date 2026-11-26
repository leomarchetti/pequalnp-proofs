# FIND ladders: exact monotone synthesis on care rows

The desk posts calibration ladders ("We hold N gates ... we do not know whether N-1 exists") for small
graph and matrix functions: `HasCircuitSize n f s` (AND/OR/NOT) or `RepSizeAtMost A s` (AND/OR,
one vertex on each side). Each rung is a proof PR, and a lower rung settles the rungs above it.
List the open ones from the public snapshot:

```
curl -s https://data.pequalnp.com/data/desk/gaps.json -o gaps.json
# rows whose context says "Answer with a circuit" / "FIND" / "gate list" and pr_open == 0
```

## Why care rows

For a monotone target f, a monotone circuit C equals f iff C is 1 on every minterm and 0 on every
maximal false point (monotonicity fills in the rest). So the SAT instance needs a few dozen rows
instead of 2^n: 30 rows for K4-in-K5, 140 for 5-vertex connectivity, 21 for the 3x3 permanent.
For an anti-monotone target (e.g. 3-colourability = NOT K4) synthesise the monotone part and add
one NOT at the output.

## Tools

- `care_stmt.py gaps.json GAP out.txt`: care rows straight from a monotone DNF statement.
- `care_graph.py PROP n out.txt`: care rows for conn / k4 / pm / tri on K_n edge bits
  (lexicographic edge order, which is what the desk statements use: (0,1),(0,2),...).
- `synth_sat2.py n SPEC S allow_not cadical workdir [secs]`: exact synthesis with S gates.
  `SPEC` is `care:file`, `hex:tt`, `rel:nl:hex` (one-each relation), `th2p:m`, `maj:k`.
  Symmetry breaking (all valid for exhaustive UNSAT claims):
  - `PSYM='and:0-1,or:0-1,and:0-7,or:0-7'`: some gate is one of these. Valid when every pair of
    distinct inputs maps to a listed pair under a symmetry of f. For K_n edge functions the pair
    orbits are "edges sharing a vertex" (0,1) and "disjoint edges" ((0,1) with (2,3); index 7 for
    n = 5, 5 for n = 4, 9 for n = 6). For the 3x3 matrix: same row (0,1), different row and column (0,4).
  - `RSYM=1 RSYM_NL=nl`: crown relations; `SYMM=1`: symmetric functions.
- `care_shards.sh S T` (env `CARE=file PFX=tag`): the four PSYM shards of a K5 edge function in
  parallel; together they are exhaustive.
- `hcs.py gaps.json GAP witness.txt [out.lean]`: exhaustive Python check of a gate list
  (`op a b`, 0 AND 1 OR 2 NOT) against the statement, then the Lean file. Two proof forms both
  pass `lake env lean`: `hasCircuitSize_of_colReplay witness (by decide +kernel)` (needs
  `import PEqualNP.Library.Helpers.ReplayCol`; the desk's advice for 15 inputs), and plain
  `refine ⟨witness, ?_, by decide, ?_⟩; simp [FanInTwo, witness]; decide +kernel` (69 s at 10 inputs).
- `dp2.py`, `build.py`: crown cost model and builder (w_i = x_i OR y_i, then two-of under the
  at-most-two promise; split / grid / alone / tri plans). Reproduces every held crown value.

## Hand constructions worth knowing (Nov 26)

- K4 in K5 (10 edge bits, 3-colourability ladder 17435/17732/17737): 20 monotone gates, so 21 with
  the NOT (`k4_hand21.txt`, verified). Split the vertices {0,1} | {2,3,4}: centre in {0,1} is
  T(234) AND (star0 OR star1) (8 gates, optimal for its 9 inputs); centre in {2,3,4} is e01 AND
  X(b; e) with b_i = e0i AND e1i and X = "some edge of the triangle with both ends labelled"
  (7 gates; SAT says 6 is impossible, with or without NOT). The rungs are 20/18/16, so one gate short.
- Triangle in K_n, depth-3 formulas: 2T - 1 + tau gates (T triangles, tau = least edge set meeting
  every triangle). K5: 23 (desk 25), K6: 45 (desk 49). Same count for any "OR of triples where every
  pair lies in one triple" (perfect matchings of K6: 34, the desk's value; 3x3 permanent: 14).

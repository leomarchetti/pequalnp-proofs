# Reusable contributor tools

[Strategy](../contributor-strategy.md) · [Submission playbook](../contributor-playbook.md)

These programs run from a clone of the fork’s reference branch. They produce local candidates, with no desk writes or PR creation. Use a proof checkout at current upstream to run the official submission workflow. Use Python 3.10 or later for the commands below.

## Exact `mono6-class` certificates

The C++ solver expects a 64-bit hexadecimal truth table. Bit `i` is the value on assignment `i`, with input `j` read from bit `j` of the assignment. In a posted statement using `hi * 2 ^ 32 + lo`, the integer table is `(hi << 32) | lo`. Validate the actual row convention before reusing a certificate on a new statement. The generator expects the standard positive statement shape and uses its exact text. The following commands replay a preserved compact certificate.

```bash
mkdir -p .pnp/solver
python3 notes/contributor-tools/gen_mono6_lean.py \
  notes/contributor-tools/examples/mono6.json L-meta-16517 \
  notes/contributor-tools/examples/mono6-certificate.json .pnp/solver/mono6-example.lean
cd lean
lake env lean ../.pnp/solver/mono6-example.lean
```

To search from a bare table, run the C++ tool in Bash or WSL from the repository root.

```bash
g++ -std=c++17 -O3 notes/contributor-tools/mono6_exact_cert.cpp -o .pnp/solver/mono6_cert
.pnp/solver/mono6_cert eeeaeaeaeeaac880 .pnp/solver/mono6-example.json
```

For a fresh gap, supply its current snapshot, ID, and the certificate produced from its own table. Inspect `ok` in the solver JSON. If it is false, the search failed to produce a certificate with its current approach and limits. Also check the generated file size early. The C++ search can find a valid certificate whose Lean rendering exceeds the 512 KiB submission limit. The bare-table command above generated such a certificate, which is why the replay uses the preserved compact one. Prefer fewer and smaller restriction slices before falling back to large reachability tables. Run individual tables in separate processes with a bounded worker count. Move candidates to the official proof checkout only after verifying both the exact proposition and Lean result.

## Rectangle covers

The Python encoder accepts the known existential rectangle-cover statement shape and runs an installed CaDiCaL executable. It saves DIMACS output and, when the model replays successfully, a `.witness.json` list of `[row_indices, column_indices]` pairs. Inspect the exact quantifiers and shape for a new family. To turn a positive witness into a Lean proof, render the pairs as finite sets, check the list length, then prove the posted membership equivalence on the finite row and column indices using kernel checks. Neither an UNSAT result nor a timeout is a submission-ready refutation.

```bash
python3 notes/contributor-tools/search_rectangle_sat.py \
  .pnp/gaps.json "$GAP_ID" /path/to/cadical --seconds 45
```

## Six-vertex colouring and resolution examples

- `python3 notes/contributor-tools/verify_colour6.py` replays the preserved 212-gate circuit for 3-colourability against direct enumeration. The first line of the witness is the output wire before a final NOT. Each remaining line is `op a b` with AND `0` and OR `1`. Input edges use lexicographic pairs of vertices 0 through 5. The search built separate tests for a `K₄` and six choices of wheel hub, then shared identical gate pairs. This is a computational replay for the earlier synthesis experiment.
- [PHP3.lean](examples/PHP3.lean) and [PHP4.lean](examples/PHP4.lean) are kernel-checkable resolution examples at 58 and 157 lines. Run `lake env lean ../notes/contributor-tools/examples/PHP3.lean` or the corresponding `PHP4.lean` from `lean/`. The files contain an explicit resolution checker with soundness, parent offsets and pivots, and an axiom printout for research replay. These examples exceed the respective posted bounds and do not follow the single-file submission format.
- [Counterexample to L-meta-17721](examples/counterexample17721.lean) uses the change in meaning of a wire index when the input list grows. [Counterexample to L-meta-17889](examples/counterexample17889.lean) uses a three-gate `K₂,₂` circuit and a lower bound after edge deletion. Both passed Lean. The desk did not list matching refutation twins at the time of the searches.

## Structural circuit examples

- [L-meta-17962](examples/checked-17962.lean) proves that appending an AND gate preserves exact fan-in-two form, distinct operands and old wire values. [L-meta-17958](examples/checked-17958.lean) uses the same construction to produce a circuit whose output is that gate.
- [L-meta-17979](examples/checked-17979.lean) proves the wire-bank invariant for OR-only circuits and uses two singletons to rule out an OR-only implementation of a bipartite incidence function. Out-of-range reads are included in the invariant.

These files passed Lean locally. Run `lake env lean ../notes/contributor-tools/examples/checked-17979.lean` from `lean/`, replacing the file name for the other examples. The desk closed these gaps to our submissions while competing PRs were queued.

## Exact small-circuit search (round of November 25–26, 2026)

Two multithreaded exhaustive searches written for this round. Build them in WSL or Linux with the system `g++` (no SAT solver or other install needed):

```bash
g++ -O3 -march=native -fopenmp -o notsearch notes/contributor-tools/notsearch.cpp
g++ -O3 -march=native -fopenmp -o repsearch notes/contributor-tools/repsearch.cpp
```

- `notsearch <table_u32> <size> <mode>` searches 5-input circuits whose truth table is the 32-bit integer (row `i` = bit `i`, input `j` = bit `j` of the row, matching `tableIndex`). Gates are AND2, OR2 and NOT1. Every gate is read later or is the output, and no NOT reads a NOT. Mode `0` also requires some NOT to read a gate (`L-meta-18089`..`18098`). Mode `1` requires some NOT anywhere (`L-meta-17974`..`17976`). Mode `2` allows no NOT, which gives the monotone optimum. It prints `FOUND` with `op a b` lines (op 0 AND, 1 OR, 2 NOT) or `NONE ... nodes`.
- `repsearch n m <hex relation> <size> <allowNot>` is the same search under `PEqualNP.Represents` semantics. Only inputs with one row and one column on matter, so every wire is a relation on `[n]×[m]` (bit `u*m+v`): row inputs are full rows and column inputs are full columns.
- `run_notsearch.sh` and `run_repsearch.sh` write results to files. Write to files rather than relying on stdout: output through `wsl.exe` sometimes went missing in this round.
- `gen_table5_lean.py gaps.json GAP_ID circuit.txt out.lean` renders a `notsearch` witness as the exact `L-meta-18089`-shaped statement. It proves `FanInTwo` by `simp`, `ReadsBack` by unfolding and `decide`, and the finite rest by `decide`. A test rendering checked in about 12 s with `lake env lean`.

**Completeness.** The search requires every gate to be read later or be the output, and it uses a canonical topological order (each gate reads its predecessor or has a larger `(op, a, b)` key). It removes constant and duplicate wires and uses only AND2, OR2 and NOT1. For plain existence questions none of these restrictions loses a solution. In the NOT-on-gate statements, a NOT's ignored second input counts as "read", so a qualifying NOT can be kept alive as the second input of another NOT. Such a circuit drops to a size-(k−1) circuit containing some NOT. So also run mode `1` at size `k-1` before calling a NOT-on-gate gap empty.

**Timings on 16 threads.** For 5 inputs at size 8: about 13 s and 1.6·10⁹ nodes. Size 9: 450–620 s and 6.0·10¹⁰ nodes. Expect each extra gate to cost about 40× more. Size 10 and above wants a SAT encoding instead.

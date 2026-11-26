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

# Strategy for the `leomarchetti` contribution

[Submission playbook](contributor-playbook.md) · [Round log](contributor-rounds.md) · [Reusable search code](contributor-tools/README.md)

This is a handoff for agents working from the `leomarchetti/pequalnp-proofs` fork. Pick a current gap and deliver one exact Lean file through the project desk. Measure a tactic by time to a checked Lean file, whether the desk still offered the gap, and the eventual upstream verdict. A computational witness, a local Lean pass, an open PR, and a merged proof are distinct milestones.

## Next agent: start here (after the November 26 reduction round)

1. **Restart the workers first.** Everything is in [reduction-pipeline](contributor-tools/reduction-pipeline/); the operating notes are in the tools README.
   - `auto_any.py`: races any newly posted step that fits a generic template.
   - `auto_children.py`: races children we pre-proved.
   - `harvest_loop.py`: pre-proves children of others' open reductions.
   - A verdict poller.
   Run each as a persistent background process writing a log, and only *tail* the logs with monitors: a monitor timeout kills the command it runs.
2. **Do not send more reductions until one of ours lands again.** Since 02:42 on Nov 26 every reduction of ours was "accepted, never merged" (30 open). Reductions also do not count for ranking. Only proofs do.
3. **Proofs come from three places:**
   - children of anyone's merged reductions, via the generic racer;
   - one-off proofs of open steps where we have a real idea;
   - "beat by one" ladders, which still need a stronger search (`pcx`, majority-7).
4. **The race is about 1–2 minutes from posting,** and the snapshot lags up to 100 s for everyone. Our pipeline needs about 15–25 s of local check, then lease, splice, `pnp.sh check` and submit in about 35 s. Never lease with `--proof-of` before a local Lean check has passed.

## What we learned on November 26

- **Race-proof splits beat generic splits, in principle.** An AND-gate split's easy side is proved by anyone in 90 s (the OR-only split argument). A size split's small side, by contrast, needs a connectivity bound: the `DepKit`, adapted from `L_meta_2135`. Willakone's "output is an input wire" split has a trivially vacuous easy side, which they prove themselves before anyone else.
- **Generic templates cover the shapes that recur:**

  | Template | Shape |
  |---|---|
  | T1 / T1b | no-AND (with an iff characterization / with an `∃ x, eval ≠ F` conclusion) |
  | T2 | small size |
  | T3 / T3b | output is an input (same two conclusion forms) |

  Each finds its witnesses with `decide`, so no per-gap data is needed. T3/T3b reproduced three real merged proofs (18759, 18779, 18771).
- **The rest of the recent flow is bespoke.** About 60% of new child steps are structural lemmas over generic n, list or graph arguments, or synthesis claims with wire-value conditions. Templates do not pay there.
- **The checker's `reduce-child` limit:** child statements must print in ≤ 2000 characters. Skip statements over about 1650 characters before splitting.
- **Merge mechanics:** a PR without a checker comment was taken by the desk. An `ACCEPTED` comment means the PR was not taken, and such PRs did not merge in our observations.

## Calibration from upstream merges (November 26, 2026)

- **Freshness beats planning.** Fresh gaps close within tens of minutes. Refresh the snapshot every ~15 minutes, or pull through `tools/pnp.sh next`. A plan built on a one-hour-old snapshot is mostly stale.
- **Do not skip universal statements by reflex.** Contributors close large finite lower bounds with kernel computation (`decide +kernel`, packed `Nat`/`BitVec` banks). Start from the engines in `L_meta_18044` / `L_meta_18169` (BitVec circuit simulation) and `L_meta_17335` (verified exhaustive search) instead of writing semantics lemmas from scratch.
- **Take cut steps seriously.** Reductions are about a quarter of merges.
- **Test a "FIND" gap against its posted floor before searching.** `L-meta-18185` (6×6 crown ≤ 17) contradicts `L-meta-18163` (crown ≥ 3n for n ≥ 5). Families like the 5-input "NOT on a gate" bounds came back empty under exhaustive search, so prefer gaps whose sketch says a witness is held or the bound has slack.
- **Use SAT for exact synthesis beyond ~9 gates.** Enumeration grows about 40× per gate. Ask the owner before installing CaDiCaL.

## Start here

1. Download the current [gap snapshot](https://data.pequalnp.com/data/desk/gaps.json) and record its `updated_at`. Look for newly posted gaps with `pr_open == 0`. Read the entire statement, including its quantifiers, output indices, and whether it asks for a witness or a universal result. The snapshot is for triage. Confirm availability on the live desk and check exact-title PRs before spending time.
2. Give the first agent circuit rewrites with a close existing proof, the second finite graph certificates, and the third a short search for a different family with a concrete reason to expect a witness. Put distinct IDs in a shared candidate list before anyone starts editing. Keep one coordinator for writes to the real proof path and submissions in any shared checkout.
3. Prefer the candidate that can get through Lean and the desk soonest. A three-minute construction with a small Lean file can beat a one-second witness that takes minutes to elaborate. Report a promising result as soon as its exact statement passes, with the file path, elapsed time, and latest desk state.
4. Refresh after a batch or a lost race. Record gap ID, approach, check time, competing PR age, our PR number, and verdict. When using all local cores, keep memory and Lean wall time in view. Start independent searches with bounded worker counts and leave capacity for proof checks.

## What worked

| Family | Method and evidence |
|---|---|
| Structural circuit rewrites | Reuse an existing invariant rather than reprove circuit semantics. For input maps, distinguish input wires from gate-output wires. Push the map through a `foldl` invariant and preserve default reads, gate lengths, and output indices. The map can repeat inputs. `L-meta-17261` and [L-meta-17832](https://github.com/open-goat/pequalnp-proofs/pull/22411) give starting points. For gate extensions, use the wire prefix and list length after each new gate. [L-meta-17904](https://github.com/open-goat/pequalnp-proofs/pull/22450) adds a NOT before the original circuit and an OR afterward. [L-meta-17906](https://github.com/open-goat/pequalnp-proofs/pull/22466) adapts the normalization pass from `L-meta-10057` using two evaluations to show the function is nonconstant. |
| Circuit erasure and simplification | Show a removable gate has no effect on the relevant output or outputs, then map downstream references and prove each retained wire evaluates as before. Start with the merged [L-meta-17663](https://github.com/open-goat/pequalnp-proofs/pull/22339). Test very short input lists and out-of-range reads. A change in input length can turn an old gate index into an input index. This gave a Lean-checked counterexample to `L-meta-17721`. A counterexample can be submitted when the desk lists its exact negated twin. |
| Exact fan-in-two AND/OR circuits | For an appended gate, preserve the read-back condition on old indices via `List.getD_append`. Prove the new index separately using the two input bounds. Split `List.foldl_append` and use the old wire bank’s length to preserve its values. For an OR-only circuit, show by induction that evaluation preserves pointwise OR of two equal-length inputs. A graph incidence function can accept the union of two singleton inputs while rejecting both separately, which contradicts that invariant. [Checked examples](contributor-tools/README.md#structural-circuit-examples) |
| Boolean decompositions and local graph consequences | Simplify the statement before building a solver. [L-meta-17902](https://github.com/open-goat/pequalnp-proofs/pull/22441) is Boolean case analysis. A matching gives every vertex at most one neighbor, which forbids a cycle in [L-meta-17887](https://github.com/open-goat/pequalnp-proofs/pull/22455). For a purported zero-gate circuit, two disjoint positive inputs can rule out every valid input-wire read, and the empty input can then contradict the output. Removing an edge need not lower circuit size. The Lean counterexample for `L-meta-17889` uses `K₂,₂` and the four essential inputs of the resulting path. |
| Finite graph certificates | Represent subsets as integer masks. For a translate family, precompute one output mask per source vertex, OR them over each source subset, and keep one witness per distinct output. Sort outputs and prove strict increase in Lean to get injectivity. [L-meta-17775](https://github.com/open-goat/pequalnp-proofs/pull/22425) selected 16,385 of 25,237 outputs from `2^21` subsets. Search took under a second and the full local Lean check took 49 seconds. Use bounded chunks and prove the ordering across boundaries. For `L-meta-17891`, a local Lean proof enumerated the 2,048 vertex subsets and counted selected vertices plus edges missed by each subset. The desk closed before submission. |
| `mono6-class` | A six-input truth table fits in one `uint64_t`. The preserved C++ search builds a monotone witness and a lower-bound certificate on the number of binary gates in a competing circuit. If the competitor has a NOT, that extra gate pays for the monotone witness at the same budget. Otherwise the competitor already meets `Monotone2`. The Lean generator checks the reachability and truth-table certificates. See the runnable example in [the tooling guide](contributor-tools/README.md). |
| Rectangle covers | Prioritize the existential side of paired gaps. For each possible rectangle, use row and column membership variables. Forbid all wrong-color cells and enforce coverage of every required cell. Sort rectangles lexicographically to reduce symmetry. Replay SAT witnesses by checking that their union is exactly the desired cells and the rectangle count fits. The preserved script does this replay. An UNSAT result needs a separate Lean-checkable proof for a nonexistence gap. |
| Small circuit synthesis | Pack function values by input assignment and search for smaller gates using factored expressions, shared subexpressions, row/column symmetries, and gate deduplication. For six-vertex 3-colorability, factored `K₄` and five-cycle wheel tests gave a 212-gate circuit against a 220-gate cap on `L-meta-17731`. It matched all 32,768 graphs against direct coloring enumeration. The desk closed before submission and the result did not reach Lean. The construction is in [the tooling guide](contributor-tools/README.md). |

## Exploration priorities

- **`direction4-one-not-replace` and nearby families.** Start with the exact truth-table row order and the exact allowed gates. Use two `uint64_t` limbs for 128 rows and four for 256 rows when the data has those widths. Try existing monotone witnesses, duality, restrictions, shared factors, and shallow circuit synthesis. For a universal replacement claim, the witness proves only the upper bound. Look for a gate-count lower bound or a structural replacement theorem first. Treat the 6-input certificate generator as a reference implementation. This branch has no verified general solver for these larger families.
- **Proof complexity.** In the pigeonhole examples, minimize actual resolution lines with explicit parents and pivots. Replay every axiom and inference, then check the empty final clause in Lean. SAT solver trace length and resolution length can differ substantially. The best attempts were 58 lines against 55 for `L-pcx-151`, 157 against 149 for `L-pcx-169`, and 159 against 143 for `L-pcx-135`. The first two constructions passed Lean at their own bounds. Over one million local resynthesis moves failed to improve the 58-line proof. A Res(2) attempt for `L-pcx-189` stayed at the 55-line seed against a target of 50. Spend a short budget on fresh statements with slack or a specific stronger inference.
- **Harder constructive targets.** Try longer work on one gap only after a concrete invariant, a close numeric witness, or a reduction that removes a substantial part of the difficulty. Use independent scoring for search progress, such as best verified gate count or Lean certificate size. Reconsider when that score stops moving and compare expected time to a fresh easier gap.
- **Algebra and larger graph circuits.** Use bit-packed small graphs, canonicalized gate DAGs, or polynomial equality by coefficient maps to screen candidates. Past exploratory work included matrix expressions, Hamiltonicity, and the Petersen graph. Promote a result to the active lane once there is a concrete certificate and a checker plan.

## Keep the next handoff current

Update the [round log](contributor-rounds.md) at the end of each round and revise the strategy when a new lemma shape, checker issue, or search tool changes the next agent’s first move. Store source and tiny reproducible inputs here. Use upstream PR links for exact submitted proof files and label local results accordingly. Keep lease JSON, credentials, build outputs, and bulk desk snapshots out of Git.

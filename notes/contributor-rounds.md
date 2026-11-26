# Contribution round log

[Strategy](contributor-strategy.md) · [Submission playbook](contributor-playbook.md)

The statuses are observations from the latest round. Use GitHub and the official desk for live state. A fork branch can exist without an upstream PR.

## Round on November 26, 2026, 02:20–05:05 UTC (reductions, child races, generic provers)

**Score: 7 PRs merged (6 reductions + 1 proof).** Only the proof counts for ranking, since reductions just create raceable children. 50 PRs opened in total; the final states as of 05:03 UTC are below.

| Outcome | PRs |
|---|---|
| **Merged (7)** | Reductions (AND-gate split, no-AND side proved in advance): [17138 #22884](https://github.com/open-goat/pequalnp-proofs/pull/22884), [5995 #22896](https://github.com/open-goat/pequalnp-proofs/pull/22896), [17856 #22913](https://github.com/open-goat/pequalnp-proofs/pull/22913), [18378 #22961](https://github.com/open-goat/pequalnp-proofs/pull/22961), [8468 #22962](https://github.com/open-goat/pequalnp-proofs/pull/22962), [8494 #22963](https://github.com/open-goat/pequalnp-proofs/pull/22963). Proof: **[L-meta-18453 #22955](https://github.com/open-goat/pequalnp-proofs/pull/22955)**, the no-AND child of our 17856 reduction, first in line. |
| **Lost child races (3)** | 18407, 18425, 18490: a competitor merged first. 18477 and 18481 were never sent, because of auto-submitter bugs (all fixed, see below). |
| **Accepted, never merged (30 open)** | Every reduction we opened after 02:42 got an `ACCEPTED` checker comment and stayed open. That's 17 AND-splits and 11 size-splits, plus 18266 and 17848. A lone byte-identical resubmission ([#23298](https://github.com/open-goat/pequalnp-proofs/pull/23298), 17361) also did not merge after 18+ minutes. |
| **Rejected (4, closed)** | 18207, 18276, 18057, 18467: `reduce-child`, a child hypothesis prints over 2000 characters. Statements near 1900 characters cannot be split. |
| **Closed by us (4)** | 8897 (another reduction had already landed); 17361 (closed to resubmit as #23298); 17977 and 18475 (closed when we misread willakone's same-titled PRs as proofs; they were reductions, so this was our error). |

**What we learned about the desk:**
- **The merge path is one-shot.** Reductions the desk intake takes are merged 6–60 minutes after opening with **no checker comment**. PRs it does not take get `ACCEPTED` from the GitHub Actions checker about an hour later and then **stay open indefinitely**, for every author (lokyll-social has one 3+ hours old). Treat `ACCEPTED` as "not taken", not as a step towards merging.
- **What we ruled out.** No documented per-author cap fits, nor any lease, title or body rule, nor "an author's earlier reductions must clear first" (both our timeline and lokyll's contradict it). Something per-author excluded ours after our 6th: possibly volume (about 35 reductions in bursts) or the ratio of reductions to merged proofs. Unresolved.
- **The checker queue reached about 65 minutes at peak.** The PR-to-merge median for proofs is 7.6 minutes.
- **Reduction children are raced within 1–2 minutes of posting.** The public snapshot regenerates only every 75–100 s for everyone, so speed is decided by our own pipeline.

**Independent tracks:**
- **Exact search on CaDiCaL** (installed in WSL with owner approval). Majority-7 at ≤19/≤18 gates: no answer in 50–90 minutes, and the 21-gate calibration run did not reproduce the desk's known circuit either, so the encoding is too weak. Circulant {0,1,3} (17166) is UNSAT at 8 and 9 gates. The 4×4 crown is UNSAT at 9, so it needs ≥10 gates and 17394 cannot come from 2·crown+1. All SAT jobs were stopped after the machine crash.
- **`pcx` short refutations (subagent).** None found: PHP(4,3) stays at 58 lines against the 55 target. The SAT encoder and Lean emitter work; see [pcx-sat](contributor-tools/pcx-sat/). A hand line-count suggests 55 needs a structure other than the "hole is full" lemma scheme.
- **Bulk `decide`/`simp` triage** of 245 finite gaps: 0 hits in about 170 attempts. Stopped as the lowest-yield lane.

**Incidents.**
- **The PC crashed** (bugcheck 0x154 UNEXPECTED_STORE_EXCEPTION) under heavy load: up to 16 SAT solvers plus several Lean processes. No files were lost. Since then the workers run as persistent processes, monitors only tail their logs, and done-state is persisted.
- **Auto-submitter bugs, each found by a lost race or by an end-to-end test:**
  - Python's `bash` resolved to WSL's bash;
  - a doubled `L_` path prefix;
  - the race check misread "no PR" (`null null`);
  - the splicer anchored on the first `theorem` and dropped all but one `set_option`;
  - monitor timeouts killed the workers themselves.

## Solo round on November 25–26, 2026 (exact search; no upstream PR)

No upstream PR. Every constructive bound tested exhaustively turned out empty, and the gaps that were provable went to faster contributors. The search tools below are new and reusable. See [the tooling guide](contributor-tools/README.md#exact-small-circuit-search-round-of-november-2526-2026).

| Gap | What was established | Desk / PR outcome |
|---|---|---|
| `L-meta-18094` (5-input `Th2(x0,x1,x2,x3∨x4)`, size ≤ 9 with a NOT reading a gate) | `notsearch`, exhaustive at size 9 (6.0·10¹⁰ nodes, 447 s): **NONE**. Sizes 5–8 also NONE. Mode 1 (any NOT) at sizes 5–8: NONE. That covers the NOT kept alive only as another NOT's ignored second input. Monotone optimum confirmed at 8 (7: NONE). | Statement appears **false**. No Lean refutation: a verified search engine is needed (see `L-meta-17335` below). |
| `L-meta-18093`, `L-meta-18092` (same family, size 9) | Mode 0 at size 9: **NONE** for both. | Appear false. Mode-1 size-8 check not run for these two. |
| `L-meta-18089`–`18091`, `18095`–`18098` | Not run: stopped to free cores. Expect the same outcome (size 10–11 needs SAT). | — |
| `L-meta-16081` (5-input monotone `0xeae8e880`, ≤ 9) | Mode 2 at sizes 7, 8, 9: **NONE** (2.3·10¹⁰ nodes at 9). | Appears false. |
| `L-meta-18079` (monotone ≤ 43 for the {0,1,3,9} mod 13 difference-set graph on 21 inputs) | Python check: 36 edges, C4-free, maximum matching 9. The posted `L-meta-18023` claim implies size ≥ edges + vertex cover − 1 = 44. The star construction gives exactly 44. | Likely false; it depends on `18023`. |
| `L-meta-11867` / `11869` (8×8 `IP3 ⊕ u0u1`, represented in ≤ 20 or ≥ 21) | Best hand construction is 29. The trivial floor is 14. The ≥ 21 side looks likelier. | Not attempted in Lean. |
| `L-meta-17394` (two 4×4 crowns, ≤ 20) | Sub-additivity: size ≤ 2·crown4 + 1. `repsearch` crown4: 7 NONE; size 8 see below. The desk floor `3n−3` and "5×5 crown = 15" suggest crown4 ≥ 10, which would make this a direct-sum question. | Open. |
| `L-meta-17166` (5×5 circulant {0,1,3}, ≤ 10 with NOT) | `repsearch` with NOT at size 7: NONE (2.2·10¹⁰ nodes). Sizes 8–10 too slow for enumeration. | Open; needs SAT. |
| `L-meta-5968` (TopForm cut step from `next --level solid`) | Released as `other` right away: a long structural statement with no sketch, outside this round's tools. | Released. |

**Environment.** WSL Ubuntu has `g++`, OpenMP and 16 cores. There is no SAT solver on the machine. A CaDiCaL build was blocked pending explicit owner approval, so ask before installing one. Lean stays on Windows.

**What recent merges show (≈200 PRs, 00:00–01:36 UTC on Nov 26).** About 26% are reductions. Fresh 18xxx gaps are proved roughly 10–40 minutes after posting, often as 300–7,000-line kernel-checked files using `decide +kernel` over packed `Nat`/`BitVec` data. Two engines on main to reuse:
- **`L_meta_18044` / `L_meta_18169`**: whole truth tables as `BitVec`, checking a 110-gate circuit over 32,768 rows in the kernel.
- **`L_meta_17335`** (adapted from `L_meta_1673`): a kernel-verified exhaustive search proving "≥ 16 gates". Its certificate tables (`w*_*`, `rawP`, `gtypes`) are specific to one case, so a sibling case (`17325`, `17343`, `17355`, all open) needs regenerated tables, not a parameter swap.

| Gap | Result | Desk outcome |
|---|---|---|
| `L-meta-17962` | [Lean checked](contributor-tools/examples/checked-17962.lean) that adding an AND gate preserves `IsAO2`, distinct operands and existing wire values. | Already `pr_open`. |
| `L-meta-17958` | [Lean checked](contributor-tools/examples/checked-17958.lean) the existential variant with the appended gate as output. | Already `pr_open`. |
| `L-meta-17979` | [Lean and official local build passed](contributor-tools/examples/checked-17979.lean). Pointwise OR splits an accepting input into a singleton accepted by the same circuit, contradicting the incidence specification. | Lease and check succeeded. The first competing PR was 86 seconds old at the last GitHub preflight. The final desk check stopped `submit` after the fork push. No upstream PR was opened and the lease was released. |

The shared AND construction covered two gaps. For similar OR-only cases, screen for two rejecting inputs whose union is accepted before proving any gate-count bound. The desk state changed faster than the proof workflow on these three attempts.

## Previous parallel rounds

- **Merged** — [L-meta-17775](https://github.com/open-goat/pequalnp-proofs/pull/22425) on distinct unions of translates, [L-meta-17904](https://github.com/open-goat/pequalnp-proofs/pull/22450) on circuit extension, [L-meta-17887](https://github.com/open-goat/pequalnp-proofs/pull/22455) on acyclicity of a bipartite matching, and [L-meta-17926](https://github.com/open-goat/pequalnp-proofs/pull/22482) on incidence monotonicity.
- **Closed without merging our PR** — [L-meta-17832](https://github.com/open-goat/pequalnp-proofs/pull/22411) on input reindexing, [L-meta-17902](https://github.com/open-goat/pequalnp-proofs/pull/22441) on Boolean decomposition, and [L-meta-17906](https://github.com/open-goat/pequalnp-proofs/pull/22466) on circuit normalization.

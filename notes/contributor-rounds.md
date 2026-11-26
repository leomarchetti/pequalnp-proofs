# Contribution round log

[Strategy](contributor-strategy.md) · [Submission playbook](contributor-playbook.md)

The statuses are observations from the latest round. Use GitHub and the official desk for live state. A fork branch can exist without an upstream PR.

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

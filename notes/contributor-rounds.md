# Contribution round log

[Strategy](contributor-strategy.md) · [Submission playbook](contributor-playbook.md)

The statuses are observations from the latest round. Use GitHub and the official desk for live state. A fork branch can exist without an upstream PR.

## Solo round on November 25, 2026

| Gap | Result | Desk outcome |
|---|---|---|
| `L-meta-17962` | [Lean checked](contributor-tools/examples/checked-17962.lean) that adding an AND gate preserves `IsAO2`, distinct operands and existing wire values. | Already `pr_open`. |
| `L-meta-17958` | [Lean checked](contributor-tools/examples/checked-17958.lean) the existential variant with the appended gate as output. | Already `pr_open`. |
| `L-meta-17979` | [Lean and official local build passed](contributor-tools/examples/checked-17979.lean). Pointwise OR splits an accepting input into a singleton accepted by the same circuit, contradicting the incidence specification. | Lease and check succeeded. The first competing PR was 86 seconds old at the last GitHub preflight. The final desk check stopped `submit` after the fork push. No upstream PR was opened and the lease was released. |

The shared AND construction covered two gaps. For similar OR-only cases, screen for two rejecting inputs whose union is accepted before proving any gate-count bound. The desk state changed faster than the proof workflow on these three attempts.

## Previous parallel rounds

- **Merged** — [L-meta-17775](https://github.com/open-goat/pequalnp-proofs/pull/22425) on distinct unions of translates, [L-meta-17904](https://github.com/open-goat/pequalnp-proofs/pull/22450) on circuit extension, [L-meta-17887](https://github.com/open-goat/pequalnp-proofs/pull/22455) on acyclicity of a bipartite matching, and [L-meta-17926](https://github.com/open-goat/pequalnp-proofs/pull/22482) on incidence monotonicity.
- **Closed without merging our PR** — [L-meta-17832](https://github.com/open-goat/pequalnp-proofs/pull/22411) on input reindexing, [L-meta-17902](https://github.com/open-goat/pequalnp-proofs/pull/22441) on Boolean decomposition, and [L-meta-17906](https://github.com/open-goat/pequalnp-proofs/pull/22466) on circuit normalization.

# Contributor playbook

[Strategy and results](contributor-strategy.md) · [Reusable search code](contributor-tools/README.md)

Use this branch as a reference from the fork. Start proof work on a clean checkout or worktree of current `upstream/main`. `origin` should point to the contributor’s fork, and `upstream` to `open-goat/pequalnp-proofs`. Use the repository’s [contribution rules](../CONTRIBUTING.md), [desk guide](https://pequalnp.com/join.txt), and current [`tools/pnp.sh`](../tools/pnp.sh) for the protocol. The playbook records what worked on this fork.

From a proof checkout in the fork, read the handoff without switching branches.

```bash
git fetch origin codex/contributor-playbook
git show FETCH_HEAD:notes/contributor-strategy.md
git show FETCH_HEAD:notes/contributor-playbook.md
```

## Setup and discovery

- Set up Git, GitHub CLI, Python 3, curl, Bash, and the pinned Lean toolchain. Run `bash tools/pnp.sh setup` from the proof checkout. On Windows, use Git Bash or WSL with the dependencies visible from that shell. Run `gh auth status` to check the account. Keep any local shims outside proof files and versioned docs.
- Pull the [public gap snapshot](https://data.pequalnp.com/data/desk/gaps.json). Some releases have family data in `faithful_by_template.template`. When it is absent, classify from the exact statement. For a specific ID, the live endpoint is `https://pequalnp.com/desk/step?gap=L-meta-17902`, replacing the example ID. Use a few seconds between desk requests. A lease can coexist with another contributor’s lease if the desk offers a race.
- Use `gh pr list -R open-goat/pequalnp-proofs --state all --search 'L-meta-17902 in:title' --json number,title,state,createdAt`. Filter by exact title and sort `createdAt` in UTC. Per the contributor’s five-minute rule, continue with a checked proof when the earliest competing exact-title PR is at most 300 seconds old **and** the desk still permits the submission. A merged proof or a desk refusal ends that attempt. Recheck before `submit`. A public activity page can lag GitHub or the live desk.

## Prove, reserve, check, submit

1. For a likely quick proof, prepare a scratch file with the snapshot’s exact statement and run `lake env lean path/to/file.lean` from `lean/`. Use `bash tools/pnp.sh next --proof-of <id>` once the proof checks. For work selected by the desk, use ordinary `next` and follow its lease instructions from the start.
2. Use the desk-generated skeleton as the authority for the file, final theorem name, and statement. Keep the exact header, including parentheses and the statement text. Place helper definitions and lemmas in the named namespace, close it, and leave the one fully qualified outside theorem last. Use UTF-8 and LF. Normally import the listed project definitions and only the Mathlib modules needed. Check `CONTRIBUTING.md` for the current limits and accepted proof syntax.
3. Put the checked proof in the skeleton’s file and run `bash tools/pnp.sh check <id>`. This checks the format and builds the exact project module. A scratch `lake env lean` pass alone does not establish either that the leased proposition matches or that the file is eligible for the upstream checker.
4. Follow the lease renewal interval from the desk. The current guide says `bash tools/pnp.sh beat <id>` every five minutes. If any desk call tells you to stop, stop that attempt. For unfinished work, preserve the draft outside the proof path and release the lease with the reason supported by the desk. If you see an unexpected existing proof file, inspect Git state and check whether upstream settled the gap before touching it.
5. Check the race rule again, then run `bash tools/pnp.sh submit <id>`. Let the script create the branch and PR. Inspect the result with `gh pr view <number> -R open-goat/pequalnp-proofs --json title,state,mergedAt,files`. There should be exactly one new Lean file. Keep docs, tests, and solver sources on the fork’s reference branch. Return the proof checkout to clean upstream state before the next submission.
6. Track the verdict through the PR comments and state. The upstream checker can accept, reject, or fault. Record an accepted proof as merged once GitHub shows the merge. If a competitor’s proof is accepted first, log the race outcome even if our local Lean check passed.

## Practical patterns

- In a parallel round, have agents write in distinct scratch directories. Tell the coordinator the ID immediately, then send the exact path, Lean exit status, and one sentence explaining the method. Keep submissions serialized in a single checkout, since `submit` changes Git branches.
- Run C++ for exhaustive search over many states and Python for orchestration, parsing, truth-table operations with large integers, and certificate generation. Benchmark the entire path. In several small finite searches, Lean dominated wall time. Cap expensive jobs and keep at least one Lean check progressing.
- Use explicit witnesses and independently replay them before rendering Lean. Chunk large lists for kernel checks, prove facts about each chunk and combine them with ordinary lemmas. Use kernel checking where suitable, subject to the current guard. Keep the final proof within the project’s size and resource limits.
- For unexpectedly false statements, try a tiny Lean counterexample first. Inspect the desk’s exact refutation twin before writing a submission. Keep a local counterexample in the research record when no twin is offered.
- The five-minute cutoff is a contributor preference. The desk and the upstream checker determine eligibility and acceptance.

# Small "Represents" FIND steps (Nov 26 round)

The desk posts batches of tiny calibration steps:

    ∃ C, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin 4 => (MASK : ℕ).testBit (4 * u.val + v.val)) C

(an AND/OR/NOT circuit on the one-vertex-a-side promise, s between 1 and 9). They are worth weight
100 each and the compact encoder `../synth_sat3.py` settles each in under a second:

    python3 synth_sat3.py 8 rel:4:<hex mask> <s> 1 cadical cnf44

On Nov 26: 55 such steps, 40 had a circuit at the bound, 15 were UNSAT at the bound (those are the
desk's "one below the AND/OR cost" rows where NOT does not help).

## Pipeline

- `mk_rep.py NUM witness.txt skeleton.lean`: exhaustive Python check of the gate list on all 16
  promise inputs, then splices a `Helpers.witness` definition and the proof
  `refine ⟨witness, ?_, by decide, by decide⟩; simp [FanInTwo, witness]` into the desk skeleton.
  The desk skeleton wraps the statement in parentheses: always splice into the skeleton, do not
  write your own theorem header.
- Local Lean check first (one combined file for a batch loads Mathlib once), only then
  `pnp.sh next --proof-of`.
- `batch_go.sh ids.txt`: lease, splice, desk check (4 at once), then submit serially.
- `rep_worker.py`: persistent version (polls the snapshot, SAT, local check, lease, check, submit);
  a step another agent holds is retried after "Bring your proof back after T".

## Lessons

- New steps are handed to agents at once with a ~30 minute head start ("Another agent was handed
  this step ... Bring your proof back after ..."). Holders prove most of them inside that window.
- The desk PAUSED this handle for an hour after a burst of ~40 leases / 21 submits plus two re-sends
  to steps that had answered "not open": "its agent sent the same proof again and again". Rules now
  in `../../reduction-pipeline/fastsubmit.sh`: never resend to a closed step (`.pnp/closed_steps.txt`),
  at least 45 s between submits; on a 429 stop every desk-calling worker until the stated time
  (`resume.sh` probes once, waits `retry_after_s`, then restarts the workers).
- A stray untracked file in the repo root makes `pnp.sh submit` refuse silently.

## L-meta-19147 (general theorem, weight 120)

XOR of two represented graphs costs at most s + t + 4 gates: `L_meta_19147.lean` builds A's gates,
then B's gates with wire indices moved past A's (`shiftIdx`, as in the library's
`RRDistinguisher.fold_shift`), then `p = a OR b, q = a AND b, r = NOT q, out = p AND r`, with a
missing output wire replaced by an index past the end. Compiles locally with no sorry.

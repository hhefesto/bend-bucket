# bucket: token buckets (the rule of backend/src/Limit.hs)

**What it means.** A bucket's level is a behavior of time:
level(now) = min(size*period, left + (now - at)), in whole milliseconds (a
try is `period` of them), so the arithmetic is Nat's and exact. A try by a
key at `now` is let through iff its bucket and the shared one each hold a
try, and then takes one from each; refused, it changes nothing and says how
long to wait. A key with no bucket has a full one; full buckets are
forgotten. `bk.rules()` are Limit.hs's: 5 tries then one each 12 s per
visitor, 20 then one each 3 s for all together.

**Laws** (LAWS.bend, proved in PROOF.bend, `--verdict` too):
`refused_keeps` (Limits.hs's prop_refusedKeeps), `admitted_all`,
`admitted_mine` (a try let through leaves each bucket one try below its
level then), `level_le_cap` (a level never passes its size), `level_mono`
(waiting never lowers a level), `burst` (prop_burst: 5 of 7 at one
instant), `together` (prop_together: 20 of 22). burst and together are
proved with Limit's sizes and a 1 ms period (at one instant nothing
refills; the kernel counts in unary); probe/Bucket.bend runs them with
Limit's own periods: 5 and 20.

Mutants (`../mutants.sh bucket`): 7, each caught.

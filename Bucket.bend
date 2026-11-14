import Base

# Bucket: token buckets, the rule Limit.hs keeps sign-in tries with.
#
# What it means: a bucket's level is a behavior of time: the tries it holds
# at `now` are what it had when last set, plus the refill since, up to its
# size: level(now) = min(cap, left + (now - at)). A try at `now` by a key
# is let through iff its own bucket and the shared one each hold a try, and
# then takes one from each; refused, it changes nothing and says how long
# to wait. A key with no bucket has a full one; buckets that have filled up
# again are forgotten.
#
# Everything is in whole milliseconds, a try being `period` of them (a rule
# of 5 tries, one each 12 s, is size 5, period 12000): so the arithmetic is
# Nat's, exact, and the laws (LAWS.bend) are proved, not sampled.
#
# Every def is prefixed `bk.` (a program's defs share one namespace).

# a rule: `size` tries at once, one more each `period` ms
type bk.Rule is Data:
  bk.Rule{size: Nat, period: Nat}

# a visitor's rule and the one for all visitors together
type bk.Rules is Data:
  bk.Rules{one: bk.Rule, all: bk.Rule}

# a bucket: what it held (ms of refill) when it was last set, and when (ms)
type bk.B is Data:
  bk.B{left: Nat, at: Nat}

# a key's bucket
type bk.KB is Data:
  bk.KB{k: String, b: bk.B}

# the shared bucket, and the keys'
type bk.Bs is Data:
  bk.Bs{all: bk.B, each: List<&2, bk.KB>}

type bk.Verdict is Data:
  bk.Admitted{}
  bk.Wait{ms: Nat}

type bk.R is Data:
  bk.R{v: bk.Verdict, bs: bk.Bs}

def bk.cap(r: bk.Rule) -> Nat:
  match r:
    case bk.Rule{s, p}:
      Nat.mul(s, p)

def bk.period(r: bk.Rule) -> Nat:
  match r:
    case bk.Rule{s, p}:
      p

# A bucket's tries at now (in ms of refill)
def bk.level(r: bk.Rule, +now: Nat, b: bk.B) -> Nat:
  match b:
    case bk.B{l, a}:
      Nat.min(bk.cap(r), Nat.add(l, Nat.sub(now, a)))

def bk.find.at(hit: Bool, +b: bk.B, more: Unit -> Maybe<&2, bk.B>) -> Maybe<&2, bk.B>:
  match hit:
    case True{}:
      Some{b}
    case False{}:
      more(Unit{})

# a key's bucket, if it has one
def bk.find(es: List<&2, bk.KB>, +k: String) -> Maybe<&2, bk.B>:
  match es:
    case Nil{}:
      None{}
    case Con{bk.KB{+k2, +b}, t}:
      bk.find.at(String.eq(k2, k), b, u => bk.find(t, k))

# a key's tries at now: its bucket's level, or a full one's
def bk.mine(r: bk.Rule, +now: Nat, m: Maybe<&2, bk.B>) -> Nat:
  match m:
    case None{}:
      bk.cap(r)
    case Some{b}:
      bk.level(r, now, b)

def bk.keep(full: Bool, e: bk.KB, rest: List<&2, bk.KB>) -> List<&2, bk.KB>:
  match full:
    case True{}:
      rest
    case False{}:
      e <> rest

# the keys whose buckets have not filled up again (a full one is what a new
# key gets: forgotten)
def bk.unfilled(+r: bk.Rule, +now: Nat, es: List<&2, bk.KB>) -> List<&2, bk.KB>:
  match es:
    case Nil{}:
      []
    case Con{bk.KB{+k, +b}, t}:
      bk.keep(Nat.is_ge(bk.level(r, now, b), bk.cap(r)), bk.KB{k, b}, bk.unfilled(r, now, t))

def bk.need(r: bk.Rule, +l: Nat) -> Nat:
  Nat.sub(bk.period(r), l)

# whether a try by k at now is let through: its bucket and the shared one
# each hold a try
def bk.ok(rs: bk.Rules, +now: Nat, +k: String, bs: bk.Bs) -> Bool:
  match rs bs:
    case bk.Rules{+one, +all} bk.Bs{a, es}:
      Nat.is_ge(bk.mine(one, now, bk.find(es, k)), bk.period(one)) && Nat.is_ge(bk.level(all, now, a), bk.period(all))

def bk.drop(es: List<&2, bk.KB>, +k: String) -> List<&2, bk.KB>:
  match es:
    case Nil{}:
      []
    case Con{bk.KB{+k2, +b}, t}:
      bk.keep(String.eq(k2, k), bk.KB{k2, b}, bk.drop(t, k))

def bk.taken(+rs: bk.Rules, +now: Nat, +k: String, bs: bk.Bs) -> bk.Bs:
  match rs bs:
    case bk.Rules{+one, +all} bk.Bs{+a, +es}:
      bk.Bs{bk.B{Nat.sub(bk.level(all, now, a), bk.period(all)), now},
        bk.KB{k, bk.B{Nat.sub(bk.mine(one, now, bk.find(es, k)), bk.period(one)), now}} <> bk.unfilled(one, now, bk.drop(es, k))}

def bk.wait(+rs: bk.Rules, +now: Nat, +k: String, bs: bk.Bs) -> Nat:
  match rs bs:
    case bk.Rules{+one, +all} bk.Bs{a, es}:
      Nat.max(bk.need(one, bk.mine(one, now, bk.find(es, k))), bk.need(all, bk.level(all, now, a)))

def bk.admit.at(ok: Bool, +rs: bk.Rules, +now: Nat, +k: String, +bs: bk.Bs) -> bk.R:
  match ok:
    case True{}:
      bk.R{bk.Admitted{}, bk.taken(rs, now, k, bs)}
    case False{}:
      bk.R{bk.Wait{bk.wait(rs, now, k, bs)}, bs}

# A try by k at now: let through (the buckets after it), or how long to wait
# (the buckets as they were)
def bk.admit(+rs: bk.Rules, +now: Nat, +k: String, +bs: bk.Bs) -> bk.R:
  bk.admit.at(bk.ok(rs, now, k, bs), rs, now, k, bs)

# every bucket full, at now
def bk.full(rs: bk.Rules, +now: Nat) -> bk.Bs:
  match rs:
    case bk.Rules{one, all}:
      bk.Bs{bk.B{bk.cap(all), now}, []}

def bk.bs.of(r: bk.R) -> bk.Bs:
  match r:
    case bk.R{v, bs}:
      bs

def bk.v.of(r: bk.R) -> bk.Verdict:
  match r:
    case bk.R{v, bs}:
      v

def bk.all.of(bs: bk.Bs) -> bk.B:
  match bs:
    case bk.Bs{a, es}:
      a

def bk.each.of(bs: bk.Bs) -> List<&2, bk.KB>:
  match bs:
    case bk.Bs{a, es}:
      es

def bk.count.at(r: bk.R, +n: Nat, more: Nat -> bk.Bs -> Nat) -> Nat:
  match r:
    case bk.R{bk.Admitted{}, bs}:
      more(1n+n, bs)
    case bk.R{bk.Wait{w}, bs}:
      more(n, bs)

# Tries one after another, all at time t: how many were let through
def bk.count(+rs: bk.Rules, ks: List<&2, String>, +t: Nat, +n: Nat, bs: bk.Bs) -> Nat:
  match ks:
    case Nil{}:
      n
    case Con{+k, rest}:
      bk.count.at(bk.admit(rs, t, k, bs), n, r => b => bk.count(rs, rest, t, r, b))

# Limit.hs's rules: 5 tries at once per visitor, then one each 12 s; 20 at
# once for all together, then one each 3 s
def bk.rules() -> bk.Rules:
  bk.Rules{bk.Rule{5n, 12000n}, bk.Rule{20n, 3000n}}

# the same sizes, a try a millisecond: what one instant sees of them (at
# one instant nothing refills, so the period plays no part; the kernel
# that rechecks proofs counts in unary, and 60000 is a long count)
def bk.rules.instant() -> bk.Rules:
  bk.Rules{bk.Rule{5n, 1n}, bk.Rule{20n, 1n}}

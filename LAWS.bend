# Bucket's laws: Limit.hs's QuickCheck properties (backend/test/Limits.hs),
# and the README's, as claims about every rule, time and bucket.

import Base
import ./Bucket.bend as B

# prop_refusedKeeps: a refused try changes nothing
law refused_keeps:
  for one: B.bk.Rule
  for all: B.bk.Rule
  for +now: Nat
  for +k: String
  for a: B.bk.B
  for es: List<&2, B.bk.KB>
  for no: {B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}) == False{} : Bool}
  {B.bk.bs.of(B.bk.admit(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es})) == B.bk.Bs{a, es} : B.bk.Bs}

# a try let through leaves the shared bucket one try less than its level
# then, from now on
law admitted_all:
  for +one: B.bk.Rule
  for +all: B.bk.Rule
  for +now: Nat
  for +k: String
  for +a: B.bk.B
  for +es: List<&2, B.bk.KB>
  for yes: {B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}) == True{} : Bool}
  {B.bk.all.of(B.bk.bs.of(B.bk.admit(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es})))
     == B.bk.B{Nat.sub(B.bk.level(all, now, a), B.bk.period(all)), now} : B.bk.B}

# and the visitor's own bucket one try less than its level then
law admitted_mine:
  for +one: B.bk.Rule
  for +all: B.bk.Rule
  for +now: Nat
  for +k: String
  for +a: B.bk.B
  for +es: List<&2, B.bk.KB>
  for yes: {B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}) == True{} : Bool}
  {B.bk.find(B.bk.each.of(B.bk.bs.of(B.bk.admit(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}))), k)
     == Some{B.bk.B{Nat.sub(B.bk.mine(one, now, B.bk.find(es, k)), B.bk.period(one)), now}} : Maybe<&2, B.bk.B>}

# a level never passes its rule's size
law level_le_cap:
  for +r: B.bk.Rule
  for +now: Nat
  for l: Nat
  for at: Nat
  {Nat.is_le(B.bk.level(r, now, B.bk.B{l, at}), B.bk.cap(r)) == True{} : Bool}

# waiting never lowers a level
law level_mono:
  for +r: B.bk.Rule
  for +l: Nat
  for +at: Nat
  for +t1: Nat
  for +t2: Nat
  for h: {Nat.is_le(t1, t2) == True{} : Bool}
  {Nat.is_le(B.bk.level(r, t1, B.bk.B{l, at}), B.bk.level(r, t2, B.bk.B{l, at})) == True{} : Bool}

# prop_burst: one visitor gets 5 tries at once, and no more (Limit's sizes;
# probe/Bucket.bend counts the same with its periods too)
law burst:
  {B.bk.count(B.bk.rules.instant(), ["v", "v", "v", "v", "v", "v", "v"], 0n, 0n, B.bk.full(B.bk.rules.instant(), 0n)) == 5n : Nat}

# prop_together: many visitors together get 20 at once, and no more
law together:
  {B.bk.count(B.bk.rules.instant(), ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v"], 0n, 0n,
     B.bk.full(B.bk.rules.instant(), 0n)) == 20n : Nat}

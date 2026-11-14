# The proofs of LAWS.bend. Nothing here is trusted: `bend PROOF.bend`
# checks every def, `--verdict` rechecks them with BendTT's kernel.

import Base
import ./Bucket.bend as B
import ./LAWS.bend as Laws

# Equality of strings is reflexive, from the bits up
law bool_cmp_refl:
  for b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}

def bool_cmp_refl(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law word_cmp_refl:
  for +n: Nat
  for a: Word(n)
  {Word.cmp(n, a, a) == EQ{} : Cmp}

def word_cmp_refl(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{+ab, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, word_cmp_refl(p, at)) : {Word.cmp.fin(ab, ab, _) == EQ{} : Cmp}
          bool_cmp_refl(ab)

law u32_cmp_refl:
  for x: U32
  {U32.cmp(x, x) == EQ{} : Cmp}

def u32_cmp_refl(x):
  match x:
    case U32{+w}:
      word_cmp_refl(32n, w)

law order_refl:
  for s: String
  {String.order.go(s, s, EQ{}) == EQ{} : Cmp}

def order_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_cmp_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
      order_refl(t)

law string_eq_refl:
  for s: String
  {String.eq(s, s) == True{} : Bool}

def string_eq_refl(s):
  %Equal.sym(Cmp, String.order.go(s, s, EQ{}), EQ{}, order_refl(s)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# A clash of truth values proves anything
def disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

law ft:
  for h: {False{} == True{} : Bool}
  Empty

def ft(h):
  %h : disc(_)
  Unit{}

# Order on Nat
law le_zero:
  for y: Nat
  {Nat.is_le(0n, y) == True{} : Bool}

def le_zero(y):
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

law min_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}

def min_le(a, b):
  match a b:
    case 0n x:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le(p, q)

law sub_mono:
  for +t1: Nat
  for +t2: Nat
  for +a: Nat
  for h: {Nat.is_le(t1, t2) == True{} : Bool}
  {Nat.is_le(Nat.sub(t1, a), Nat.sub(t2, a)) == True{} : Bool}

def sub_mono(t1, t2, a, h):
  match t1 t2 a:
    case 0n y z:
      le_zero(Nat.sub(y, z))
    case 1n+p 0n z:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, z), Nat.sub(0n, z)) == True{} : Bool}, ft(h))
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      sub_mono(p, q, r, h)

law add_mono:
  for +l: Nat
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.is_le(Nat.add(l, x), Nat.add(l, y)) == True{} : Bool}

def add_mono(l, x, y, h):
  match l:
    case 0n:
      h
    case 1n+p:
      add_mono(p, x, y, h)

law min_mono:
  for +c: Nat
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.is_le(Nat.min(c, x), Nat.min(c, y)) == True{} : Bool}

def min_mono(c, x, y, h):
  match c x y:
    case 0n a b:
      {==}
    case 1n+p 0n b:
      le_zero(Nat.min(1n+p, b))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(Nat.min(1n+p, 1n+q), Nat.min(1n+p, 0n)) == True{} : Bool}, ft(h))
    case 1n+p 1n+q 1n+r:
      min_mono(p, q, r, h)

# The laws
def Laws.refused_keeps(one, all, now, k, a, es, no):
  %Equal.sym(Bool, B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}), False{}, no)
    : {B.bk.bs.of(B.bk.admit.at(_, B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es})) == B.bk.Bs{a, es} : B.bk.Bs}
  {==}

def Laws.admitted_all(one, all, now, k, a, es, yes):
  %Equal.sym(Bool, B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}), True{}, yes)
    : {B.bk.all.of(B.bk.bs.of(B.bk.admit.at(_, B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es})))
         == B.bk.B{Nat.sub(B.bk.level(all, now, a), B.bk.period(all)), now} : B.bk.B}
  {==}

def Laws.admitted_mine(one, all, now, k, a, es, yes):
  %Equal.sym(Bool, B.bk.ok(B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}), True{}, yes)
    : {B.bk.find(B.bk.each.of(B.bk.bs.of(B.bk.admit.at(_, B.bk.Rules{one, all}, now, k, B.bk.Bs{a, es}))), k)
         == Some{B.bk.B{Nat.sub(B.bk.mine(one, now, B.bk.find(es, k)), B.bk.period(one)), now}} : Maybe<&2, B.bk.B>}
  %Equal.sym(Bool, String.eq(k, k), True{}, string_eq_refl(k))
    : {B.bk.find.at(_, B.bk.B{Nat.sub(B.bk.mine(one, now, B.bk.find(es, k)), B.bk.period(one)), now},
         u => B.bk.find(B.bk.unfilled(one, now, B.bk.drop(es, k)), k))
         == Some{B.bk.B{Nat.sub(B.bk.mine(one, now, B.bk.find(es, k)), B.bk.period(one)), now}} : Maybe<&2, B.bk.B>}
  {==}

def Laws.level_le_cap(r, now, l, at):
  min_le(B.bk.cap(r), Nat.add(l, Nat.sub(now, at)))

def Laws.level_mono(r, l, at, t1, t2, h):
  min_mono(B.bk.cap(r), Nat.add(l, Nat.sub(t1, at)), Nat.add(l, Nat.sub(t2, at)), add_mono(l, Nat.sub(t1, at), Nat.sub(t2, at), sub_mono(t1, t2, at, h)))

def Laws.burst():
  {==}

def Laws.together():
  {==}

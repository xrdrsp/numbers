import Mathlib.Tactic

import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Algebra.Ring.Regular
import Mathlib.Order.Interval.Finset.Defs
import Batteries.CodeAction

import Numbers.naturals

/-
**IMPORTANT** This file actually starts from line 349. Line 14-343 contains the same content in naturals.lean
-/

/-!

In this file we define our copy `MyNat` of the natural numbers. To check that we don't cheat
using results already proved in mathlib we don't import anything. (Note that even if `MyNat` is
defined here, the simple fact of, say, providing the `Semiring` instance allows to use a lot of
results in mathlib.)

-/

namespace MyNat

instance : CommSemiring MyNat where
  add := (· + · )
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  add_comm := add_comm
  mul := (· * ·)
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

instance : AddCancelCommMonoid MyNat where
  __ := (inferInstance : AddCommMonoid MyNat)
  add_left_cancel _ _ _ := add_left_cancel

noncomputable instance linearOrder : LinearOrder MyNat where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _

instance : IsStrictOrderedRing MyNat where
  add_le_add_left _ _ h _ := add_le_add_left h
  zero_le_one := by simp
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left
  exists_pair_ne := ⟨0, 1, one_ne_zero.symm⟩
  mul_lt_mul_of_pos_left _ h _ _ H := mul_lt_mul_of_pos_left h H
  mul_lt_mul_of_pos_right _ h _ _ H := mul_lt_mul_of_pos_right h H

instance : CanonicallyOrderedAdd MyNat where
  exists_add_of_le := id
  le_add_self := le_add_self
  le_self_add := le_self_add

instance : IsDomain MyNat := inferInstance

theorem Icc_zero_succ (a : MyNat) : (Set.Icc 0 a.succ) = insert a.succ (Set.Icc 0 a) :=
  Set.ext fun x ↦ ⟨fun hx ↦ by simp_all, fun hx ↦ by simp_all⟩

theorem Icc_succ {a b : MyNat} (hab : a ≤ b.succ) :
    (Set.Icc a b.succ) = insert b.succ (Set.Icc a b) := by
  sorry

theorem Icc_zero_left_finite (a : MyNat) : (Set.Icc 0 a).Finite := by
  sorry

@[simp] theorem Icc_succ_zero (a : MyNat) : Set.Icc a.succ 0 = ∅ := by
  sorry

theorem Icc_zero_right_finite (a : MyNat) : (Set.Icc a 0).Finite := by
  sorry

theorem Icc_finite (a b : MyNat) : (Set.Icc a b).Finite := by
  sorry

noncomputable
instance : LocallyFiniteOrder MyNat :=
  LocallyFiniteOrder.ofFiniteIcc Icc_finite

lemma eq_or_eq_of_add_mul_eq_add_mul {a b c d : MyNat} (h : a * d + b * c = a * c + b * d) :
    a = b ∨ c = d := by
  induction a generalizing b with
  | zero =>
    simp only [zero_def, zero_mul, zero_add, mul_eq_mul_left_iff] at *
    tauto
  | succ e he =>
    cases b with
    | zero =>
      simp only [succ_mul, zero_def, zero_mul, add_zero] at *
      rw [← one_mul d] at h
      nth_rewrite 1 [one_mul] at h
      rw [← one_mul c] at h
      nth_rewrite 2 [one_mul] at h
      rw [← right_distrib, ← right_distrib] at h
      simp at h
      symm at h
      right
      exact h
    | succ f =>
      simp only [succ.injEq]
      grind


end MyNat



/- True Start Here -/

/-!

All the original work is by Kevin Buzzard.

# The integers

The strategy is to observe that every integer can be written as `a - b`
for `a` and `b` naturals, so we define the "pre-integers" to be `MyNat × MyNat`, the pairs
`(a, b)` of naturals. We define an equivalence relation `≈` on `MyNat × MyNat`, with the
idea being that `(a, b) ≈ (c, d)` if and only if `a - b = c - d`. This doesn't
make sense yet, but the equivalent equation `a + d = b + c` does. We prove
that this is an equivalence relation, and define the integers to be the quotient.

## The ring structure on the integers

We extend addition and multiplication from the naturals to the integers,
and also define negation `-x` (subtraction `x - y` then comes for free
from the ring structure).
We then prove that the integers are a commutative ring. The proofs are all of
the form "reduce to a question about naturals, and then solve it using tactics
which prove theorems about naturals".

## The ordering on the integers

We prove that the integers are a total order, and also that the ordering
plays well with the ring structure.

-/

/-!

## The pre-integers

-/

-- A term of type `MyPreint` is just a pair of natural numbers.
abbrev MyPreint := MyNat × MyNat

namespace MyPreint

/-!

## The equivalence relation on the pre-integers

-/

/-- The equivalence relation on pre-integers, which we'll quotient out
by to get integers. -/
def R (x y : MyPreint) : Prop := x.1 + y.2 = x.2 + y.1

/-- Useful lemma that is mathematically trivial. -/
@[simp, grind =]
lemma R_def (a b c d : MyNat) : R (a,b) (c,d) ↔ a + d = b + c := by
  rfl

lemma R_refl : ∀ x, R x x := by
  -- intro ⟨a, b⟩
  intro x
  rcases x with ⟨a, b⟩
  rw [R_def]
  ring

lemma R_symm : ∀ {x y}, R x y → R y x := by
  intro x y h
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rw [R_def] at *
  -- grind
  rw [add_comm a d] at h
  rw [h]
  ring

lemma R_trans : ∀ {x y z}, R x y → R y z → R x z := by
  intro x y z h1 h2
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases z with ⟨e, f⟩
  rw [R_def] at *
  grind


/-- Enable `≈` notation for `R` and ability to quotient by it -/
-- you can ignore this
instance R_equiv : Setoid MyPreint where
  r := R
  iseqv := ⟨R_refl, R_symm, R_trans⟩

-- Teach the definition of `≈` to the simplifier, so `simp` becomes more powerful
@[simp, grind =] lemma equiv_def (a b c d : MyNat) : (a, b) ≈ (c, d) ↔ a + d = b + c := by
  rfl

-- Teach the definition of `Setoid.r` to the simplifier, so `simp` becomes more powerful
@[simp] lemma equiv_def' (a b c d : MyNat) : Setoid.r (a, b) (c, d) ↔ a + d = b + c := by
  rfl

/-!

## The algebraic structure on the pre-integers

-/

/-- Negation on pre-integers. -/
def neg (x : MyPreint) : MyPreint := (x.2, x.1)

-- Teach it to the simplifier
@[simp, grind =] lemma neg_def (a b : MyNat) : neg (a, b) = (b, a) := by
  rfl

lemma neg_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') : neg x ≈ neg x' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨a', b'⟩
  simp at *
  grind

/-- Addition on pre-integers. -/
@[simp] def add (x y : MyPreint) : MyPreint := (x.1 + y.1, x.2 + y.2)

-- Teach it to the simplifier
@[simp, grind =] lemma add_def (a b c d : MyNat) : add (a, b) (c, d) = (a + c, b + d) := by
  rfl

lemma add_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    add x y ≈ add x' y' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨a', b'⟩
  rcases y with ⟨c, d⟩
  rcases y' with ⟨c', d'⟩
  grind

/-- Multiplication on pre-integers. -/
@[simp] def mul (x y : MyPreint) : MyPreint :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

-- Teach it to the simplifier
@[simp, grind =] lemma mul_def (a b c d : MyNat) :
    mul (a, b) (c, d) = (a * c + b * d, a * d + b * c) := by
  rfl

lemma mul_quotient ⦃x x' : MyPreint⦄ (h : x ≈ x') ⦃y y' : MyPreint⦄ (h' : y ≈ y') :
    mul x y ≈ mul x' y' := by
  rcases x with ⟨a, b⟩
  rcases x' with ⟨a', b'⟩
  rcases y with ⟨c, d⟩
  rcases y' with ⟨c', d'⟩
  simp at *
  grind

end MyPreint

open MyPreint

/-!

## The integers: definition and algebraic structure

-/

/-- Make the integers as a quotient of preintegers. -/
abbrev MyInt := Quotient R_equiv

-- Now one can use the notation `⟦(a,b)⟧` to denote the class of `(a,b)`.

namespace MyInt

@[simp] lemma Quot_eq_Quotient (a b : MyNat) : Quot.mk Setoid.r (a, b) = ⟦(a, b)⟧ := by
  rfl

-- `0` notation (the equiv class of (0,0))
instance zero : Zero MyInt where zero := ⟦(0, 0)⟧

-- lemma stating definition of zero
lemma zero_def : (0 : MyInt) = ⟦(0, 0)⟧ := by
  rfl

-- `1` notation (the equiv class of (1,0))
instance one : One MyInt where one := ⟦(1, 0)⟧

-- lemma stating definition of one
lemma one_def : (1 : MyInt) = ⟦(1, 0)⟧ := by
  rfl

/-- Negation on integers. -/
def neg : MyInt → MyInt := Quotient.map MyPreint.neg neg_quotient

-- unary `-` notation
instance : Neg MyInt where neg := neg

/-- Addition on integers. -/
def add : MyInt → MyInt → MyInt := Quotient.map₂ MyPreint.add add_quotient

-- `+` notation
instance : Add MyInt where add := add

/-- Multiplication on integers. -/
def mul : MyInt → MyInt → MyInt := Quotient.map₂ MyPreint.mul mul_quotient

-- `*` notation
instance : Mul MyInt where mul := mul

lemma add_def (a b c d : MyNat) : (⟦(a, b)⟧ : MyInt) + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ := by
  rfl

lemma mul_def (a b c d : MyNat) :
    (⟦(a, b)⟧ : MyInt) * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ := by
  rfl

lemma add_assoc : ∀ (x y z : MyInt), (x + y) + z = x + (y + z) := by
  intro x y z
  refine Quot.induction_on₃ x y z ?_
  intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
  apply Quot.sound
  simp [Setoid.r]
  grind


-- Your proof of `add_assoc` will work for almost everything else we want to prove!

/-!

## Tactic hackery

Every single proof of every single ring axiom for the integers is:
"replace all integers with pairs of naturals, turn the question into a question
about naturals, and then get the `ring` tactic to prove it"

One slight problem is that we need three different tactics depending on whether the
axiom mentions 1, 2 or 3 variables. So we write three tactics and then one tactic
which does all three cases.

-/

macro "quot_proof₁" : tactic =>
  `(tactic|
  focus
    intro x
    refine Quot.induction_on x ?_
    rintro ⟨a, b⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₂" : tactic =>
  `(tactic|
  focus
    intro x y
    refine Quot.induction_on₂ x y ?_
    rintro ⟨a, b⟩ ⟨c, d⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

macro "quot_proof₃" : tactic =>
  `(tactic|
  focus
    intro x y z
    refine Quot.induction_on₃ x y z ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    apply Quot.sound
    simp [Setoid.r, R]
    try ring)

/-- Tactic for proving equality goals in rings defined as quotients. -/
macro "quot_proof" : tactic =>
  `(tactic|
  focus
    try quot_proof₁
    try quot_proof₂
    try quot_proof₃)

instance commRing : CommRing MyInt where
  add := (· + ·)
  add_assoc := by quot_proof
  zero := 0
  zero_add := by quot_proof
  add_zero := by quot_proof
  add_comm := by quot_proof
  mul := (· * ·)
  left_distrib := by quot_proof
  right_distrib := by quot_proof
  zero_mul := by quot_proof
  mul_zero := by quot_proof
  mul_assoc := by quot_proof
  one := 1
  one_mul := by quot_proof
  mul_one := by quot_proof
  neg := (- ·)
  mul_comm := by quot_proof
  neg_add_cancel := by quot_proof
  nsmul := nsmulRec --ignore this
  zsmul := zsmulRec --ignore this

lemma zero_ne_one : (0 : MyInt) ≠ 1 := by
  rw [zero_def, one_def]
  by_contra! h
  simp [Quotient.eq] at h

lemma mul_ne_zero (x y : MyInt) : x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  refine Quot.induction_on₂ x y ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2 h
  simp only [Quot_eq_Quotient] at *
  simp only [mul_def, zero_def, Quotient.eq, equiv_def, add_zero] at *
  simp at h1 h2
  cases MyNat.eq_or_eq_of_add_mul_eq_add_mul h with
  | inl hab =>
    apply h1
    rw [hab]
    simp [Quotient.eq]
  | inr hcd =>
    apply h2
    rw [hcd]
    simp [Quotient.eq]

lemma eq_of_mul_eq_mul_right {x y z : MyInt} (hx : x ≠ 0) (h : y * x = z * x) : y = z := by
  have : (y - z) * x = 0 := by
    rw [sub_mul, sub_eq_zero]
    assumption
  rw [← sub_eq_zero]
  by_contra! h
  apply mul_ne_zero (y - z) x h hx
  assumption

/-!

## The map from the naturals to the integers

-/

/-- The natural map from the naturals to the integers. -/
def i (n : MyNat) : MyInt := ⟦(n, 0)⟧

-- The natural map preserves 0
@[simp, grind =]
lemma i_zero : i 0 = 0 := by
  rfl

-- The natural map preserves 1
@[simp, grind =]
lemma i_one : i 1 = 1 := by
  rfl

-- The natural map preserves addition
@[grind =]
lemma i_add (a b : MyNat) : i (a + b) = i a + i b := by
  rfl

-- The natural mp preserves multiplication
@[grind =]
lemma i_mul (a b : MyNat) : i (a * b) = i a * i b := by
  simp only [i]
  apply Quot.sound
  simp

-- The natural map is injective
lemma i_injective : Function.Injective i := by
  intro a b h
  simp? [i, Quotient.eq] at h
  exact h


/-!

## Linear order structure on the integers

-/

/-- We say `x ≤ y` if there's some natural `a` such that `y = x + i a` -/
def le (x y : MyInt) : Prop := ∃ a : MyNat, y = x + i a

-- Notation `≤` for `le`
instance : LE MyInt where
  le := le

lemma le_refl (x : MyInt) : x ≤ x := by
  use 0
  simp

lemma le_trans (x y z : MyInt) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  obtain ⟨x1, hx1⟩ := h1
  obtain ⟨x2, hx2⟩ := h2
  use x1 + x2
  grind

lemma le_antisymm (x y : MyInt) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry

lemma le_total (x y : MyInt) : x ≤ y ∨ y ≤ x := by
  sorry

noncomputable instance linearOrder : LinearOrder MyInt where
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := fun _ _ => Classical.propDecidable _ --ignore this

lemma zero_le_one : (0 : MyInt) ≤ 1 := by
  use 1
  simp

/-- The natural map from the naturals to the integers preserves and reflects `≤`. -/
lemma i_le_iff (a b : MyNat) : i a ≤ i b ↔ a ≤ b := by
  sorry

/-!

## Interaction between ordering and algebraic structure

-/

lemma add_le_add_left (x y : MyInt) (h : x ≤ y) (z : MyInt) : x + z ≤ y + z := by
  sorry

lemma mul_pos (x y : MyInt) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  sorry

instance : Nontrivial MyInt := ⟨0, 1, zero_ne_one⟩

instance : ZeroLEOneClass MyInt := ⟨zero_le_one⟩

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := add_le_add_left

instance : IsStrictOrderedRing MyInt :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma exists_nat_of_nonneg (x : MyInt) (hx : 0 ≤ x) : ∃ n, x = i n := by
  obtain ⟨n, hn⟩ := hx
  use n
  grind

lemma archimedean (x : MyInt) : ∃ (n : MyNat), x ≤ i n := by
  rcases le_total 0 x with h | h
  · obtain ⟨n, hn⟩ := exists_nat_of_nonneg x h
    use n
    grind
  · use 0
    grind

end MyInt

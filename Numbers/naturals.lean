-- import Batteries.CodeAction
import Mathlib.Tactic


/-!

In this file we define our copy `MyNat` of the natural numbers. To check that we don't cheat
using results already proved in mathlib we don't import anything. (Note that even if `MyNat` is
defined here, the simple fact of, say, providing the `Semiring` instance allows to use a lot of
results in mathlib.)

-/

/-- Our copy of the natural numbers.-/
inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

#check MyNat.zero
namespace MyNat

#check zero

#check succ

#check succ zero

#check succ (succ zero)

variable (a b c : MyNat)

/-- The following is to activate the notation `(0 : MyNat)`.
Beware: if you just write `0`, sometimes Lean thinks you mean the "usual" natural number `0`. -/
instance : Zero MyNat := ⟨zero⟩

#check 0

#check (0 : MyNat)

theorem zero_def : zero = 0 := by
  rfl

def one : MyNat := succ 0

instance : One MyNat := ⟨one⟩

theorem one_def : one = 1 := by
  rfl

theorem one_eq_succ_zero : 1 = succ 0 := by
  rfl

/-- This is basically an axiom added by Lean when defining natural numbers (feel free to ask more
details if you want!) -/
theorem succ_ne_zero : succ a ≠ 0 := by
  intro h
  contradiction

theorem one_ne_zero : (1 : MyNat) ≠ 0 := by
  intro h
  rw [one_eq_succ_zero] at h
  apply succ_ne_zero at h
  exact h

theorem zero_ne_one : (0 : MyNat) ≠ 1 := by
  intro h
  symm at h
  apply one_ne_zero at h
  exact h

/-- Addition on `MyNat`. -/
def add : MyNat → MyNat → MyNat
| a, 0 => a
| a, (succ b) => succ (add a b)

instance : Add MyNat where
  add := add

theorem add_zero : a + 0 = a := by
  rfl

theorem add_succ : a + succ b = succ (a + b):= by
  rfl

@[grind =] --Ignore all tags like this one, same for `@[simp]`
theorem succ_eq_add_one : succ a = a + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

@[simp]
theorem add_one_ne_zero : a + 1 ≠ 0 := by
  intro h
  rw [← succ_eq_add_one] at h
  apply succ_ne_zero at h
  exact h

theorem zero_add : 0 + a = a := by
  induction a with
  | zero =>
    rfl
  | succ a ha =>
    rw [add_succ]
    rw [ha]

theorem succ_add : (succ a) + b = succ (a + b) := by
  induction b with
  | zero =>
    rfl
  | succ b hb =>
    rw [add_succ]
    rw [hb]
    rw [add_succ]


theorem add_assoc : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rfl
  | succ c hc =>
    repeat rw [add_succ]
    rw [hc]

theorem add_comm : a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_def]
    rw [zero_add]
    rfl
  | succ a ha =>
    rw [succ_add, add_succ]
    rw [ha]

variable {a b} in
theorem eq_zero_of_add_eq_zero (h : a + b = 0) : a = 0 := by
  induction b with
  | zero =>
    rw [zero_def, add_zero] at h
    exact h
  | succ b hb =>
    rw [add_succ] at h
    have h_contr := succ_ne_zero (a + b)
    contradiction

/-- Multiplication on `MyNat`. -/
def mul : MyNat → MyNat → MyNat
| _, 0 => 0
| a, (succ b) => mul a b + a

instance : Mul MyNat where
  mul := mul

theorem mul_zero : a * 0 = 0 := by
  rfl

theorem mul_succ : a * b.succ = a * b + a := by
  rfl

@[grind =]
theorem succ_mul : a.succ * b = a * b + b := by
  induction b with
  | zero =>
    rw [zero_def]
    rw [mul_zero, mul_zero]
    rfl
  | succ b hb =>
    repeat rw [mul_succ]
    rw [hb]
    repeat rw [add_assoc]
    rw [add_succ]
    rw [add_succ a]
    rw [add_comm a]

theorem zero_mul : 0 * a = 0 := by
  induction a with
  | zero =>
    rw [zero_def, mul_zero]
  | succ a ha =>
    rw [mul_succ]
    rw [ha]
    rfl

theorem left_distrib : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [zero_def, add_zero, mul_zero]
    rw [add_zero]
  | succ c hc =>
    rw [add_succ, mul_succ, mul_succ]
    rw [hc]
    rw [add_assoc]


theorem mul_one : a * 1 = a := by
  induction a with
  | zero =>
    rw [zero_def, zero_mul]
  | succ a ha =>
    rw [succ_mul, ha]
    rw [succ_eq_add_one]

theorem mul_comm : a * b = b * a := by
  induction a with
  | zero =>
    rw [zero_def, zero_mul, mul_zero]
  | succ a ha =>
    rw [succ_mul, mul_succ]
    rw [ha]


theorem right_distrib : (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b), left_distrib]
  rw [mul_comm c, mul_comm c]


theorem one_mul : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem mul_assoc : a * b * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [zero_def]
    repeat rw[mul_zero]
  | succ c hc =>
    repeat rw [mul_succ]
    rw [left_distrib, hc]

variable {a b c} in
/-- In this one you may find useful to use `succ.inj`, the `succ` function is injective. -/
theorem add_left_cancel (h : a + b = a + c) : b = c := by
  induction a with
  | zero =>
    rw [zero_def] at h
    repeat rw [zero_add] at h
    exact h
  | succ a ha =>
    repeat rw [succ_add] at h
    rw [ha]
    apply succ.inj
    exact h

theorem mul_ne_zero : ∀ {a b : MyNat}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  | 0, b => by
    simp
  | a, 0 => by
    simp
  | a + 1, b + 1 => by
    intro h1 h2
    rw [left_distrib, right_distrib, right_distrib,
        one_mul, mul_one, mul_one]
    rw [← succ_eq_add_one, add_succ]
    apply succ_ne_zero

/-- The predecessor function, with `pred 0 = 0`. -/
def pred : MyNat → MyNat
| zero => 0
| succ a => a

@[simp]
theorem pred_zero : pred 0 = 0 := by
  rfl

theorem pred_succ : pred (succ a) = a := by
  rfl

@[simp]
theorem add_one_pred : pred (a + 1) = a := by
  rw [← succ_eq_add_one]
  rw [pred_succ]

variable {a} in
theorem succ_pred (ha : a ≠ 0) : succ (pred a) = a := by
  cases a with
  | zero =>
    contradiction
  | succ d =>
    rw [pred_succ]

variable {a} in
@[simp]
theorem pred_add_one (ha : a ≠ 0) : (pred a) + 1 = a := by
  rw [← succ_eq_add_one]
  rw [succ_pred]
  exact ha

/-- The order relation on `MyNat`. -/
def le : Prop := ∃ x, b = a + x

instance : LE MyNat where
  le := le

lemma le_iff : a ≤ b ↔ ∃ x, b = a + x := by
  rfl

@[simp]
theorem zero_le : 0 ≤ a := by
  rw [le_iff]
  use a
  rw [zero_add]

theorem le_succ : a ≤ a.succ := by
  rw [le_iff]
  use 1
  rw [succ_eq_add_one]

theorem le_refl : a ≤ a := by
  rw [le_iff]
  use 0
  rw [add_zero]

variable {a b c} in
theorem le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff] at *
  obtain ⟨x1, hx1⟩ := hab
  obtain ⟨x2, hx2⟩ := hbc
  use x1 + x2
  rw [← add_assoc, ← hx1]
  exact hx2

variable {a b} in
theorem le_antisymm (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [le_iff] at *
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hba
  rw [hx] at hy
  nth_rw 1 [← add_zero a] at hy
  rw [add_assoc] at hy
  apply add_left_cancel at hy
  cases x with
  | zero =>
    rw [zero_def] at hx
    rw [add_zero] at hx
    symm at hx
    exact hx
  | succ d =>
    rw [succ_add] at hy
    contradiction

theorem le_total : a ≤ b ∨ b ≤ a := by
  sorry

theorem le_self_add : a ≤ a + b := by
  sorry

theorem le_add_self : a ≤ b + a := by
  sorry

@[simp]
theorem le_succ_iff_eq_succ_or_le : a ≤ b.succ ↔ a = b.succ ∨ a ≤ b := by
  sorry

/-- The obvious `<` relation. -/
def lt : Prop := a ≤ b ∧ ¬b ≤ a

instance : LT MyNat where
  lt := lt

variable {a b} in
theorem lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b := by
  sorry

theorem ne_zero_iff_pos : a ≠ 0 ↔ 0 < a := by
  sorry

theorem lt_iff_ex_ne_zero : a < b ↔ ∃ x ≠ 0, b = a + x := by
  sorry

variable {a b c}

theorem add_le_add_left (hab : a ≤ b) : a + c ≤ b + c := by
  sorry

theorem mul_lt_mul_of_pos_left (hc : 0 < c) (hab : a < b) : c * a < c * b := by
  sorry

theorem mul_lt_mul_of_pos_right (hc : 0 < c) (hab : a < b) : a * c < b * c := by
  sorry

theorem le_of_add_le_add_left (h : a + b ≤ a + c) : b ≤ c := by
  sorry

theorem mul_left_cancel_of_ne_zero (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

theorem mul_right_cancel_of_ne_zero (ha : a ≠ 0) (h : b * a = c * a) : b = c := by
  sorry

end MyNat

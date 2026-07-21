import Numbers.rationals

/-!

# The order on the rationals

We prove that the rationals are a total order, and also that the ordering
plays well with the ring structure.

-/

namespace MyRat

/-!

## Nonnegativity on the rationals

-/

-- Note: forming the prerational requires `b ≠ 0`, which we get from the
-- assumption `0 < b` as `hb.ne'`.
def IsNonneg (x : MyRat) : Prop :=
  ∃ (a b : MyInt) (_ : 0 ≤ a) (hb : 0 < b), x = ⟦(a, ⟨b, hb.ne'⟩)⟧

/-!

### Relationship with 0 and 1

-/

@[simp]
lemma zero_nonneg : IsNonneg 0 := by
  use 0, 1
  simp [zero_def]


@[simp]
lemma one_nonneg : IsNonneg 1 := by
  use 1, 1
  simp [one_def]

/-!

## Relationship with neg

-/

lemma nonneg_neg {x : MyRat} (h : IsNonneg x) (h' : IsNonneg (-x)) :
    x = 0 := by
  rcases h with ⟨a, b, ha, hb, h1⟩
  rcases h' with ⟨c, d, hc, hd, h2⟩
  rw [h1, neg_def, Quotient.eq] at h2
  simp at h2
  have h0 : a = 0 := by
    nlinarith
  rw [h0] at h1
  rw [h1, zero_def, Quotient.eq]
  simp

-- this one is also useful
lemma nonneg_neg_of_not_nonneg {x : MyRat} : ¬ IsNonneg x → IsNonneg (-x) := by
  refine Quot.induction_on x ?_
  sorry


/-!

## Relationship with addition

-/

lemma isNonneg_add_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x + y) := by
  sorry

/-!

## Relationship with multiplication

-/

-- github copilot wrote the first proof I had of this
lemma isNonneg_mul_isNonneg {x y : MyRat} (hx : IsNonneg x) (hy : IsNonneg y) :
    IsNonneg (x * y) := by
  sorry

/-!

## Relationship with inverse

-/

lemma isNonneg_inv_isNonneg {x : MyRat} (hx : IsNonneg x) :
    IsNonneg x⁻¹ := by
  sorry

/-!

## The linear order on the rationals

I think that's it for non-negativity on the rationals. Let's see
if we can use those theorems about nonnegativity to prove that
the rationals are a linear order.

-/

/-- Our definition of `x ≤ y` on the rationals. -/
def le (x y : MyRat) : Prop := IsNonneg (y - x)

lemma le_refl (x : MyRat) : le x x := by
  sorry

/-!

Next is transitivity

-/

lemma le_trans (x y z : MyRat) (h1 : le x y) (h2 : le y z) : le x z := by
  sorry

/-!

Next is antisymmetry

-/

lemma le_antisymm (x y : MyRat) (hxy : le x y) (hyx : le y x) : x = y := by
  sorry

instance : PartialOrder MyRat where
  le := le
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

lemma le_def (x y : MyRat) : x ≤ y ↔ IsNonneg (y - x) := by
  sorry

lemma zero_le_iff_IsNonneg (x : MyRat) : 0 ≤ x ↔ IsNonneg x := by
  sorry

/-!

We now develop some basic theory of `≤` on the rationals.
Let's warm up with 0 ≤ 1.

-/

lemma zero_le_one : (0 : MyRat) ≤ 1 := by
  sorry

instance : ZeroLEOneClass MyRat := ⟨zero_le_one⟩

lemma add_le_add_left (x y : MyRat) (h : x ≤ y) (t : MyRat) : x + t ≤ y + t := by
  simp_all [le_def]

lemma mul_nonneg (x y : MyRat) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  sorry

instance : IsOrderedAddMonoid MyRat where
  add_le_add_left := add_le_add_left

instance : IsOrderedRing MyRat :=
  IsOrderedRing.of_mul_nonneg mul_nonneg

/-!

The interplay between the ordering and the natural maps from
the naturals and integers to the rationals.

-/

-- let's do `j` first, then we can use it for `i`

/-- The natural map from the integers to the rationals
preserves and reflects `≤`. -/
lemma j_le_iff (p q : MyInt) : j p ≤ j q ↔ p ≤ q := by
  sorry

/-- The natural map from the naturals to the rationals preserves
and reflects `≤`. -/
lemma i_le_iff (a b : MyNat) : i a ≤ i b ↔ a ≤ b := by
  sorry

lemma i_lt_iff (a b : MyNat) : i a < i b ↔ a < b := by
  sorry

/-!

## Linear order structure on the rationals

-/

lemma le_total (a b : MyRat) : a ≤ b ∨ b ≤ a := by
  sorry

noncomputable instance linearOrder : LinearOrder MyRat where
  le_total := le_total
  toDecidableLE := Classical.decRel _

lemma mul_pos (a b : MyRat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  sorry

noncomputable instance : IsStrictOrderedRing MyRat :=
  IsStrictOrderedRing.of_mul_pos mul_pos

lemma archimedean (x : MyRat) : ∃ (n : MyNat), x ≤ i n := by
  rcases le_total 0 x with h | h
  swap
  · use 0
    rw [i_zero]
    exact h
  · revert h
    refine Quot.induction_on x ?_
    intro ⟨a, b, hb⟩ h
    simp at *
    rcases h with ⟨c, d, hc, hd, h⟩
    simp at h
    obtain ⟨n, hn⟩ := MyInt.archimedean c
    use n
    simp only [i]
    use MyInt.i n - c, 1
    refine ⟨?_, by norm_num, ?_⟩
    · -- 0 ≤ MyInt.i n - c from c ≤ MyInt.i n
      -- hn : c ≤ i n means ∃ k, i n = c + i k
      -- We need: ∃ k, MyInt.i n - c = 0 + i k, i.e., ∃ k, MyInt.i n - c = i k
      obtain ⟨k, hk⟩ := hn
      use k
      -- i k = MyInt.i n - c
      have : MyInt.i n = c + MyInt.i k := by simp [hk]
      linarith
    · -- Need to show the subtraction gives the right result
      sorry

end MyRat

/-

Both of these now work

#synth LinearOrder MyRat
#synth IsStrictOrderedRing MyRat

-/

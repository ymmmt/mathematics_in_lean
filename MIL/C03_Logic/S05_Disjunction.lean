import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    have h' : x ≤ 0 := le_of_lt h
    exact le_neg_self_iff.mpr h'

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    exact neg_le_self h
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  · rw [neg_le]
    rw [neg_add]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
  · exact add_le_add (le_abs_self x) (le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    constructor
    · exact Or.inl
    · intro h
      rcases h with h' | h'
      · exact h'
      · have : -y ≤ y := neg_le_self hy
        exact lt_of_lt_of_le h' this
  · rw [abs_of_neg hy]
    constructor
    · exact Or.inr
    · intro h
      rcases h with h' | h'
      · have : y < -y := lt_neg_self_iff.mpr hy
        exact lt_trans h' this
      · exact h'

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    constructor
    · rw [neg_lt]
      have : -x ≤ |x| := neg_le_abs_self x
      exact lt_of_le_of_lt this h
    · have : x ≤ |x| := le_abs_self x
      exact lt_of_le_of_lt this h
  · intro ⟨h₁, h₂⟩
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      exact h₂
    · rw [abs_of_neg h]
      rw [neg_lt]
      exact h₁

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right
    exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

theorem aux {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [← @sub_eq_zero _ _ x y, ← @sub_eq_zero _ _ x (-y)]
  rw [sub_neg_eq_add]
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  have : (x - y) * (x + y) = 0 :=
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = y ^ 2 - y ^ 2 := by rw [h]
      _ = 0 := by ring
  exact this

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (1 : ℝ) = 1 ^ 2 := by norm_num
  rw [this] at h
  exact aux h

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

-- example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
--   sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [← @sub_eq_zero _ _ x y, ← @sub_eq_zero _ _ x (-y)]
  rw [sub_neg_eq_add]
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  have : (x - y) * (x + y) = 0 :=
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = y ^ 2 - y ^ 2 := by rw [h]
      _ = 0 := by ring
  exact this

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro himp
    by_cases h : P
    · exact Or.inr (himp h)
    · exact Or.inl h
  · rintro (hnp | hq)
    · intro hp
      exact absurd hp hnp
    · intro hp
      exact hq

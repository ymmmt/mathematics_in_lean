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
  match le_or_gt 0 x with
  | Or.inl h =>
    rw [abs_of_nonneg h]
  | Or.inr h =>
    rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    rw [abs_of_nonneg h]
    linarith
  case inr h =>
    rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y)
  case inl h =>
    rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self x) (le_abs_self y)
  case inr h =>
    rw [abs_of_neg h]
    rw [neg_add]
    exact add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    cases le_or_gt 0 y
    case mp.inl h' =>
      rw [abs_of_nonneg h'] at h
      left
      exact h
    case mp.inr h' =>
      rw [abs_of_neg h'] at h
      right
      exact h
  intro h
  cases h
  case mpr.inl h' =>
    have : y ≤ |y| := le_abs_self y
    linarith
  case mpr.inr h' =>
    have : -y ≤ |y| := neg_le_abs_self y
    linarith

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    cases le_or_gt 0 x
    case mp.inl h' =>
      rw [abs_of_nonneg h'] at h
      constructor
      · linarith
      exact h
    case mp.inr h' =>
      rw [abs_of_neg h'] at h
      constructor
      · linarith
      linarith
  intro ⟨h₁, h₂⟩
  cases le_or_gt 0 x
  case mpr.inl h' =>
    rw [abs_of_nonneg h']
    exact h₂
  case mpr.inr h' =>
    rw [abs_of_neg h']
    linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

#check sq_nonneg
#check pow_two_nonneg

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x + 1) * (x - 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h₁ | h₂
  · right
    linarith
  left
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h₁ | h₂
  · right; linarith
  left; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

#check eq_neg_of_add_eq_zero_left
#check eq_of_sub_eq_zero

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x + 1) * (x - 1) = 0 :=
    calc
      (x + 1) * (x - 1) = x ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h₁ | h₂
  · right
    exact eq_neg_of_add_eq_zero_left h₁
  left
  exact eq_of_sub_eq_zero h₂

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x + y) * (x - y) = 0 :=
    calc
      (x + y) * (x - y) = x ^ 2 - y ^ 2 := by ring
      _ = y ^ 2 - y ^ 2 := by rw [h]
      _ = 0 := by ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h₁ | h₂
  · right
    exact eq_neg_of_add_eq_zero_left h₁
  left
  exact eq_of_sub_eq_zero h₂

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
  · intro h
    by_cases h' : P
    · right; exact h h'
    left ; exact h'
  rintro (hnp | hq) hp
  · contradiction
  exact hq

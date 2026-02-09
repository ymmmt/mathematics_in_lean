import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . show min (min a b) c ≤ a
      apply le_trans
      apply min_le_left
      apply min_le_left
    . show min (min a b) c ≤ min b c
      apply le_min
      . show min (min a b) c ≤ b
        apply le_trans
        apply min_le_left
        apply min_le_right
      . show min (min a b) c ≤ c
        apply min_le_right
  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . show min a (min b c) ≤ min a b
      apply le_min
      . show min a (min b c) ≤ a
        apply min_le_left
      . show min a (min b c) ≤ b
        apply le_trans
        apply min_le_right
        apply min_le_left
    . show min a (min b c) ≤ c
      apply le_trans
      apply min_le_right
      apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    apply add_le_add_left
    apply min_le_left
  . show min a b + c ≤ b + c
    apply add_le_add_left
    apply min_le_right

#check add_neg_cancel_right
#check add_neg
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . exact aux a b c
  . calc
      min (a + c) (b + c) = min (a + c) (b + c) + c + -c :=
        (add_neg_cancel_right (min (a + c) (b + c)) c).symm
      _ = min (a + c) (b + c) + -c + c := by ring
      _ ≤ min (a + c + -c) (b + c + -c) + c := by
        linarith [aux (a + c) (b + c) (-c)]
      _ = min a b + c := by ring_nf

#check (abs_add_le: ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have : |a| ≤ |a - b| + |b| := by
    calc
      |a| = |a - b + b| := by ring_nf
      _ ≤ |a - b| + |b| := by apply abs_add_le
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

#check dvd_add

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  rw [pow_two, pow_two]
  apply dvd_add
  apply dvd_add
  . exact dvd_trans (dvd_mul_right x z) (dvd_mul_left (x * z) y)
  . exact dvd_mul_left x x
  . exact dvd_trans h (dvd_mul_left w w)
end

section
variable (a b m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ (x y : ℕ), Nat.gcd x y ∣ Nat.gcd y x := by
    intro x y
    have hy : Nat.gcd x y ∣ y := gcd_dvd_right x y
    have hx : Nat.gcd x y ∣ x := gcd_dvd_left x y
    exact (dvd_gcd_iff (gcd x y) y x).mpr ⟨hy, hx⟩
  exact dvd_antisymm (h m n) (h n m)
end

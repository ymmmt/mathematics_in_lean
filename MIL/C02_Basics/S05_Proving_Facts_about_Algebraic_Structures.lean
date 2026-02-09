import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    · apply le_inf
      · trans x ⊓ y
        apply inf_le_left
        apply inf_le_right
      · apply inf_le_right
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · apply le_inf
      · apply inf_le_left
      · trans y ⊓ z
        apply inf_le_right
        apply inf_le_left
    · trans y ⊓ z
      apply inf_le_right
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤ y ⊔ x
    apply sup_le
    · apply le_sup_right
    · apply le_sup_left
  · show y ⊔ x ≤ x ⊔ y
    apply sup_le
    · apply le_sup_right
    · apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · apply sup_le
      · apply le_sup_left
      · trans y ⊔ z
        · apply le_sup_left
        · apply le_sup_right
    · trans y ⊔ z
      · apply le_sup_right
      · apply le_sup_right
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · trans x ⊔ y
      · apply le_sup_left
      · apply le_sup_left
    · apply sup_le
      · trans x ⊔ y
        · apply le_sup_right
        · apply le_sup_left
      · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem my_sup_idem : x ⊔ x = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply le_refl
  · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    · apply le_refl
    · apply inf_le_left
  · show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · show a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)
    apply sup_le
    · apply le_inf
      · apply le_sup_left
      · apply le_sup_left
    · apply le_inf
      · trans b
        · apply inf_le_left
        · apply le_sup_right
      · trans c
        · apply inf_le_right
        · apply le_sup_right
  · show (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c
    rw [h, inf_comm, h]
    apply sup_le
    · apply sup_le
      · trans a
        · apply inf_le_left
        · apply le_sup_left
      · trans a
        · apply inf_le_left
        · apply le_sup_left
    · rw [inf_comm, h]
      apply sup_le
      · trans a
        · apply inf_le_right
        · apply le_sup_left
      · rw [inf_comm]
        apply le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  . show a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c
    rw [h, sup_comm (a ⊓ b) a, h, sup_comm (a ⊓ b) c, h]
    apply le_inf
    . apply le_inf
      · trans a
        . apply inf_le_left
        · apply le_sup_left
      . trans a
        . apply inf_le_left
        . apply le_sup_left
    . apply le_inf
      . trans a
        . apply inf_le_left
        . apply le_sup_right
      . rw [sup_comm]
        trans c ⊔ b
        . apply inf_le_right
        . apply le_refl
  . show a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c)
    apply le_inf
    . apply sup_le
      . apply inf_le_left
      . apply inf_le_left
    . apply sup_le
      . trans b
        . apply inf_le_right
        . apply le_sup_left
      . trans c
        . apply inf_le_right
        . apply le_sup_right

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add_left h

example (h: 0 ≤ b - a) : a ≤ b :=
  calc
    a = 0 + a := (zero_add a).symm
    _ ≤ (b - a) + a := add_le_add_left h a
    -- _ = b + -a + a := by rw [sub_eq_add_neg]
    -- _ = b + (-a + a) := by apply add_assoc
    -- _ = b + 0 := by rw [neg_add_cancel]
    -- _ = b := by apply add_zero
    _ = b := by abel

example (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a :=
    calc
      0 = a + -a := by rw [add_neg_cancel]
      _ ≤ b + -a := by apply add_le_add_left hab (- a)
      _ = b - a := by rw [sub_eq_add_neg]
  have : 0 ≤ b * c - a * c :=
    calc
      0 ≤ (b - a) * c := mul_nonneg hab' hc
      _ = b * c - a * c := by apply sub_mul
  have : 0 + a * c ≤ b * c - a * c + a * c := by
    apply add_le_add_left this
  rw [zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at this
  assumption

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end

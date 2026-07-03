import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    show f x ∈ v
    apply h
    use x
  · intro h
    intro y ⟨x, xs, xeq⟩
    have h' : x ∈ f ⁻¹' v := h xs
    -- simp? at h'
    simp only [mem_preimage] at h'
    rw [← xeq]
    exact h'

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xff
  simp only [mem_preimage, mem_image] at xff
  rcases xff with ⟨y, ys, yeq⟩
  have : x = y := (h yeq).symm
  rw [this]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y
  intro ⟨x, xf, xeq⟩
  simp only [mem_preimage] at xf
  rw [← xeq]
  exact xf

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, rfl⟩
  simp only [mem_image]
  use x
  exact ⟨yu, rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yf
  rcases yf with ⟨x, xs, rfl⟩
  simp only [mem_image]
  use x
  exact ⟨h xs, rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xf
  simp only [mem_preimage] at *
  exact h xf

-- preimage_union
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro xf
    simp only [mem_preimage] at *
    rcases xf with fxu | fxv
    · exact Or.inl fxu
    · exact Or.inr fxv
  · rintro (xfu | xfv)
    · simp only [mem_preimage] at *
      apply subset_union_left
      exact xfu
    · simp only [mem_preimage] at *
      apply subset_union_right
      exact xfv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y yf
  rcases yf with ⟨x, xst, rfl⟩
  constructor
  · use x
    exact ⟨xst.left, rfl⟩
  · use x
    exact ⟨xst.right, rfl⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨yfs, yft⟩
  rcases yfs with ⟨x₁, x₁s, x₁eq⟩
  rcases yft with ⟨x₂, x₂t, x₂eq⟩
  have feq : f x₁ = f x₂ := by simp [x₁eq, x₂eq]
  have xeq : x₁ = x₂ := h feq
  use x₁
  constructor
  · constructor
    · exact x₁s
    · rw [xeq]
      exact x₂t
  · exact x₁eq

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨yfs, ynft⟩
  rcases yfs with ⟨x, xs, rfl⟩
  use x
  constructor
  · constructor
    · exact xs
    · intro xt
      have : f x ∈ f '' t := by use x
      contradiction
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xfu, xnfv⟩
  constructor
  · exact xfu
  · intro fxv
    contradiction

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, xs, rfl⟩, yv⟩
    use x
    exact ⟨⟨xs, yv⟩, rfl⟩
  · rintro ⟨x, xsfv, rfl⟩
    constructor
    · use x
      exact ⟨xsfv.left, rfl⟩
    · exact xsfv.right

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, xsfu, rfl⟩
  constructor
  · use x
    exact ⟨xsfu.left, rfl⟩
  · exact xsfu.right

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs,  xfu⟩
  constructor
  · use x
  · exact xfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | xfu)
  · left
    use x
  · right
    exact xfu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · rintro ⟨x, xU, rfl⟩
    simp only [mem_iUnion] at *
    rcases xU with ⟨i, xAi⟩
    use i, x
  · simp only [mem_iUnion]
    rintro ⟨i, ⟨x, xAi, rfl⟩⟩
    use x
    constructor
    · simp only [mem_iUnion]
      use i
    · rfl

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, xU, rfl⟩
  simp only [mem_iInter] at *
  intro i
  use x
  exact ⟨xU i, rfl⟩

example (i₀ : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  intro h
  simp only [mem_iInter] at h
  rcases h i₀ with ⟨x₀, xAi₀, rfl⟩
  use x₀
  constructor
  · simp only [mem_iInter]
    intro i
    rcases h i with ⟨x, xAi, xeq⟩
    have : x = x₀ := injf xeq
    rw [← this]
    exact xAi
  · rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro h
    have h' : f x ∈ ⋃ i, B i := h
    simp only [mem_iUnion] at *
    rcases h' with ⟨i, fxBi⟩
    use i, fxBi
  · simp only [mem_iUnion]
    intro ⟨i, xfBi⟩
    show f x ∈ ⋃ i, B i
    simp only [mem_iUnion]
    use i, xfBi

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  · intro (h : f x ∈ ⋂ i, B i)
    simp only [mem_iInter] at *
    intro i
    exact h i
  · intro h
    simp at *
    exact h

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy
  intro e
  calc
    x = √ y ^ 2 := sqrt_eq_iff_eq_sq hx (sqrt_nonneg y) |>.mp e
    _ = √ x ^ 2 := congr_arg (· ^ 2) e |>.symm
    _ = y := sqrt_eq_iff_eq_sq hy (sqrt_nonneg x) |>.mp e.symm |>.symm

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy
  dsimp
  intro e
  calc
    x = √ (x ^ 2) := sqrt_sq hx |>.symm
    _ = √ (y ^ 2) := congr_arg _ e
    _ = y := sqrt_sq hy

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  dsimp
  constructor
  · rintro ⟨x, xpos, rfl⟩
    exact sqrt_nonneg x
  · intro ypos
    use y ^ 2
    exact ⟨sq_nonneg y, sqrt_sq ypos⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  dsimp
  constructor
  · rintro ⟨x, hx⟩
    dsimp at hx
    rw [← hx]
    exact sq_nonneg x
  · intro ypos
    use √ y
    dsimp
    exact sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    rw [LeftInverse]
    intro x
    apply injf
    apply inverse_spec
    use x
  · intro h
    rw [LeftInverse] at h
    intro x y feq
    rw [← h x, ← h y]
    congr

example : Surjective f ↔ RightInverse (inverse f) f := by
  rw [RightInverse]
  rw [LeftInverse]
  constructor
  · intro surjf
    intro y
    apply inverse_spec
    exact surjf y
  · intro h y
    use (inverse f y)
    exact h y

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [Set.mem_setOf]
    push_neg
    rw [h]
    exact h₂
  contradiction

-- COMMENTS: TODO: improve this
end

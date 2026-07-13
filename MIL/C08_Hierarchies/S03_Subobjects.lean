import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z
      intro ⟨t, ht, u, hu, htu⟩ ⟨v, hv, w, hw, hvw⟩
      use t * v, N.mul_mem' ht hv, w * u, N.mul_mem' hw hu
      calc
        x * (t * v) = x * t * v := (mul_assoc x t v).symm
        _ = y * u * v := by rw [htu]
        _ = y * (u * v) := mul_assoc y u v
        _ = y * (v * u) := by rw [mul_comm u v]
        _ = y * v * u := (mul_assoc y v u).symm
        _ = z * w * u := by rw [hvw]
        _ = z * (w * u) := mul_assoc z w u
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

lemma mul_aux [CommMonoid M] (a b x y : M) : a * b * (x * y) = a * x * (b * y) :=
  calc
    a * b * (x * y) = a * (b * (x * y)) := mul_assoc a b (x * y)
    _ = a * (b * x * y) := by rw [mul_assoc]
    _ = a * (x * b * y) := by rw [mul_comm b x]
    _ = a * (x * (b * y)) := by rw [← mul_assoc x b y]
    _ = a * x * (b * y) := by rw [mul_assoc]

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) <| by
    intro a₁ a₂ ha b₁ b₂ hb
    dsimp
    rcases ha with ⟨x, hx, y, hy, axy⟩
    rcases hb with ⟨z, hz, w, hw, bzw⟩
    use x * z, N.mul_mem' hx hz, y * w, N.mul_mem' hy hw
    calc
      a₁ * b₁ * (x * z) = a₁ * x * (b₁ * z) := by apply mul_aux
      _ = a₂ * y * (b₂ * w) := by rw [axy, bzw]
      _ = a₂ * b₂ * (y * w) := by apply mul_aux
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
    rintro ⟨a⟩
    apply Quotient.sound
    dsimp
    rw [one_mul]
    apply @Setoid.refl M N.Setoid
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    dsimp
    rw [mul_one]
    apply @Setoid.refl M N.Setoid

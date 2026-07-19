import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp only [Int.cast_add]
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem
    group
  inv_mem' := by
    dsimp
    rintro a ⟨h, ⟨hH, rfl⟩⟩
    use h⁻¹, H.inv_mem hH
    group
  mul_mem' := by
    dsimp
    rintro a b ⟨ha, ⟨haH, rfl⟩⟩ ⟨hb, ⟨hbH, rfl⟩⟩
    use ha * hb, H.mul_mem haH hbH
    group

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  simp [comap]
  intro x xS
  simp [Set.mem_preimage] at *
  exact hST xS

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  simp [map]
  intro x xS
  simp [Set.mem_preimage]
  use x
  exact ⟨hST xS, rfl⟩

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext x
  simp only [mem_comap]
  rfl

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext k
  simp only [mem_map]
  constructor
  · rintro ⟨x, xS, hx⟩
    use φ x
    constructor
    · use x
    · exact hx
  · rintro ⟨y, ⟨x, xS, hx⟩, hy⟩
    use x, xS
    simp
    rw [hx]
    rw [hy]

end exercises

open scoped Classical


example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

open Subgroup

example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨x, ⟨xH, h⟩⟩
    intro y yH
    have : 1 = x := h 1 H.one_mem
    rw [this]
    exact h y yH

#check card_dvd_of_le

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
  apply eq_bot_iff_card.mpr
  apply Nat.eq_one_of_dvd_coprimes h
  · show Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H
    exact card_dvd_of_le inf_le_left
  · show Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K
    exact card_dvd_of_le inf_le_right

open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle

#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]


def myGroup := PresentedGroup {.of () ^ 3} deriving Group

def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup

noncomputable section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm

open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out ω)) :=
  MulAction.selfEquivSigmaOrbits G X

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  constructor
  · intro xconj
    have : ∃ h, h ∈ H ∧ x = 1 * h * 1⁻¹ := xconj
    rcases this with ⟨h, hH, xeq⟩
    rw [xeq]
    rw [one_mul, inv_one, mul_one]
    exact hH
  · intro xH
    show ∃ h, h ∈ H ∧ x = 1 * h * 1⁻¹
    use x, xH
    group

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    intro H
    exact conjugate_one H
  mul_smul := by
    intro x y H
    show conjugate (x * y) H = conjugate x (conjugate y H)
    ext g
    constructor
    · intro gconj
      rcases gconj with ⟨h, hH, heq⟩
      use y * h * y⁻¹
      constructor
      · use h
      · group at *
        exact heq
    · rintro ⟨h, hH, rfl⟩
      rcases hH with ⟨i, iH, rfl⟩
      use i, iH
      group

end GroupActions

noncomputable section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  apply Nat.eq_of_mul_eq_mul_right (m := Nat.card H) Nat.card_pos
  nth_rw 2 [mul_comm]
  rw [← h']
  rw [← index_eq_card]
  rw [index_mul_card]

variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

lemma injective_comp_of_inj_of_inj {α β γ : Type*} (f : α → β) (g : β → γ)
    (injf : Function.Injective f) (injg : Function.Injective g) : Function.Injective (g ∘ f) := by
  intro x y h
  have : g (f x) = g (f y) := h
  exact injf (injg this)

def iso₁ : K ≃* G ⧸ H := by
  let f : K →* G ⧸ H := (QuotientGroup.mk' H).restrict K
  apply MulEquiv.ofBijective f
  apply Nat.bijective_iff_injective_and_card f |>.mpr
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp only [QuotientGroup.ker_mk', subgroupOf_eq_bot]
    exact h
  · symm
    exact aux_card_eq h'

def iso₁' : H ≃* G ⧸ K := by
  let f : H →* G ⧸ K := (QuotientGroup.mk' K).restrict H
  apply MulEquiv.ofBijective f
  apply Nat.bijective_iff_injective_and_card f |>.mpr
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' K).ker_restrict H]
    simp only [QuotientGroup.ker_mk', subgroupOf_eq_bot]
    exact h.symm
  · symm
    rw [mul_comm] at h'
    exact aux_card_eq h'

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  let fK : G →* G ⧸ K := QuotientGroup.mk' K
  let fH : G →* G ⧸ H := QuotientGroup.mk' H
  set f : G →* (G ⧸ K) × (G ⧸ H) := MonoidHom.prod fK fH with f_def
  apply MulEquiv.ofBijective f
  apply Nat.bijective_iff_injective_and_card f |>.mpr
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    rw [QuotientGroup.ker_mk', QuotientGroup.ker_mk']
    apply h.symm.eq_bot
  · rw [Nat.card_prod]
    rw [aux_card_eq h', ← index_eq_card, index_mul_card]

#check MulEquiv.prodCongr

def finalIso : G ≃* H × K := by
  apply MulEquiv.trans (N := (G ⧸ K) × (G ⧸ H))
  · exact iso₂ h h'
  · apply MulEquiv.prodCongr
    · exact iso₁' h h' |>.symm
    · exact iso₁ h h' |>.symm

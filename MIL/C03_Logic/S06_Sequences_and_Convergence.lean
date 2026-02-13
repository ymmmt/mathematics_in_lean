import MIL.Common
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- #check mul_lt_mul_left
-- #check mul_lt_mul_right
-- #check mul_lt_mul_iff_right
-- #check CovariantClass
-- #check CovariantClass.elim
-- #check Function.swap

-- #check lt_mul_self

-- #check @mul_lt_mul ℝ
-- #check @mul_lt_mul_right ℝ
-- #check @mul_lt_mul_iff_right ℝ
-- #check MulLeftStrictMono ℝ

-- #check _root_.mul_lt_mul_iff_right
-- #check mul_lt_mul_of_pos_right

-- #check @mul_lt_mul_left ℝ

#check mul_lt_mul
#check (@mul_lt_mul ℝ _ _ _ 1 2 2 2 _ _)

-- ℝ is NOT instance of MulRightStrictmono/MulLeftStrictmono, so
-- mul_lt_mul_right and mul_lt_mul_left and so on can't be used here.
example {a : ℝ} (h : 1 < a) : a < a * a := by
  -- convert (@mul_lt_mul ℝ _ _ _ 1 a a a _ _ h (by rfl) (by linarith) (by linarith))
  convert mul_lt_mul h (le_refl a) (by linarith : 0 < a) (by linarith : 0 ≤ a)
  rw [one_mul]

theorem real_mul_lt_mul_right {b c : ℝ} : b < c → c ≥ 0 → ∀ a > 0, a * b < a * c := by
  intro hbc hc a apos
  calc
    a * b = b * a := by ring
    _ < c * a := mul_lt_mul hbc (le_refl a) apos hc
    _ = a * c := by ring

theorem real_mul_lt_mul_left {a b : ℝ} : a < b → b ≥ 0 → ∀ c > 0, a * c < b * c := by
  intro hab hb c cpos
  have : c * a < c * b := real_mul_lt_mul_right hab hb c cpos
  rw [mul_comm c a, mul_comm c b] at this
  assumption

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have nges : n ≥ Ns := le_trans (le_max_left Ns Nt) nge
  have nget : n ≥ Nt := le_trans (le_max_right Ns Nt) nge
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs n nges) (ht n nget)
    _ = ε := by ring

#check mul_div_cancel_left₀

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : ε / |c| > 0 := div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨N, hs⟩
  use N
  intro n nge
  calc
    |c * s n - c * a| = |c * (s n - a)| := by ring_nf
    _ = |c| * |s n - a| := abs_mul _ _
    _ < |c| * (ε / |c|) :=
      real_mul_lt_mul_right (hs n nge) (by linarith : ε / |c| ≥ 0) |c| acpos
    _ = |c| * ε / |c| := by ring
    _ = ε := mul_div_cancel_left₀ ε (by linarith : |c| ≠ 0)

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  calc
    |s n| = |a + (s n - a)| := by ring_nf
    _ ≤ |a| + |s n - a| := abs_add_le _ _
    _ < |a| + 1 := add_lt_add_right (h n nge) |a|

#check mul_lt_mul
#check le_of_lt
#check mul_div_cancel_left₀

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  let N := max N₀ N₁
  use N
  intro n nge
  have nge₀ : n ≥ N₀ := le_trans (le_max_left _ _) nge
  have nge₁ : n ≥ N₁ := le_trans (le_max_right _ _) nge
  rw [sub_zero]
  simp [sub_zero] at h₁
  rcases lt_trichotomy |t n| 0 with (hlt | heq | hgt)
  · have : |t n| ≥ 0 := abs_nonneg _
    linarith
  · calc
      |s n * t n| = |s n| * |t n| := abs_mul _ _
      _ = |s n| * 0 := by rw [heq]
      _ = 0 := by ring
      _ < ε := by exact εpos
  calc
    |s n * t n| = |s n| * |t n| := abs_mul _ _
    _ < B * (ε / B) := mul_lt_mul (h₀ n nge₀) (le_of_lt (h₁ n nge₁)) hgt (by linarith)
    _ = B * ε / B := by ring
    _ = ε := mul_div_cancel_left₀ ε (by linarith : B ≠ 0)

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    exact sub_ne_zero_of_ne abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left _ _)
  have absb : |s N - b| < ε := hNb N (le_max_right _ _)
  apply (lt_self_iff_false |a - b|).mp
  calc
    |a - b| = |(s N - b) + - (s N - a)| := by ring_nf
    _ ≤ |s N - b| + |- (s N - a)| := abs_add_le _ _
    _ = |s N - b| + |s N - a| := by rw [abs_neg]
    _ < ε + ε := add_lt_add absb absa
    _ = |a - b| := by ring

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

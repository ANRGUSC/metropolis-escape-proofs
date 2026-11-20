import Metropolis.LowerFluxDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open scoped ENNReal
open Finset
namespace Metropolis.Lower
open Metropolis.Green
noncomputable section
variable {S : Type*} [DecidableEq S]

def stay (K : Kernel S) (a : S) (n : ℕ) : ℝ≥0∞ := ∑' y, steps K n a y

theorem stay_le_one (K : Kernel S) (hK : ∀ x, (∑' y, K x y) ≤ 1) (a : S) (n : ℕ) :
    stay K a n ≤ 1 := by
  induction n generalizing a with
  | zero => simp [stay,steps,identity]
  | succ n ih =>
    calc stay K a (n+1) = ∑' z, K a z * stay K z n := by
           unfold stay
           simp only [steps, compose, ← ENNReal.tsum_mul_left]
           exact ENNReal.tsum_comm
         _ ≤ ∑' z, K a z * 1 := ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (ih z)
         _ ≤ 1 := by simpa using hK a

theorem killed_le (P : Kernel S) (A : Set S) [DecidablePred (· ∈ A)] (x y : S) :
    killed P A x y ≤ P x y := by unfold killed; split_ifs <;> simp

theorem steps_le_of_le {P Q : Kernel S} (h : ∀ x y, P x y ≤ Q x y) (n : ℕ) (x y : S) :
    steps P n x y ≤ steps Q n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    exact ENNReal.tsum_le_tsum fun z => mul_le_mul' (h x z) (ih z y)

theorem killed_mean_mono (P : Kernel S) {A B : Set S} [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] (h : A ⊆ B) (a : S) :
    meanLifetime (killed P B) a ≤ meanLifetime (killed P A) a := by
  have hk (x y : S) : killed P B x y ≤ killed P A x y := by
    unfold killed
    by_cases hb : x ∈ B ∨ y ∈ B
    · simp [hb]
    · have ha : ¬ (x ∈ A ∨ y ∈ A) := fun e => hb (e.imp (fun m => h m) (fun m => h m))
      simp [ha,hb]
  exact ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum (steps_le_of_le hk n a)

/-- A reversible chain started at a state of unit mass sends at most the
stationary exit flux through a killed boundary during each time step. -/
theorem stay_plus_flux (P : Kernel S) (μ : S → ℝ≥0∞)
    (hP : ∀ x, (∑' y, P x y) = 1) (bal : Balance μ P)
    (A : Set S) [DecidablePred (· ∈ A)] (a : S) (ha : a ∉ A) (hma : μ a = 1) (n : ℕ) :
    1 ≤ stay (killed P A) a n + n * stationaryExit P μ A := by
  let K := killed P A
  have hK (x : S) : (∑' y, K x y) ≤ 1 :=
    (ENNReal.tsum_le_tsum (killed_le P A x)).trans (hP x).le
  have bound (t : ℕ) (x : S) : steps K t a x ≤ μ x := by
    have hb := steps_balance (killed_balance bal A) t a x
    have hentry : steps K t x a ≤ 1 :=
      (ENNReal.le_tsum a).trans (stay_le_one K hK x t)
    calc steps K t a x = μ x * steps K t x a := by simpa [hma, K] using hb
         _ ≤ μ x := by simpa using (mul_le_mul' (le_rfl : μ x ≤ μ x) hentry)
  have noArrival (t : ℕ) (x : S) (hx : x ∈ A) : steps K t a x = 0 := by
    cases t with
    | zero => simp [steps,identity,show a ≠ x by rintro rfl; exact ha hx]
    | succ t => simp [steps_right,compose,K,killed,hx]
  have mass_step (t : ℕ) : stay K a t ≤ stay K a (t+1) + stationaryExit P μ A := by
    have partition (x : S) (hx : x ∉ A) : (∑' y, K x y) + exitRow P A x = 1 := by
      rw [← hP x]
      simp only [K, killed, exitRow, hx, false_or, if_false, ← ENNReal.tsum_add]
      apply tsum_congr
      intro y
      by_cases hy : y ∈ A <;> simp [hy]
    calc stay K a t = ∑' x, (steps K t a x * (∑' y, K x y) + steps K t a x * exitRow P A x) := by
           apply tsum_congr; intro x
           rw [← mul_add]
           by_cases hx : x ∈ A
           · simp [noArrival t x hx]
           · simp [partition x hx]
         _ = stay K a (t+1) + ∑' x, steps K t a x * exitRow P A x := by
           rw [ENNReal.tsum_add]
           congr 1
           simp only [stay, steps_right, compose, ← ENNReal.tsum_mul_left]
           exact ENNReal.tsum_comm
         _ ≤ _ := add_le_add le_rfl (ENNReal.tsum_le_tsum (fun x => mul_le_mul' (bound t x) le_rfl))
  induction n with
  | zero => simp [K,stay,steps,identity]
  | succ n ih =>
    calc (1:ℝ≥0∞) ≤ stay K a n + n * stationaryExit P μ A := ih
         _ ≤ (stay K a (n+1) + stationaryExit P μ A) + n * stationaryExit P μ A :=
           add_le_add (mass_step n) le_rfl
         _ = _ := by push_cast; rw [add_mul,one_mul]; ac_rfl

/-- Quantitative tail-sum bound obtained by adding the first ceil(1/(2b))
survival probabilities. It also covers expected hitting times of infinite value. -/
theorem quarter_flux (u : ℕ → ℝ≥0∞) (b : ℝ) (hb : 0 < b)
    (hu : ∀ n, u n ≤ 1) (hl : ∀ n : ℕ, 1 ≤ u n + n * ENNReal.ofReal b) :
    ENNReal.ofReal (1/(4*b)) ≤ ∑' n, u n := by
  let M := ⌈1 / (2*b)⌉₊
  have low (n : ℕ) (hn : n ∈ range M) : ENNReal.ofReal (1/2) ≤ u n := by
    have hf : u n ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hu n)
    have he : 1 ≤ (u n).toReal + (n:ℝ)*b := by
      have hn' : (n:ℝ≥0∞) * ENNReal.ofReal b ≠ ∞ := ENNReal.mul_ne_top (by simp) (by simp)
      have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf, hn'⟩) (hl n)
      simpa [ENNReal.toReal_add hf hn', ENNReal.toReal_ofReal hb.le] using h
    have hnr : (n:ℝ) < 1/(2*b) := (Nat.lt_ceil.mp (show n < ⌈1/(2*b)⌉₊ from mem_range.mp hn))
    have hnm := (lt_div_iff₀ (by positivity : 0<2*b)).mp hnr
    apply (ENNReal.ofReal_le_iff_le_toReal hf).mpr
    linarith
  have hM : 1/(2*b) ≤ (M : ℝ) := Nat.le_ceil _
  calc ENNReal.ofReal (1/(4*b)) ≤ ENNReal.ofReal ((M:ℝ)*(1/2)) := by
         apply ENNReal.ofReal_le_ofReal
         calc 1/(4*b) = (1/(2*b))*(1/2) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hM (by norm_num)
       _ = ∑ _n ∈ range M, ENNReal.ofReal (1/2) := by
         simp [ENNReal.ofReal_mul (Nat.cast_nonneg M)]
       _ ≤ ∑ n ∈ range M, u n := sum_le_sum low
       _ ≤ ∑' n, u n := ENNReal.sum_le_tsum _

end
end Metropolis.Lower

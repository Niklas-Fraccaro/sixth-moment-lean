import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional Cauchy transfer of a uniform disk remainder

These are genuine complex-analytic estimates, followed by generic asymptotic
transfer lemmas. The input is holomorphy and an undifferentiated uniform bound
on a disk or its boundary. This file does not assert the shifted zeta moment
asymptotic: obtaining its uniform disk remainder remains a separate obligation.

Parameters need not form a finite set. The same constants control all parameters,
including parameters selected as a function of the asymptotic variable.
-/

namespace Sechstmoment

open Filter Metric Asymptotics
open scoped BigOperators

noncomputable section

/-- A finite polynomial in the ordinary complex differentiation operator. -/
def finiteDifferentialOperator (N : ℕ) (q : Fin (N + 1) → ℂ)
    (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  ∑ j : Fin (N + 1), q j * iteratedDeriv j.val f c

/-- Holomorphy on a disk makes every derivative linear on a difference at its center. -/
theorem iteratedDeriv_sub_of_diffContOnCl (n : ℕ) {R : ℝ} {c : ℂ}
    {f g : ℂ → ℂ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hg : DiffContOnCl ℂ g (ball c R)) :
    iteratedDeriv n (fun z => f z - g z) c =
      iteratedDeriv n f c - iteratedDeriv n g c := by
  exact iteratedDeriv_fun_sub
    (hf.differentiableOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))).contDiffAt
    (hg.differentiableOn.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))).contDiffAt

/-- A polynomial differential operator applied to a remainder is the difference of the operators. -/
theorem finiteDifferentialOperator_sub_of_diffContOnCl (N : ℕ)
    (q : Fin (N + 1) → ℂ) {R : ℝ} {c : ℂ} {f g : ℂ → ℂ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hg : DiffContOnCl ℂ g (ball c R)) :
    finiteDifferentialOperator N q (fun z => f z - g z) c =
      finiteDifferentialOperator N q f c - finiteDifferentialOperator N q g c := by
  unfold finiteDifferentialOperator
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDeriv_sub_of_diffContOnCl j.val hR hf hg]
  ring

/-- Cauchy's estimate, with the radius factor separated from the remainder bound. -/
theorem cauchy_iteratedDeriv_bound (n : ℕ) {R M : ℝ} {c : ℂ} {f : ℂ → ℂ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖iteratedDeriv n f c‖ ≤ ((Nat.factorial n : ℝ) / R ^ n) * M := by
  simpa only [div_mul_eq_mul_div, mul_comm M] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hM

/-- A disk bound controls derivatives uniformly on every smaller concentric disk. -/
theorem cauchy_iteratedDeriv_innerDisk_bound (n : ℕ) {R ρ M : ℝ}
    {c : ℂ} {f : ℂ → ℂ} (hρR : ρ < R)
    (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall c ρ,
      ‖iteratedDeriv n f z‖ ≤ ((Nat.factorial n : ℝ) / (R - ρ) ^ n) * M := by
  intro z hz
  have hz' : dist z c ≤ ρ := mem_closedBall.mp hz
  have hs : R - ρ + dist z c ≤ R := by linarith
  apply cauchy_iteratedDeriv_bound n (sub_pos.mpr hρR)
    (hf.mono (ball_subset_ball' hs))
  intro w hw
  exact hM w ((closedBall_subset_closedBall' hs) (sphere_subset_closedBall hw))

/-- Norm estimate for a finite polynomial differential operator. -/
theorem cauchy_finiteDifferentialOperator_bound (N : ℕ)
    {R M : ℝ} {c : ℂ} {f : ℂ → ℂ} (q : Fin (N + 1) → ℂ)
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ‖finiteDifferentialOperator N q f c‖ ≤
      (∑ j : Fin (N + 1), ‖q j‖ * ((Nat.factorial j.val : ℝ) / R ^ j.val)) * M := by
  unfold finiteDifferentialOperator
  calc
    ‖∑ j : Fin (N + 1), q j * iteratedDeriv j.val f c‖ ≤
        ∑ j : Fin (N + 1), ‖q j * iteratedDeriv j.val f c‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin (N + 1),
        ‖q j‖ * (((Nat.factorial j.val : ℝ) / R ^ j.val) * M) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (cauchy_iteratedDeriv_bound j.val hR hf hM) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring

variable {α β : Type*}

/-- The explicit Cauchy constant is uniform over an arbitrary parameter type. -/
theorem uniform_cauchy_iteratedDeriv_bound (n : ℕ) (l : Filter α)
    (f : α → β → ℂ → ℂ) (c : α → β → ℂ) (g : α → ℝ)
    {R C : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ x in l, ∀ p, DiffContOnCl ℂ (f x p) (ball (c x p) R))
    (hM : ∀ᶠ x in l, ∀ p, ∀ z ∈ sphere (c x p) R,
      ‖f x p z‖ ≤ C * ‖g x‖) :
    ∀ᶠ x in l, ∀ p,
      ‖iteratedDeriv n (f x p) (c x p)‖ ≤
        (((Nat.factorial n : ℝ) / R ^ n) * C) * ‖g x‖ := by
  filter_upwards [hf, hM] with x hx hMx
  intro p
  simpa only [mul_assoc] using cauchy_iteratedDeriv_bound n hR (hx p) (hMx p)

/-- Uniform bounds remain big-O bounds after any parameter selection. -/
theorem uniform_cauchy_iteratedDeriv_isBigO (n : ℕ) (l : Filter α)
    (f : α → β → ℂ → ℂ) (c : α → β → ℂ) (g : α → ℝ)
    (p : α → β) {R C : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ x in l, ∀ b, DiffContOnCl ℂ (f x b) (ball (c x b) R))
    (hM : ∀ᶠ x in l, ∀ b, ∀ z ∈ sphere (c x b) R,
      ‖f x b z‖ ≤ C * ‖g x‖) :
    (fun x => iteratedDeriv n (f x (p x)) (c x (p x))) =O[l] g := by
  apply IsBigO.of_bound (((Nat.factorial n : ℝ) / R ^ n) * C)
  exact (uniform_cauchy_iteratedDeriv_bound n l f c g hR hf hM).mono
    (fun x hx => hx (p x))

/-- The same uniform transfer holds throughout any smaller closed disk. -/
theorem uniform_cauchy_innerDisk_bound (n : ℕ) (l : Filter α)
    (f : α → β → ℂ → ℂ) (c : α → β → ℂ) (g : α → ℝ)
    {R ρ C : ℝ} (hρR : ρ < R)
    (hf : ∀ᶠ x in l, ∀ p, DiffContOnCl ℂ (f x p) (ball (c x p) R))
    (hM : ∀ᶠ x in l, ∀ p, ∀ z ∈ closedBall (c x p) R,
      ‖f x p z‖ ≤ C * ‖g x‖) :
    ∀ᶠ x in l, ∀ p, ∀ z ∈ closedBall (c x p) ρ,
      ‖iteratedDeriv n (f x p) z‖ ≤
        (((Nat.factorial n : ℝ) / (R - ρ) ^ n) * C) * ‖g x‖ := by
  filter_upwards [hf, hM] with x hx hMx
  intro p z hz
  simpa only [mul_assoc] using
    cauchy_iteratedDeriv_innerDisk_bound n hρR (hx p) (hMx p) z hz

/-- An eventually bounded family of operator coefficients preserves the uniform error scale. -/
theorem uniform_cauchy_finiteDifferentialOperator_bound (N : ℕ) (l : Filter α)
    (f : α → β → ℂ → ℂ) (c : α → β → ℂ) (g : α → ℝ)
    (q : α → β → Fin (N + 1) → ℂ) (A : Fin (N + 1) → ℝ)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ᶠ x in l, ∀ p, DiffContOnCl ℂ (f x p) (ball (c x p) R))
    (hM : ∀ᶠ x in l, ∀ p, ∀ z ∈ sphere (c x p) R,
      ‖f x p z‖ ≤ C * ‖g x‖)
    (hq : ∀ᶠ x in l, ∀ p, ∀ j, ‖q x p j‖ ≤ A j) :
    ∀ᶠ x in l, ∀ p,
      ‖finiteDifferentialOperator N (q x p) (f x p) (c x p)‖ ≤
        (C * ∑ j : Fin (N + 1), A j * ((Nat.factorial j.val : ℝ) / R ^ j.val)) *
          ‖g x‖ := by
  filter_upwards [hf, hM, hq] with x hx hMx hqx
  intro p
  calc
    _ ≤ (∑ j : Fin (N + 1), ‖q x p j‖ *
        ((Nat.factorial j.val : ℝ) / R ^ j.val)) * (C * ‖g x‖) :=
      cauchy_finiteDifferentialOperator_bound N (q x p) hR (hx p) (hMx p)
    _ ≤ (∑ j : Fin (N + 1), A j *
        ((Nat.factorial j.val : ℝ) / R ^ j.val)) * (C * ‖g x‖) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC (norm_nonneg _))
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hqx p j)
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hR.le _))
    _ = _ := by ring

/-- Polynomial differential operators also preserve big-O after any parameter selection. -/
theorem uniform_cauchy_finiteDifferentialOperator_isBigO (N : ℕ) (l : Filter α)
    (f : α → β → ℂ → ℂ) (c : α → β → ℂ) (g : α → ℝ)
    (q : α → β → Fin (N + 1) → ℂ) (A : Fin (N + 1) → ℝ)
    (p : α → β) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ᶠ x in l, ∀ b, DiffContOnCl ℂ (f x b) (ball (c x b) R))
    (hM : ∀ᶠ x in l, ∀ b, ∀ z ∈ sphere (c x b) R,
      ‖f x b z‖ ≤ C * ‖g x‖)
    (hq : ∀ᶠ x in l, ∀ b, ∀ j, ‖q x b j‖ ≤ A j) :
    (fun x => finiteDifferentialOperator N (q x (p x)) (f x (p x))
      (c x (p x))) =O[l] g := by
  apply IsBigO.of_bound
    (C * ∑ j : Fin (N + 1), A j * ((Nat.factorial j.val : ℝ) / R ^ j.val))
  exact (uniform_cauchy_finiteDifferentialOperator_bound N l f c g q A hR hC hf hM hq).mono
    (fun x hx => hx (p x))

/-- A boundary remainder bounded by `C / log T` transfers to every fixed derivative order.
This is a conditional transfer theorem, not the shifted zeta moment asymptotic. -/
theorem uniform_cauchy_iteratedDeriv_invLog_isBigO (n : ℕ)
    (f : ℝ → β → ℂ → ℂ) (c : ℝ → β → ℂ) (p : ℝ → β)
    {R C : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (f T b) (ball (c T b) R))
    (hM : ∀ᶠ T in atTop, ∀ b, ∀ z ∈ sphere (c T b) R,
      ‖f T b z‖ ≤ C / Real.log T) :
    (fun T => iteratedDeriv n (f T (p T)) (c T (p T))) =O[atTop]
      (fun T => (Real.log T)⁻¹) := by
  apply uniform_cauchy_iteratedDeriv_isBigO n atTop f c
    (fun T => (Real.log T)⁻¹) p hR hf
  filter_upwards [hM, eventually_gt_atTop (1 : ℝ)] with T hMT hT
  intro b z hz
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_pos hT).le)]
  simpa only [div_eq_mul_inv] using hMT b z hz

/-- The inverse-logarithmic remainder also survives any uniformly bounded finite operator. -/
theorem uniform_cauchy_finiteDifferentialOperator_invLog_isBigO (N : ℕ)
    (f : ℝ → β → ℂ → ℂ) (c : ℝ → β → ℂ)
    (q : ℝ → β → Fin (N + 1) → ℂ) (A : Fin (N + 1) → ℝ) (p : ℝ → β)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (f T b) (ball (c T b) R))
    (hM : ∀ᶠ T in atTop, ∀ b, ∀ z ∈ sphere (c T b) R,
      ‖f T b z‖ ≤ C / Real.log T)
    (hq : ∀ᶠ T in atTop, ∀ b, ∀ j, ‖q T b j‖ ≤ A j) :
    (fun T => finiteDifferentialOperator N (q T (p T)) (f T (p T))
      (c T (p T))) =O[atTop] (fun T => (Real.log T)⁻¹) := by
  apply uniform_cauchy_finiteDifferentialOperator_isBigO N atTop f c
    (fun T => (Real.log T)⁻¹) q A p hR hC hf _ hq
  filter_upwards [hM, eventually_gt_atTop (1 : ℝ)] with T hMT hT
  intro b z hz
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_pos hT).le)]
  simpa only [div_eq_mul_inv] using hMT b z hz

/-- Transfer from an undifferentiated uniform `actual - main` remainder to derivative differences. -/
theorem uniform_cauchy_iteratedDeriv_sub_invLog_isBigO (n : ℕ)
    (f main : ℝ → β → ℂ → ℂ) (c : ℝ → β → ℂ) (p : ℝ → β)
    {R C : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (f T b) (ball (c T b) R))
    (hmain : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (main T b) (ball (c T b) R))
    (hM : ∀ᶠ T in atTop, ∀ b, ∀ z ∈ sphere (c T b) R,
      ‖f T b z - main T b z‖ ≤ C / Real.log T) :
    (fun T => iteratedDeriv n (f T (p T)) (c T (p T)) -
      iteratedDeriv n (main T (p T)) (c T (p T))) =O[atTop]
        (fun T => (Real.log T)⁻¹) := by
  have hrem : ∀ᶠ T in atTop, ∀ b,
      DiffContOnCl ℂ (fun z => f T b z - main T b z) (ball (c T b) R) := by
    filter_upwards [hf, hmain] with T hTf hTm
    exact fun b => (hTf b).sub (hTm b)
  have h := uniform_cauchy_iteratedDeriv_invLog_isBigO n
    (fun T b z => f T b z - main T b z) c p hR hrem hM
  apply h.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hf, hmain] with T hTf hTm
  exact iteratedDeriv_sub_of_diffContOnCl n hR (hTf (p T)) (hTm (p T))

/-- Transfer of the same undifferentiated remainder to differences of finite operators. -/
theorem uniform_cauchy_finiteDifferentialOperator_sub_invLog_isBigO (N : ℕ)
    (f main : ℝ → β → ℂ → ℂ) (c : ℝ → β → ℂ)
    (q : ℝ → β → Fin (N + 1) → ℂ) (A : Fin (N + 1) → ℝ) (p : ℝ → β)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (f T b) (ball (c T b) R))
    (hmain : ∀ᶠ T in atTop, ∀ b, DiffContOnCl ℂ (main T b) (ball (c T b) R))
    (hM : ∀ᶠ T in atTop, ∀ b, ∀ z ∈ sphere (c T b) R,
      ‖f T b z - main T b z‖ ≤ C / Real.log T)
    (hq : ∀ᶠ T in atTop, ∀ b, ∀ j, ‖q T b j‖ ≤ A j) :
    (fun T => finiteDifferentialOperator N (q T (p T)) (f T (p T)) (c T (p T)) -
      finiteDifferentialOperator N (q T (p T)) (main T (p T)) (c T (p T))) =O[atTop]
        (fun T => (Real.log T)⁻¹) := by
  have hrem : ∀ᶠ T in atTop, ∀ b,
      DiffContOnCl ℂ (fun z => f T b z - main T b z) (ball (c T b) R) := by
    filter_upwards [hf, hmain] with T hTf hTm
    exact fun b => (hTf b).sub (hTm b)
  have h := uniform_cauchy_finiteDifferentialOperator_invLog_isBigO N
    (fun T b z => f T b z - main T b z) c q A p hR hC hrem hM hq
  apply h.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hf, hmain] with T hTf hTm
  exact finiteDifferentialOperator_sub_of_diffContOnCl N (q T (p T)) hR
    (hTf (p T)) (hTm (p T))

end

end Sechstmoment

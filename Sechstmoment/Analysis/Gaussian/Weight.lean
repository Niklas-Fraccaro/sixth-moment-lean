import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace Sechstmoment
open MeasureTheory Set Filter Real
open scoped Topology
noncomputable section

def d02GaussianTail (u : ℝ) : ℝ :=
  (∫ v in Ioi u, Real.exp (-v^2)) / Real.sqrt Real.pi

def d02Erfc (u : ℝ) : ℝ := 2*d02GaussianTail u

def d02GaussianV0 (x : ℝ) : ℝ := d02GaussianTail (Real.log x/2)

def d02GaussianLogWeight (L q c : ℝ) : ℝ :=
  d02GaussianTail ((L*(q-1)+c)/2)

theorem d02Gaussian_integrable : Integrable (fun v : ℝ => Real.exp (-v^2)) := by
  simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)

theorem d02Gaussian_total_mass :
    (∫ v : ℝ, Real.exp (-v^2)) = Real.sqrt Real.pi := by
  simpa using integral_gaussian (1 : ℝ)

theorem d02GaussianTail_nonneg (u : ℝ) : 0 ≤ d02GaussianTail u := by
  unfold d02GaussianTail
  exact div_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.sqrt_nonneg _)

theorem d02GaussianTail_le_one (u : ℝ) : d02GaussianTail u ≤ 1 := by
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold d02GaussianTail
  rw [div_le_iff₀ hp, one_mul, ← d02Gaussian_total_mass]
  exact setIntegral_le_integral d02Gaussian_integrable
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le))

theorem d02GaussianTail_reflection (u : ℝ) :
    d02GaussianTail (-u) = 1-d02GaussianTail u := by
  have hs : (∫ v in Ioi (-u), Real.exp (-v^2)) =
      ∫ v in Iic u, Real.exp (-v^2) := by
    calc
      _ = ∫ v in Ioi (-u), Real.exp (-(-v)^2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        exact congrArg Real.exp (by ring : -(v^2) = -((-v)^2))
      _ = _ := by
        convert integral_comp_neg_Ioi (-u) (fun v : ℝ => Real.exp (-v^2)) using 1
        simp
  have hc := integral_add_compl (s := Ioi u) measurableSet_Ioi d02Gaussian_integrable
  have hc' : (∫ v in Ioi u, Real.exp (-v^2)) +
      (∫ v in Iic u, Real.exp (-v^2)) = Real.sqrt Real.pi := by
    simpa only [compl_Ioi, d02Gaussian_total_mass] using hc
  unfold d02GaussianTail
  rw [hs]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
  linarith

@[simp] theorem d02GaussianTail_zero : d02GaussianTail 0 = 1/2 := by
  have h := d02GaussianTail_reflection 0
  simp only [neg_zero] at h
  linarith

@[simp] theorem d02GaussianV0_one : d02GaussianV0 1 = 1/2 := by
  simp [d02GaussianV0]

theorem d02GaussianV0_eq_erfc (x : ℝ) :
    d02GaussianV0 x = (1/2)*d02Erfc (Real.log x/2) := by
  simp [d02GaussianV0, d02Erfc]

theorem d02GaussianTail_antitone : Antitone d02GaussianTail := by
  intro u v huv
  unfold d02GaussianTail
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact setIntegral_mono_set d02Gaussian_integrable.integrableOn
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
    (Eventually.of_forall (fun x hx => lt_of_le_of_lt huv hx))

theorem d02GaussianTail_gaussian_bound {u : ℝ} (hu : 0 ≤ u) :
    d02GaussianTail u ≤ (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*
      Real.exp (-(1/2)*u^2) := by
  let g : ℝ → ℝ := fun v => Real.exp (-(1/2)*u^2)*Real.exp (-(1/2)*v^2)
  have hgi : Integrable g :=
    (integrable_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul _
  have hpt : ∀ v ∈ Ioi u, Real.exp (-v^2) ≤ g v := by
    intro v hv
    dsimp [g]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hv' : u < v := hv
    nlinarith
  have hi : (∫ v in Ioi u, Real.exp (-v^2)) ≤
      Real.exp (-(1/2)*u^2)*Real.sqrt (2*Real.pi) := by
    calc
      _ ≤ ∫ v in Ioi u, g v := setIntegral_mono_on
        d02Gaussian_integrable.integrableOn hgi.integrableOn measurableSet_Ioi hpt
      _ ≤ ∫ v : ℝ, g v := setIntegral_le_integral hgi
        (Eventually.of_forall (fun v => by dsimp [g]; positivity))
      _ = _ := by
        rw [integral_const_mul, integral_gaussian]
        congr 2
        ring
  unfold d02GaussianTail
  calc
    _ ≤ (Real.exp (-(1/2)*u^2)*Real.sqrt (2*Real.pi))/Real.sqrt Real.pi :=
      div_le_div_of_nonneg_right hi (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem d02GaussianTail_tendsto_zero :
    Tendsto d02GaussianTail atTop (𝓝 0) := by
  have ht : Tendsto (fun u : ℝ => ∫ v in Ioi u, Real.exp (-v^2)) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  change Tendsto (fun u : ℝ => (∫ v in Ioi u, Real.exp (-v^2))/Real.sqrt Real.pi) atTop (𝓝 0)
  simpa only [zero_div] using ht.div_const (Real.sqrt Real.pi)

theorem d02GaussianTail_tendsto_one :
    Tendsto d02GaussianTail atBot (𝓝 1) := by
  have ht := d02GaussianTail_tendsto_zero.comp tendsto_neg_atBot_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  convert h using 1
  · ext u
    change d02GaussianTail u = 1-d02GaussianTail (-u)
    rw [d02GaussianTail_reflection]
    ring
  · norm_num

theorem d02GaussianLogWeight_below_cut {q : ℝ} (hq : q < 1) (c : ℝ) :
    Tendsto (fun L : ℝ => d02GaussianLogWeight L q c) atTop (𝓝 1) := by
  apply d02GaussianTail_tendsto_one.comp
  exact (tendsto_atBot_add_const_right atTop c
    (tendsto_id.atTop_mul_const_of_neg (by linarith : q-1 < 0))).atBot_div_const (by norm_num : (0 : ℝ)<2)

theorem d02GaussianLogWeight_above_cut {q : ℝ} (hq : 1 < q) (c : ℝ) :
    Tendsto (fun L : ℝ => d02GaussianLogWeight L q c) atTop (𝓝 0) := by
  apply d02GaussianTail_tendsto_zero.comp
  exact (tendsto_atTop_add_const_right atTop c
    (tendsto_id.atTop_mul_const (by linarith : 0 < q-1))).atTop_div_const (by norm_num : (0 : ℝ)<2)

theorem d02GaussianV0_logarithmic_identity (L q : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    d02GaussianV0 (2*Real.pi*Real.exp (L*q)/(Real.exp L*τ)) =
      d02GaussianLogWeight L q (Real.log (2*Real.pi/τ)) := by
  unfold d02GaussianV0 d02GaussianLogWeight
  congr 1
  rw [Real.log_div (by positivity : 2*Real.pi*Real.exp (L*q) ≠ 0)
    (by positivity : Real.exp L*τ ≠ 0),
    Real.log_mul (by positivity : 2*Real.pi ≠ 0) (Real.exp_ne_zero _),
    Real.log_mul (Real.exp_ne_zero _) hτ.ne',
    Real.log_exp, Real.log_exp,
    Real.log_div (by positivity : 2*Real.pi ≠ 0) hτ.ne']
  ring


theorem d02GaussianLogWeight_uniform_above {η ε C : ℝ}
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ q c : ℝ, 1+η ≤ q → |c| ≤ C →
      d02GaussianLogWeight L q c < ε := by
  have ht : Tendsto (fun L : ℝ => d02GaussianTail ((L*η-C)/2)) atTop (𝓝 0) := by
    apply d02GaussianTail_tendsto_zero.comp
    exact (tendsto_atTop_add_const_right atTop (-C)
      (tendsto_id.atTop_mul_const hη)).atTop_div_const (by norm_num)
  filter_upwards [ht.eventually_lt_const hε, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro q c hq hc
  apply lt_of_le_of_lt (d02GaussianTail_antitone ?_) hL
  have hc' := (abs_le.mp hc).1
  change (L*η-C)/2 ≤ (L*(q-1)+c)/2
  nlinarith

theorem d02GaussianLogWeight_uniform_below {η ε C : ℝ}
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ q c : ℝ, q ≤ 1-η → |c| ≤ C →
      1-ε < d02GaussianLogWeight L q c := by
  filter_upwards [d02GaussianLogWeight_uniform_above (C := C) hη hε] with L hL
  intro q c hq hc
  have h := hL (2-q) (-c) (by linarith) (by simpa using hc)
  have he : d02GaussianLogWeight L (2-q) (-c) =
      1-d02GaussianLogWeight L q c := by
    unfold d02GaussianLogWeight
    rw [show (L*(2-q-1)+(-c))/2 = -((L*(q-1)+c)/2) by ring,
      d02GaussianTail_reflection]
  rw [he] at h
  linarith

theorem d02GaussianLogWeight_exponential_tail {C L q c : ℝ}
    (hC : 0 ≤ C) (hL : 8+2*C ≤ L) (hq : 2 ≤ q) (hc : |c| ≤ C) :
    Real.exp (C*q)*d02GaussianLogWeight L q c ≤
      (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (C^2)*Real.exp (-q^2) := by
  let u := (L*(q-1)+c)/2
  have hu : 2*q ≤ u := by
    have hc' := (abs_le.mp hc).1
    have hprod : (8+2*C)*(q-1) ≤ L*(q-1) :=
      mul_le_mul_of_nonneg_right hL (by linarith)
    dsimp [u]
    nlinarith
  have hu0 : 0 ≤ u := by linarith
  have ht := d02GaussianTail_gaussian_bound hu0
  have hexp : Real.exp (C*q-(1/2)*u^2) ≤ Real.exp (C^2-q^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (C-q/2), sq_nonneg q]
  unfold d02GaussianLogWeight
  change Real.exp (C*q)*d02GaussianTail u ≤ _
  calc
    _ ≤ Real.exp (C*q)*((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*
      Real.exp (-(1/2)*u^2)) := mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*
      Real.exp (C*q-(1/2)*u^2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 1
        ring
    _ ≤ (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (C^2-q^2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1


theorem d02GaussianV0_power_bound {x : ℝ} (hx : 1 ≤ x) (A : ℝ) :
    d02GaussianV0 x ≤
      (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*x^(-A) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have ht := d02GaussianTail_gaussian_bound (show 0 ≤ Real.log x/2 by positivity)
  have he : Real.exp (-(1/2)*(Real.log x/2)^2) ≤
      Real.exp (2*A^2)*x^(-A) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (Real.log x-4*A)]
  unfold d02GaussianV0
  apply ht.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
    (show 0 ≤ Real.sqrt (2*Real.pi)/Real.sqrt Real.pi by positivity)

theorem d02Erfc_log_power_bound {x : ℝ} (hx : 1 ≤ x) (A : ℝ) :
    d02Erfc (Real.log x/2) ≤
      2*((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2))*x^(-A) := by
  have h := mul_le_mul_of_nonneg_left (d02GaussianV0_power_bound hx A) (by norm_num : (0 : ℝ)≤2)
  simpa only [d02GaussianV0, d02Erfc, mul_assoc] using h


theorem d02GaussianV0_power_bound_all {x A : ℝ} (hx : 0 < x) (hA : 0 ≤ A) :
    d02GaussianV0 x ≤
      (1+(Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2))*x^(-A) := by
  by_cases hx1 : 1 ≤ x
  · exact (d02GaussianV0_power_bound hx1 A).trans (by gcongr; linarith)
  · have hp : 1 ≤ x^(-A) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx (by linarith) (by linarith)
    have hC : 0 ≤ (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2) := by positivity
    have hv := d02GaussianTail_le_one (Real.log x/2)
    change d02GaussianV0 x ≤ 1 at hv
    exact hv.trans (by nlinarith)

end
end Sechstmoment

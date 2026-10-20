import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic.GCongr
import SixthMoment.Analysis.Profiles.Classes
import SixthMoment.Zeta.Centering.Uniform
import SixthMoment.Zeta.Moments.Definitions

namespace SixthMoment
open Complex Filter Metric
open scoped BigOperators Topology ComplexConjugate
noncomputable section

theorem zetaChi_conj (s : ℂ) : zetaChi (conj s) = conj (zetaChi s) := by
  simp [zetaChi, ← gammaReal_conj]

theorem centeringFactorAt_conj (T : ℝ) (s z : ℂ) :
    centeringFactorAt T (conj s) (conj z) = conj (centeringFactorAt T s z) := by
  simp [centeringFactorAt, ← zetaChi_conj, Complex.exp_conj]

def lowerCenteringFactor (T : ℝ) (x z : ℂ) : ℂ :=
  centeringFactorAt T (1-complexHeightPoint T x) z

def dpCenteringPairError (T : ℝ) (x z w : ℂ) : ℂ :=
  lowerCenteringFactor T x z*lowerCenteringFactor T x w-1

def dpCenteredArchimedeanCorrection (T t : ℝ) (σ : MomentShifts) : ℂ :=
  Complex.exp (σ 2+σ 3)*dpArchimedeanCorrection t (rawMomentShifts T σ)

theorem lowerCenteringFactor_eq_conj (T : ℝ) (x z : ℂ) :
    lowerCenteringFactor T x z =
      conj (centeringFactorAt T (complexHeightPoint T (conj x)) (conj z)) := by
  have hp : conj (complexHeightPoint T (conj x)) = 1-complexHeightPoint T x := by
    simp [complexHeightPoint, map_ofNat]
    ring
  rw [← centeringFactorAt_conj, hp, Complex.conj_conj]
  rfl

theorem dpCenteredArchimedeanCorrection_eq_pair (T x : ℝ) (σ : MomentShifts) :
    dpCenteredArchimedeanCorrection T (T*x) σ-1 =
      dpCenteringPairError T (x : ℂ) (σ 2) (σ 3) := by
  have hp : complexHeightPoint T (x : ℂ) = criticalLinePoint (T*x) := by
    unfold complexHeightPoint criticalLinePoint
    push_cast
    ring
  unfold dpCenteredArchimedeanCorrection dpArchimedeanCorrection dpCenteringPairError
    lowerCenteringFactor centeringFactorAt rawMomentShifts
  rw [hp, Complex.exp_add]
  ring

theorem lowerCenteringFactor_uniform_complex_height_bound (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x z : ℂ,
      x.re ∈ Set.Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 → ‖z‖ ≤ R →
      ‖lowerCenteringFactor T x z-1‖ ≤ centeringUniformConstant R/Real.log T := by
  filter_upwards [centeringFactorAt_uniform_complex_height_bound R] with T hT
  intro x z hxre hxim hz
  rw [lowerCenteringFactor_eq_conj]
  have hh := hT (conj x) (conj z) (by simpa using hxre) (by simpa using hxim)
    (by simpa using hz)
  rw [show conj (centeringFactorAt T (complexHeightPoint T (conj x)) (conj z))-1 =
    conj (centeringFactorAt T (complexHeightPoint T (conj x)) (conj z)-1) by simp,
    Complex.norm_conj]
  exact hh

theorem dpCenteringPairError_uniform_complex_height_bound {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ x z w : ℂ,
      x.re ∈ Set.Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 → ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖dpCenteringPairError T x z w‖ ≤ 3*centeringUniformConstant R/Real.log T := by
  have hC : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop
    (max 1 (centeringUniformConstant R)))
  filter_upwards [lowerCenteringFactor_uniform_complex_height_bound R, hlog] with T hT hL
  intro x z w hxre hxim hz hw
  have hLpos : 0 < Real.log T := by linarith [(le_max_left (1 : ℝ) _).trans hL]
  have hCL : centeringUniformConstant R/Real.log T ≤ 1 := by
    rw [div_le_iff₀ hLpos]
    simpa using (le_max_right (1 : ℝ) _).trans hL
  have hbz := hT x z hxre hxim hz
  have hbw := hT x w hxre hxim hw
  have hnw : ‖lowerCenteringFactor T x w‖ ≤ 2 := by
    have hh : ‖lowerCenteringFactor T x w‖ ≤ ‖lowerCenteringFactor T x w-1‖+1 := by
      convert norm_add_le (lowerCenteringFactor T x w-1) (1 : ℂ) using 1 <;> simp
    linarith
  have he : dpCenteringPairError T x z w =
      (lowerCenteringFactor T x z-1)*lowerCenteringFactor T x w+
        (lowerCenteringFactor T x w-1) := by unfold dpCenteringPairError; ring
  rw [he]
  calc
    _ ≤ ‖(lowerCenteringFactor T x z-1)*lowerCenteringFactor T x w‖+
        ‖lowerCenteringFactor T x w-1‖ := norm_add_le _ _
    _ ≤ (centeringUniformConstant R/Real.log T)*2+
        centeringUniformConstant R/Real.log T := by rw [norm_mul]; gcongr
    _ = _ := by ring


theorem lowerCenteringFactor_analyticAt_height (T : ℝ) (z : ℂ) {x : ℂ}
    (hs : (1-complexHeightPoint T x).im ≠ 0)
    (hw : (1-complexHeightPoint T x+z/(Real.log T : ℂ)).im ≠ 0) :
    AnalyticAt ℂ (fun y : ℂ => lowerCenteringFactor T y z) x := by
  have ha : AnalyticAt ℂ (fun y : ℂ => 1-complexHeightPoint T y) x := by
    unfold complexHeightPoint
    fun_prop
  exact (centeringFactorAt_analyticAt_base T z hs hw).comp
    (f := fun y : ℂ => 1-complexHeightPoint T y) ha

private theorem lowerCenteringFactor_nonreal {T R : ℝ} {x z : ℂ}
    (hxre : 3/4 ≤ x.re) (hz : ‖z‖ ≤ R) (hL : 1 ≤ Real.log T)
    (hT : 192*(R+R^2)+8 ≤ T) :
    (1-complexHeightPoint T x).im ≠ 0 ∧
      (1-complexHeightPoint T x+z/(Real.log T : ℂ)).im ≠ 0 := by
  have hh := complexHeightPoint_shift_nonreal (x := conj x) (z := conj z)
    (by simpa using hxre) (by simpa using hz) hL hT
  have hp : conj (complexHeightPoint T (conj x)) = 1-complexHeightPoint T x := by
    simp [complexHeightPoint, map_ofNat]
    ring
  have hpz : conj (complexHeightPoint T (conj x)+conj z/(Real.log T : ℂ)) =
      1-complexHeightPoint T x+z/(Real.log T : ℂ) := by
    simp [hp]
  constructor
  · rw [← hp]
    simpa only [Complex.conj_im, neg_ne_zero] using hh.1
  · rw [← hpz]
    simpa only [Complex.conj_im, neg_ne_zero] using hh.2

private theorem dpCentering_quarter_ball_window {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) {y : ℂ} (hy : y ∈ closedBall (x : ℂ) (1/4 : ℝ)) :
    y.re ∈ Set.Icc (3/4 : ℝ) (9/4) ∧ |y.im| ≤ 1/4 := by
  have hn : ‖y-(x : ℂ)‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hre := (Complex.abs_re_le_norm (y-(x : ℂ))).trans hn
  have him := (Complex.abs_im_le_norm (y-(x : ℂ))).trans hn
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  exact ⟨⟨by linarith [(abs_le.mp hre).1, hx.1],
    by linarith [(abs_le.mp hre).2, hx.2]⟩, him⟩

theorem dpCenteringPairError_uniform_real_derivative_bound (n : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      ∀ z w : ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖iteratedDeriv n (fun y : ℝ => dpCenteringPairError T (y : ℂ) z w) x‖ ≤
          ((Nat.factorial n : ℝ)/(1/4 : ℝ)^n)*
            (3*centeringUniformConstant R/Real.log T) := by
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [dpCenteringPairError_uniform_complex_height_bound hR, hlog,
    eventually_ge_atTop (192*(R+R^2)+8)] with T hbound hL hT
  intro x hx z w hz hw
  let f : ℂ → ℂ := fun y => dpCenteringPairError T y z w
  have ha : AnalyticOnNhd ℂ f (closedBall (x : ℂ) (1/4 : ℝ)) := by
    intro y hy
    have hwindow := dpCentering_quarter_ball_window hx hy
    have hzn := lowerCenteringFactor_nonreal hwindow.1.1 hz hL hT
    have hwn := lowerCenteringFactor_nonreal hwindow.1.1 hw hL hT
    exact ((lowerCenteringFactor_analyticAt_height T z hzn.1 hzn.2).mul
      (lowerCenteringFactor_analyticAt_height T w hwn.1 hwn.2)).sub analyticAt_const
  have hf : DiffContOnCl ℂ f (ball (x : ℂ) (1/4 : ℝ)) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  apply cauchy_real_iteratedDeriv_bound n (by norm_num) hf
  intro y hy
  have hwindow := dpCentering_quarter_ball_window hx (sphere_subset_closedBall hy)
  exact hbound y z w hwindow.1 hwindow.2 hz hw


private theorem centeringFactorAt_analyticAt_base_strip (T : ℝ) (z : ℂ) {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1)
    (hw : 0 < (s+z/(Real.log T : ℂ)).re ∧ (s+z/(Real.log T : ℂ)).re < 1) :
    AnalyticAt ℂ (fun v : ℂ => centeringFactorAt T v z) s := by
  have ha : AnalyticAt ℂ (fun v : ℂ => v+z/(Real.log T : ℂ)) s := by fun_prop
  have hn := (zetaChi_analyticOnNhd_strip _ hw).comp
    (f := fun v : ℂ => v+z/(Real.log T : ℂ)) ha
  exact (analyticAt_const.mul hn).div (zetaChi_analyticOnNhd_strip _ hs)
    (zetaChi_ne_zero_strip hs.1 hs.2)

private theorem lowerCenteringFactor_analyticAt_real_height {T : ℝ}
    (hL : 0 < Real.log T) (z : ℂ) (hz : 2*‖z‖ < Real.log T) (x : ℝ) :
    AnalyticAt ℂ (fun y : ℂ => lowerCenteringFactor T y z) (x : ℂ) := by
  have hp : 1-complexHeightPoint T (x : ℂ) = criticalLinePoint (-(T*x)) := by
    unfold complexHeightPoint criticalLinePoint
    push_cast
    ring
  have hw := centeringShift_mem_strip hL (-(T*x)) z hz
  have hs : 0 < (1-complexHeightPoint T (x : ℂ)).re ∧
      (1-complexHeightPoint T (x : ℂ)).re < 1 := by rw [hp]; norm_num
  have hws : 0 < (1-complexHeightPoint T (x : ℂ)+z/(Real.log T : ℂ)).re ∧
      (1-complexHeightPoint T (x : ℂ)+z/(Real.log T : ℂ)).re < 1 := by
    simpa only [hp, centeringShift] using hw
  have ha : AnalyticAt ℂ (fun y : ℂ => 1-complexHeightPoint T y) (x : ℂ) := by
    unfold complexHeightPoint
    fun_prop
  exact (centeringFactorAt_analyticAt_base_strip T z hs hws).comp
    (f := fun y : ℂ => 1-complexHeightPoint T y) ha

theorem dpCenteringPairError_contDiff_real_height {T : ℝ}
    (hL : 0 < Real.log T) (z w : ℂ)
    (hz : 2*‖z‖ < Real.log T) (hw : 2*‖w‖ < Real.log T) :
    ContDiff ℝ ⊤ (fun x : ℝ => dpCenteringPairError T (x : ℂ) z w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have ha : AnalyticAt ℂ (fun y : ℂ => dpCenteringPairError T y z w) (x : ℂ) :=
    ((lowerCenteringFactor_analyticAt_real_height hL z hz x).mul
      (lowerCenteringFactor_analyticAt_real_height hL w hw x)).sub analyticAt_const
  exact (ha.contDiffAt.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt

def dpCenteringErrorWeight (T : ℝ) (Φ : ℝ → ℝ) (z w : ℂ)
    (ℓ : ℂ →L[ℝ] ℝ) (x : ℝ) : ℝ :=
  Φ x*(Real.log T*ℓ (dpCenteringPairError T (x : ℂ) z w))

theorem dpCenteringErrorWeight_smooth {T : ℝ} {Φ : ℝ → ℝ}
    (hΦ : SmoothDyadicWeight Φ) (hL : 0 < Real.log T) (z w : ℂ)
    (hz : 2*‖z‖ < Real.log T) (hw : 2*‖w‖ < Real.log T)
    (ℓ : ℂ →L[ℝ] ℝ) : SmoothDyadicWeight (dpCenteringErrorWeight T Φ z w ℓ) := by
  constructor
  · exact hΦ.1.mul (contDiff_const.mul (ℓ.contDiff.comp
      ((dpCenteringPairError_contDiff_real_height hL z w hz hw).of_le (by simp))))
  · exact (tsupport_mul_subset_left (f := Φ)
      (g := fun x => Real.log T*ℓ (dpCenteringPairError T (x : ℂ) z w))).trans hΦ.2


theorem dpCenteringErrorWeight_uniform_deriv_bound {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ →
      WeightSeminormBound 1 B Φ → ∀ z w : ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ∀ ℓ : ℂ →L[ℝ] ℝ, ‖ℓ‖ ≤ 1 → ∀ x : ℝ,
        ‖deriv (dpCenteringErrorWeight T Φ z w ℓ) x‖ ≤
          15*B*centeringUniformConstant R := by
  have hC : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hlog := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (max 0 (2*R)))
  filter_upwards [dpCenteringPairError_uniform_real_derivative_bound 0 hR,
    dpCenteringPairError_uniform_real_derivative_bound 1 hR, hlog]
    with T herr0 herr1 hL
  intro Φ hΦ hΦB z w hz hw ℓ hℓ x
  have hLpos : 0 < Real.log T := (le_max_left _ _).trans_lt hL
  have hzstrip : 2*‖z‖ < Real.log T :=
    (mul_le_mul_of_nonneg_left hz (by norm_num)).trans_lt ((le_max_right _ _).trans_lt hL)
  have hwstrip : 2*‖w‖ < Real.log T :=
    (mul_le_mul_of_nonneg_left hw (by norm_num)).trans_lt ((le_max_right _ _).trans_lt hL)
  have hW := dpCenteringErrorWeight_smooth hΦ hLpos z w hzstrip hwstrip ℓ
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · let E : ℝ → ℂ := fun y => dpCenteringPairError T (y : ℂ) z w
    have hE : DifferentiableAt ℝ E x :=
      (dpCenteringPairError_contDiff_real_height hLpos z w hzstrip hwstrip).differentiable
        (by simp) x
    have heder : deriv (fun y => ℓ (E y)) x = ℓ (deriv E x) :=
      (ℓ.hasFDerivAt.comp_hasDerivAt x hE.hasDerivAt).deriv
    have hl (v : ℂ) : ‖ℓ v‖ ≤ ‖v‖ := by
      apply (ℓ.le_opNorm v).trans
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hℓ (norm_nonneg v)
    have h0 : ‖E x‖ ≤ 3*centeringUniformConstant R/Real.log T := by
      simpa only [E, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero,
        div_one, one_mul] using herr0 x hx z w hz hw
    have h1 : ‖deriv E x‖ ≤ 12*centeringUniformConstant R/Real.log T := by
      have hh := herr1 x hx z w hz hw
      simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one] at hh
      convert hh using 1; ring
    have hΦ0 : ‖Φ x‖ ≤ B := by simpa using hΦB 0 (by omega) x
    have hΦ1 : ‖deriv Φ x‖ ≤ B := by simpa using hΦB 1 (by omega) x
    have hΦd : DifferentiableAt ℝ Φ x := hΦ.1.differentiable (by simp) x
    have hℓd : DifferentiableAt ℝ (fun y => ℓ (E y)) x :=
      ℓ.differentiableAt.comp x hE
    change ‖deriv (fun y => Φ y*(Real.log T*ℓ (E y))) x‖ ≤ _
    rw [deriv_fun_mul hΦd (hℓd.const_mul _), deriv_const_mul_field, heder]
    calc
      _ ≤ ‖deriv Φ x*(Real.log T*ℓ (E x))‖+
          ‖Φ x*(Real.log T*ℓ (deriv E x))‖ := norm_add_le _ _
      _ ≤ B*(Real.log T*(3*centeringUniformConstant R/Real.log T))+
          B*(Real.log T*(12*centeringUniformConstant R/Real.log T)) := by
        simp only [norm_mul, Real.norm_of_nonneg hLpos.le]
        gcongr <;> first | exact hΦ0 | exact hΦ1 | exact (hl _).trans h0 | exact (hl _).trans h1
      _ = _ := by field_simp; ring
  · have hxt : x ∉ tsupport (dpCenteringErrorWeight T Φ z w ℓ) := fun h => hx (hW.2 h)
    rw [deriv_of_notMem_tsupport hxt, norm_zero]
    positivity


theorem dpCenteringErrorWeight_uniform_norm_bound {R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ →
      WeightSeminormBound 1 B Φ → ∀ z w : ℂ, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ∀ ℓ : ℂ →L[ℝ] ℝ, ‖ℓ‖ ≤ 1 → ∀ x : ℝ,
        ‖dpCenteringErrorWeight T Φ z w ℓ x‖ ≤ 3*B*centeringUniformConstant R := by
  have hC : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  filter_upwards [dpCenteringPairError_uniform_real_derivative_bound 0 hR,
    eventually_gt_atTop (1 : ℝ)] with T herr hT
  intro Φ hΦ hΦB z w hz hw ℓ hℓ x
  have hLpos := Real.log_pos hT
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · have he : ‖dpCenteringPairError T (x : ℂ) z w‖ ≤
        3*centeringUniformConstant R/Real.log T := by
      simpa using herr x hx z w hz hw
    have hl : ‖ℓ (dpCenteringPairError T (x : ℂ) z w)‖ ≤
        3*centeringUniformConstant R/Real.log T := by
      apply (ℓ.le_opNorm _).trans
      calc
        _ ≤ 1*‖dpCenteringPairError T (x : ℂ) z w‖ :=
          mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
        _ ≤ _ := by simpa using he
    have hΦ0 : ‖Φ x‖ ≤ B := by simpa using hΦB 0 (by omega) x
    unfold dpCenteringErrorWeight
    simp only [norm_mul, Real.norm_of_nonneg hLpos.le]
    calc
      _ ≤ B*(Real.log T*(3*centeringUniformConstant R/Real.log T)) := by gcongr
      _ = _ := by field_simp
  · have hzΦ : Φ x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ.2 h))
    simp only [dpCenteringErrorWeight, hzΦ, zero_mul, norm_zero]
    positivity

end
end SixthMoment

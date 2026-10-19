import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The actual complex Laplace primitive for the damped cosine Mellin
calculation.  Its continuation in the Laplace parameter follows from genuine
dominated differentiation and the analytic identity principle. -/

namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

/-- Positive real Laplace majorants, including those used for the parameter
derivative, are integrable on the whole positive half-line. -/
theorem a03LaplaceRealMajorant_integrable {σ c : ℝ} (hσ : 0<σ) (hc : 0<c) :
    IntegrableOn (fun u : ℝ => u^(σ-1)*Real.exp (-c*u)) (Ioi 0) := by
  have hbase := Real.GammaIntegral_convergent hσ
  have hcomp : IntegrableOn
      (fun u : ℝ => Real.exp (-(c*u))*(c*u)^(σ-1)) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x)*x^(σ-1)) 0 hc).mpr (by simpa only [mul_zero] using hbase)
  apply (hcomp.const_mul (c^(1-σ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0<u := hu
  have hcc : c^(1-σ)*c^(σ-1)=1 := by
    rw [←Real.rpow_add hc,show 1-σ+(σ-1)=0 by ring,Real.rpow_zero]
  rw [Real.mul_rpow hc.le hu0.le]
  calc
    c^(1-σ)*(Real.exp (-(c*u))*(c^(σ-1)*u^(σ-1)))=
      (c^(1-σ)*c^(σ-1))*(u^(σ-1)*Real.exp (-c*u)) := by
        rw [neg_mul]
        ring
    _ = _ := by rw [hcc,one_mul]

def a03ComplexLaplaceGammaIntegrand (s r : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ))

def a03ComplexLaplaceGamma (s r : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0, a03ComplexLaplaceGammaIntegrand s r u

theorem a03ComplexLaplaceGammaIntegrand_continuousOn (s r : ℂ) :
    ContinuousOn (a03ComplexLaplaceGammaIntegrand s r) (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro u hu
  have hp : ContinuousAt (fun x : ℝ => (x:ℂ)^(s-1)) u :=
    (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hu)).comp
      Complex.continuous_ofReal.continuousAt
  exact hp.mul (by fun_prop)

theorem a03ComplexLaplaceGammaIntegrand_norm (s r : ℂ) {u : ℝ} (hu : 0<u) :
    ‖a03ComplexLaplaceGammaIntegrand s r u‖=
      u^(s.re-1)*Real.exp (-r.re*u) := by
  unfold a03ComplexLaplaceGammaIntegrand
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hu,Complex.norm_exp]
  simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.neg_re,
    Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem a03ComplexLaplaceGamma_integrable {s r : ℂ} (hs : 0<s.re) (hr : 0<r.re) :
    IntegrableOn (fun u : ℝ => (u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ))) (Ioi 0) := by
  have hm := a03LaplaceRealMajorant_integrable hs hr
  apply hm.mono'
    ((a03ComplexLaplaceGammaIntegrand_continuousOn s r).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (a03ComplexLaplaceGammaIntegrand_norm s r hu).le

theorem a03ComplexLaplaceGamma_eq_ofReal {s : ℂ} (hs : 0<s.re) {c : ℝ} (hc : 0<c) :
    a03ComplexLaplaceGamma s c=(c:ℂ)^(-s)*Complex.Gamma s := by
  unfold a03ComplexLaplaceGamma a03ComplexLaplaceGammaIntegrand
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hc
  have hneg : ∀ u : ℝ,-((c:ℂ)*u)=-(c:ℂ)*u := by intro u; ring
  simp_rw [hneg] at h
  rw [h]
  rw [one_div,Complex.inv_cpow_ofReal_nonneg hc.le,Complex.cpow_neg]

theorem a03ComplexLaplaceGamma_differentiableAt {s r₀ : ℂ}
    (hs : 0<s.re) (hr : 0<r₀.re) : DifferentiableAt ℂ (a03ComplexLaplaceGamma s) r₀ := by
  let F : ℂ→ℝ→ℂ := a03ComplexLaplaceGammaIntegrand s
  let D : ℂ→ℝ→ℂ := fun r u => -(u:ℂ)*F r u
  let c : ℝ := r₀.re/2
  have hc : 0<c := by dsimp [c]; positivity
  have hFc (r : ℂ) : ContinuousOn (F r) (Ioi 0) :=
    a03ComplexLaplaceGammaIntegrand_continuousOn s r
  have hDc (r : ℂ) : ContinuousOn (D r) (Ioi 0) :=
    (by fun_prop : ContinuousOn (fun u : ℝ => -(u:ℂ)) (Ioi 0)).mul (hFc r)
  have hlow {r : ℂ} (hmem : r∈Metric.ball r₀ c) : c≤r.re := by
    have hn : ‖r-r₀‖<c := by simpa only [Metric.mem_ball,dist_eq_norm] using hmem
    have hre : |r.re-r₀.re|≤‖r-r₀‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (r-r₀)
    have hmin := (abs_le.mp hre).1
    dsimp [c] at *
    linarith
  have hnorm : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ r∈Metric.ball r₀ c,
      ‖D r u‖≤u^(s.re)*Real.exp (-c*u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro r hrmem
    have hu0 : 0<u := hu
    have hpow : u*u^(s.re-1)=u^s.re := by
      nth_rw 1 [←Real.rpow_one u]
      rw [←Real.rpow_add hu0]
      congr 1
      ring
    simp only [D,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
    rw [a03ComplexLaplaceGammaIntegrand_norm s r hu0,
      ←mul_assoc,hpow]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu0.le _)
    apply Real.exp_le_exp.mpr
    have hrlow := hlow hrmem
    nlinarith
  have hd : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0), ∀ r∈Metric.ball r₀ c,
      HasDerivAt (fun z => F z u) (D r u) r := by
    apply ae_of_all
    intro u r _
    have h := (((hasDerivAt_id r).neg.mul_const (u:ℂ)).cexp).const_mul ((u:ℂ)^(s-1))
    simpa [D,F,a03ComplexLaplaceGammaIntegrand,mul_comm,mul_left_comm,mul_assoc] using h
  have hbound : Integrable (fun u : ℝ => u^(s.re)*Real.exp (-c*u))
      (volume.restrict (Ioi 0)) := by
    change IntegrableOn (fun u : ℝ => u^(s.re)*Real.exp (-c*u)) (Ioi 0)
    have h := a03LaplaceRealMajorant_integrable (σ:=s.re+1) (by linarith) hc
    simpa only [add_sub_cancel_right] using h
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (μ:=volume.restrict (Ioi 0)) (s:=Metric.ball r₀ c)
    (bound:=fun u : ℝ => u^(s.re)*Real.exp (-c*u))
    (Metric.ball_mem_nhds r₀ hc)
    (Eventually.of_forall (fun r => (hFc r).aestronglyMeasurable measurableSet_Ioi))
    (a03ComplexLaplaceGamma_integrable hs hr)
    ((hDc r₀).aestronglyMeasurable measurableSet_Ioi) hnorm hbound hd
  exact hi.2.differentiableAt

theorem a03ComplexLaplaceGamma_analyticOn {s : ℂ} (hs : 0<s.re) :
    AnalyticOnNhd ℂ (a03ComplexLaplaceGamma s) {r : ℂ | 0<r.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro r hr
  exact (a03ComplexLaplaceGamma_differentiableAt hs hr).differentiableWithinAt

/-- Complex Laplace evaluation on its genuine domain `Re(r)>0`.  Equality
on the positive real axis is continued only after holomorphy of the actual
integral has been established by a locally integrable derivative majorant. -/
theorem a03ComplexLaplaceGamma_eq {s r : ℂ} (hs : 0<s.re) (hr : 0<r.re) :
    (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ)))=
      r^(-s)*Complex.Gamma s := by
  let U : Set ℂ := {r : ℂ | 0<r.re}
  let R : ℂ→ℂ := fun r => r^(-s)*Complex.Gamma s
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hR : AnalyticOnNhd ℂ R U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).mpr
    intro z hz
    exact (((differentiableAt_id : DifferentiableAt ℂ id z).cpow_const
      (show z∈Complex.slitPlane from Or.inl hz)).mul_const (Complex.Gamma s)).differentiableWithinAt
  have hconn : IsPreconnected U :=
    (convex_halfSpace_gt Complex.reLm.isLinear (0:ℝ)).isPreconnected
  have h1 : (1:ℂ)∈U := by simp [U]
  have hclosure : (1:ℂ)∈closure
      ({z : ℂ | a03ComplexLaplaceGamma s z=R z} \ {(1:ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let c : ℝ := 1+ε/2
    have hc : 0<c := by dsimp [c]; linarith
    refine ⟨(c:ℂ),⟨?_,?_⟩,?_⟩
    · exact a03ComplexLaplaceGamma_eq_ofReal hs hc
    · simp only [Set.mem_singleton_iff]
      intro heq
      have hcreal : c=1 := Complex.ofReal_injective (by simpa only [Complex.ofReal_one] using heq)
      dsimp [c] at hcreal
      linarith
    · rw [dist_eq_norm,show (1:ℂ)-(c:ℂ)=((1-c:ℝ):ℂ) by push_cast; ring,
        Complex.norm_real,Real.norm_eq_abs]
      dsimp [c]
      rw [show 1-(1+ε/2)=-(ε/2) by ring,abs_neg,abs_of_pos (by positivity : 0<ε/2)]
      linarith
  exact (a03ComplexLaplaceGamma_analyticOn hs).eqOn_of_preconnected_of_mem_closure
    hR hconn h1 hclosure hr

end
end Sechstmoment.Source

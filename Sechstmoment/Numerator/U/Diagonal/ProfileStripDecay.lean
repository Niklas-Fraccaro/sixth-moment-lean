import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Sechstmoment.Numerator.U.Diagonal.ProfileHolomorphy


namespace Sechstmoment
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem actualProfileWeight_deriv {f : ℝ → ℂ} (hfs : ContDiff ℝ ∞ f) (c x : ℝ) :
    deriv (profileExponentialWeight f c) x =
      ((Real.exp (c*x)*c:ℝ):ℂ)*f x+(Real.exp (c*x):ℂ)*deriv f x := by
  have he := ((Real.hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)).ofReal_comp
  have hf := (hfs.differentiable (by simp) x).hasDerivAt
  have h := he.mul hf
  simpa only [profileExponentialWeight,Function.comp_apply,id_eq,mul_one] using! h.deriv

private theorem actualProfileStrip_deriv_bound {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ Icc a b, ∀ x : ℝ,
      ‖deriv (profileExponentialWeight f c) x‖ ≤ M*(‖f x‖+‖deriv f x‖) := by
  obtain ⟨A,hA⟩ := (show IsCompact (tsupport f) from hf).isBounded.exists_norm_le
  let R : ℝ := max A 1
  let C : ℝ := max |a| |b|
  have hR : 0 ≤ R := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hC : 0 ≤ C := (abs_nonneg a).trans (le_max_left _ _)
  refine ⟨Real.exp (C*R)*(C+1),mul_nonneg (Real.exp_pos _).le (by linarith),?_⟩
  intro c hc x
  rw [actualProfileWeight_deriv hfs]
  by_cases hx : x ∈ tsupport f
  · have hxc : ‖x‖ ≤ R := (hA x hx).trans (le_max_left _ _)
    have hcc : |c| ≤ C := abs_le.mpr ⟨by
      have h := (neg_abs_le a).trans hc.1
      exact (neg_le_neg (le_max_left |a| |b|)).trans h,
      hc.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    have hex : c*x ≤ C*R := by
      calc
        _ ≤ |c*x| := le_abs_self _
        _ = |c| *‖x‖ := by rw [abs_mul,Real.norm_eq_abs]
        _ ≤ C*R := mul_le_mul hcc hxc (norm_nonneg _) hC
    calc
      _ ≤ ‖((Real.exp (c*x)*c:ℝ):ℂ)*f x‖+‖(Real.exp (c*x):ℂ)*deriv f x‖ := norm_add_le _ _
      _ = Real.exp (c*x)*(|c| *‖f x‖+‖deriv f x‖) := by
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
          Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ Real.exp (C*R)*(C*‖f x‖+‖deriv f x‖) := by
        apply mul_le_mul (Real.exp_le_exp.mpr hex)
        · gcongr
        · positivity
        · positivity
      _ ≤ Real.exp (C*R)*(C+1)*(‖f x‖+‖deriv f x‖) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        nlinarith [norm_nonneg (f x),norm_nonneg (deriv f x),mul_nonneg hC (norm_nonneg (deriv f x))]
  · have hfx : f x=0 := Function.notMem_support.mp (fun h => hx (subset_tsupport f h))
    have hdx : deriv f x=0 := deriv_of_notMem_tsupport hx
    simp [hfx,hdx]

theorem profileLaplaceTransform_strip_frequency_bound {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, ∀ v : ℝ,
      |v| *‖profileLaplaceTransform f ((c:ℂ)+(v:ℂ)*I)‖ ≤ C := by
  obtain ⟨M,hM,hbound⟩ := actualProfileStrip_deriv_bound hf hfs a b
  have hfI : Integrable f := hfs.continuous.integrable_of_hasCompactSupport hf
  have hfdI : Integrable (deriv f) := (hfs.continuous_deriv (by simp)).integrable_of_hasCompactSupport hf.deriv
  let C : ℝ := M*(∫ x : ℝ, ‖f x‖+‖deriv f x‖)
  refine ⟨C,mul_nonneg hM (integral_nonneg (fun x => by positivity)),?_⟩
  intro c hc v
  let g := profileExponentialWeight f c
  have hgC := profileExponentialWeight_contDiff hfs c
  have hgK := profileExponentialWeight_hasCompactSupport hf c
  have hgI : Integrable g := hgC.continuous.integrable_of_hasCompactSupport hgK
  have hgdI : Integrable (deriv g) := (hgC.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgK.deriv
  have hDer := congrFun (Real.fourier_deriv hgI (hgC.differentiable (by simp)) hgdI) (-v/(2*π))
  have hcoeff : (2*π*I*((-v/(2*π):ℝ):ℂ):ℂ)=-(v:ℂ)*I := by
    push_cast
    field_simp
  have hnorm : ‖𝓕 (deriv g) (-v/(2*π))‖ = |v| *‖𝓕 g (-v/(2*π))‖ := by
    rw [hDer,norm_smul,hcoeff,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  rw [profileLaplaceTransform_eq_fourier]
  rw [← hnorm]
  calc
    _ ≤ ∫ x : ℝ, ‖deriv g x‖ := by
      rw [Real.fourier_eq']
      apply (norm_integral_le_integral_norm _).trans_eq
      apply integral_congr_ae
      filter_upwards [] with x
      rw [norm_smul,Complex.norm_exp]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,zero_mul,sub_zero,Real.exp_zero,one_mul]
    _ ≤ ∫ x : ℝ, M*(‖f x‖+‖deriv f x‖) :=
      integral_mono hgdI.norm ((hfI.norm.add hfdI.norm).const_mul M) (fun x => hbound c hc x)
    _ = C := integral_const_mul _ _

theorem profileLaplaceTransform_strip_uniform_horizontal_decay {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (a b : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ c ∈ Icc a b, ∀ v : ℝ,
      R ≤ |v| → ‖profileLaplaceTransform f ((c:ℂ)+(v:ℂ)*I)‖ ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := profileLaplaceTransform_strip_frequency_bound hf hfs a b
  intro ε hε
  refine ⟨C/ε+1,by positivity,?_⟩
  intro c hc v hv
  have h := hbound c hc v
  have hR : C < (C/ε+1)*ε := by field_simp; nlinarith
  have hvpos : 0 < |v| := (by positivity : 0 < C/ε+1).trans_le hv
  by_contra hn
  have h1 := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hvpos
  have h2 := mul_le_mul_of_nonneg_right hv hε.le
  linarith

end
end Sechstmoment

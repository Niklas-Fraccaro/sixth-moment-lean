import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Sechstmoment.Analysis.Complex.SimplePole
import Sechstmoment.Numerator.U.ZeroModes.Contour.Chambers
import Sechstmoment.Numerator.U.ZeroModes.Contour.RatioWeight

/-! A constructive Mellin ratio partition for BBLR §4. The identity
`g(x)+g(1/x)=1` is obtained by moving the genuine one-dimensional contour
across its simple pole at zero. All boundary integrability and edge limits
are proved from entire-weight bounds; no displacement is an input. -/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioKernel (G : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  G z*(x:ℂ)^(-z)/z

def a03ZeroModeRatioPartition (G : ℂ → ℂ) (x : ℝ) : ℂ :=
  verticalIntegral 1 (a03ZeroModeRatioKernel G x)

theorem a03ZeroModeRatioNumerator_differentiable {x : ℝ} (hx : 0<x)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G) :
    Differentiable ℂ (fun z : ℂ => G z*(x:ℂ)^(-z)) :=
  hG.mul (differentiable_id.neg.const_cpow
    (.inl (Complex.ofReal_ne_zero.mpr hx.ne')))

theorem a03ZeroModeRatioKernel_line_integrable {x c : ℝ}
    (hx : 0<x) (hc : c≠0) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    Integrable (fun v : ℝ => a03ZeroModeRatioKernel G x ((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 (|c|+1) (by positivity) 2
  let D : ℝ := x^(-c)/|c|
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have hD : 0≤D := by dsimp [D]; positivity
  have hpoint (v : ℝ) :
      ‖a03ZeroModeRatioKernel G x ((c:ℂ)+(v:ℂ)*I)‖≤B*D*(1+v^2)⁻¹ := by
    let z : ℂ := (c:ℂ)+(v:ℂ)*I
    have hInv : ‖z‖⁻¹≤|c|⁻¹ :=
      inv_anti₀ hcpos (by simpa [z] using Complex.abs_re_le_norm z)
    have hPow : ‖(x:ℂ)^(-z)‖=x^(-c) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [z]
    have hN : ‖a03ZeroModeRatioKernel G x z‖≤‖G z‖*D := by
      unfold a03ZeroModeRatioKernel
      rw [norm_div, norm_mul, hPow, div_eq_mul_inv]
      calc
        _ ≤ ‖G z‖*x^(-c)*|c|⁻¹ := by gcongr
        _ = _ := by dsimp [D]; ring
    have hGN : ‖G z‖*(1+|v|)^2≤B := by
      simpa [z] using hWeight z (by simp [z])
    have hFull : ‖a03ZeroModeRatioKernel G x z‖*(1+|v|)^2≤B*D := by
      calc
        _ ≤ (‖G z‖*D)*(1+|v|)^2 :=
          mul_le_mul_of_nonneg_right hN (sq_nonneg _)
        _ = (‖G z‖*(1+|v|)^2)*D := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hGN hD
    have hSq : 1+v^2≤(1+|v|)^2 := by nlinarith [sq_abs v,abs_nonneg v]
    have hProd := (mul_le_mul_of_nonneg_left hSq
      (norm_nonneg (a03ZeroModeRatioKernel G x z))).trans hFull
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : 0<1+v^2)).mpr hProd
  have hcont : Continuous (fun v : ℝ => a03ZeroModeRatioKernel G x ((c:ℂ)+(v:ℂ)*I)) := by
    apply ((a03ZeroModeRatioNumerator_differentiable hx G
      (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1)).continuous.comp
      (by fun_prop : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I))).div
      (by fun_prop)
    intro v hv
    have he := congrArg Complex.re hv
    simp at he
    exact hc he
  exact ((integrable_inv_one_add_sq.const_mul (B*D)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall hpoint))

theorem a03ZeroModeRatioKernel_horizontal_tendsto_zero {x : ℝ} (hx : 0<x)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Tendsto (fun v : ℝ => ∫ d in (-1:ℝ)..1,
      a03ZeroModeRatioKernel G x ((d:ℂ)+(v:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨B,hB,hWeight⟩ := hG.2.2.2 1 (by norm_num) 0
  let D : ℝ := B*Real.exp |Real.log x|
  have hD : 0≤D := by dsimp [D]; positivity
  have hv : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim : Tendsto (fun v : ℝ => (2*D)*|v|⁻¹) (cocompact ℝ) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hv).const_mul (2*D)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hv.eventually (eventually_ge_atTop (1:ℝ))] with v hvone
  have hvpos : 0 < |v| := zero_lt_one.trans_le hvone
  have hnorm (d : ℝ) (hd : d∈uIoc (-1:ℝ) 1) :
      ‖a03ZeroModeRatioKernel G x ((d:ℂ)+(v:ℂ)*I)‖≤D*|v|⁻¹ := by
    rw [uIoc_of_le (by norm_num : (-1:ℝ)≤1)] at hd
    let z : ℂ := (d:ℂ)+(v:ℂ)*I
    have hweight : ‖G z‖≤B := by
      simpa using hWeight z (by simp [z,abs_le]; constructor <;> linarith [hd.1,hd.2])
    have hPow : ‖(x:ℂ)^(-z)‖≤Real.exp |Real.log x| := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hre : (-z).re=-d := by simp [z]
      rw [hre,Real.rpow_def_of_pos hx]
      apply Real.exp_le_exp.mpr
      by_cases hsgn : 0≤Real.log x
      · have hs : Real.log x*(-d)≤Real.log x := by nlinarith [hd.1.le]
        exact hs.trans (le_abs_self _)
      · have hs : Real.log x*(-d)≤-Real.log x := by nlinarith [hd.2]
        exact hs.trans (neg_le_abs _)
    have hInv : ‖z‖⁻¹≤|v|⁻¹ :=
      inv_anti₀ hvpos (by simpa [z] using Complex.abs_im_le_norm z)
    unfold a03ZeroModeRatioKernel
    rw [norm_div,norm_mul,div_eq_mul_inv]
    calc
      _ ≤ B*Real.exp |Real.log x| * |v|⁻¹ := by gcongr
      _ = _ := by rfl
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1:ℝ)) (b := 1) (C := D*|v|⁻¹) hnorm
  exact hb.trans_eq (by norm_num; ring)

theorem a03ZeroModeRatioKernel_reflection {x : ℝ} (hx : 0<x)
    (G : ℂ → ℂ) (hEven : ∀ z, G (-z)=G z) (z : ℂ) :
    a03ZeroModeRatioKernel G x (-z) = -a03ZeroModeRatioKernel G x⁻¹ z := by
  unfold a03ZeroModeRatioKernel
  rw [hEven,neg_neg,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg hx.le,
    Complex.cpow_neg,inv_inv]
  simp only [div_neg]

theorem a03ZeroModeRatioPartition_identity {x : ℝ} (hx : 0<x)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    a03ZeroModeRatioPartition G x+a03ZeroModeRatioPartition G x⁻¹=1 := by
  let H : ℂ → ℂ := fun z => G z*(x:ℂ)^(-z)
  have hH : Differentiable ℂ H := a03ZeroModeRatioNumerator_differentiable hx G
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1)
  have hrect := Sechstmoment.mellinRectangle_simplePole_shift H isOpen_univ
    hH.differentiableOn (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)
    (fun _ _ _ => mem_univ _) (a03ZeroModeRatioKernel_line_integrable hx
      (by norm_num : (-1:ℝ)≠0) G α hG)
    (a03ZeroModeRatioKernel_line_integrable hx (by norm_num : (1:ℝ)≠0) G α hG)
    (a03ZeroModeRatioKernel_horizontal_tendsto_zero hx G α hG)
  have hzero : H 0=1 := by simp [H,hG.2.2.1]
  simp only [Complex.ofReal_one, Complex.ofReal_neg] at hrect
  have hshift : verticalIntegral 1 (a03ZeroModeRatioKernel G x)=
      verticalIntegral (-1) (a03ZeroModeRatioKernel G x)+1 := by
    unfold verticalIntegral
    change (1/(2*Real.pi):ℂ)*(∫ v : ℝ, H ((1:ℂ)+(v:ℂ)*I)/((1:ℂ)+(v:ℂ)*I)) = _
    rw [hrect,hzero]
    have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
    change (1/(2*Real.pi):ℂ)*(_+(2*Real.pi:ℂ)*1) = _
    rw [mul_add]
    simp only [mul_one,one_div,inv_mul_cancel₀ hπ]
    simp only [H,a03ZeroModeRatioKernel,Complex.ofReal_neg,Complex.ofReal_one]
  have href := a03ZeroMode_verticalIntegral_reflection 1 (a03ZeroModeRatioKernel G x)
  have href' : verticalIntegral (-1) (a03ZeroModeRatioKernel G x)=
      -verticalIntegral 1 (a03ZeroModeRatioKernel G x⁻¹) := by
    rw [←href]
    simp_rw [a03ZeroModeRatioKernel_reflection hx G hG.2.1]
    unfold verticalIntegral
    rw [integral_neg,mul_neg]
  unfold a03ZeroModeRatioPartition
  rw [hshift,href']
  ring

/-- The specific two-root Gaussian construction obeys the ratio partition. -/
theorem a03ZeroModeRatioPartition_actual_identity (α : MomentShifts)
    {x : ℝ} (hx : 0<x) :
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) x+
      a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) x⁻¹=1 :=
  a03ZeroModeRatioPartition_identity hx _ α (a03ZeroModeRatioWeight_admissible α)

end
end Sechstmoment.Source

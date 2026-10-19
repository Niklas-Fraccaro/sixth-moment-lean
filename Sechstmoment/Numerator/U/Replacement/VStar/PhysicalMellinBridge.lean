import Sechstmoment.Numerator.U.Replacement.VStar.Definitions
import Sechstmoment.Numerator.U.ZeroModes.Linearization.Fubini

/-! Genuine small-positive-line reconstruction of the full V* factor on
positive real physical quad variables. The real variables are never relabelled
as integers. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03PhysicalQuadProduct (Q : Fin 4→ℝ) : ℝ := ∏ j : Fin 4,Q j

private theorem realQuad_cpow_product (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (z : ℂ) :
    (a03PhysicalQuadProduct Q:ℂ)^z=∏ j : Fin 4,(Q j:ℂ)^z := by
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hP.ne'),←Complex.ofReal_log hP.le]
  unfold a03PhysicalQuadProduct
  simp only [Fin.prod_univ_four]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (hQ 0).ne' (hQ 1).ne') (hQ 2).ne') (hQ 3).ne',
    Real.log_mul (mul_ne_zero (hQ 0).ne' (hQ 1).ne') (hQ 2).ne',Real.log_mul (hQ 0).ne' (hQ 1).ne']
  simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hQ _).ne'),
    ←Complex.ofReal_log (hQ _).le]
  rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem a03ZeroModeRealQuadDenominator_shift (α : MomentShifts) (Q : Fin 4→ℝ)
    (hQ : ∀ j,0<Q j) (z : ℂ) :
    a03ZeroModeRealQuadDenominator α z Q=
      a03ZeroModeRealQuadDenominator α 0 Q*(a03PhysicalQuadProduct Q:ℂ)^z := by
  unfold a03ZeroModeRealQuadDenominator
  simp only [add_zero]
  simp_rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hQ _).ne')]
  rw [Finset.prod_mul_distrib,←realQuad_cpow_product Q hQ z]

theorem a03ZeroModeRealQuadDenominator_inv_shift (α : MomentShifts) (Q : Fin 4→ℝ)
    (hQ : ∀ j,0<Q j) (z : ℂ) :
    (a03ZeroModeRealQuadDenominator α z Q)⁻¹=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*(a03PhysicalQuadProduct Q:ℂ)^(-z) := by
  rw [a03ZeroModeRealQuadDenominator_shift α Q hQ z,mul_inv_rev,Complex.cpow_neg,mul_comm]

/-- Literal time amplitude of the actual leading tensor, with G preserved. -/
def a03PhysicalLeadingTimeAmplitude (T : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ)
    (z : ℂ) (t : ℝ) : ℂ :=
  (a03ZeroModeRealQuadDenominator α z Q)⁻¹*
    (polarPoleKiller T σ z/z*(T*t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z))

theorem a03PhysicalLeadingTimeAmplitude_eq_VStarKernel
    {T t : ℝ} (hT : 0<T) (ht : 0<t) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (z : ℂ) :
    a03PhysicalLeadingTimeAmplitude T σ α Q z t=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrVStarKernel (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) z := by
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  have hTt : 0<T*t := mul_pos hT ht
  have hh : 0<T*t/2 := by positivity
  have hy : 0<a03PhysicalQuadProduct Q/(T*t)^2 := by positivity
  have hπ : 0<2*Real.pi := by positivity
  have he : (a03PhysicalQuadProduct Q:ℂ)^(-z)*(T*t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)=
      (2*Real.pi:ℂ)^(-2*z)*(a03PhysicalQuadProduct Q/(T*t)^2:ℂ)^(-z) := by
    have hc₁ : (T*t/2:ℂ)=((T*t/2:ℝ):ℂ) := by push_cast; rfl
    have hc₂ : (a03PhysicalQuadProduct Q/(T*t)^2:ℂ)=((a03PhysicalQuadProduct Q/(T*t)^2:ℝ):ℂ) := by push_cast; rfl
    have hcπ : (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) := by push_cast; rfl
    rw [hc₁,hc₂,hcπ,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hP.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hπ.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      ←Complex.ofReal_log hP.le,←Complex.ofReal_log hh.le,←Complex.ofReal_log Real.pi_pos.le,
      ←Complex.ofReal_log hπ.le,←Complex.ofReal_log hy.le,
      ←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
    rw [Real.log_div hTt.ne' (by norm_num : (2:ℝ)≠0),
      Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero,
      Real.log_div hP.ne' (pow_ne_zero 2 hTt.ne'),Real.log_pow]
    congr 1
    push_cast
    ring
  unfold a03PhysicalLeadingTimeAmplitude bblrVStarKernel
  rw [a03ZeroModeRealQuadDenominator_inv_shift α Q hQ z]
  have he' := he
  calc
    _=(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*(polarPoleKiller T σ z/z)*
      ((a03PhysicalQuadProduct Q:ℂ)^(-z)*(T*t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)) := by ring
    _=_ := by rw [he']; push_cast; ring

/-- The full leading weight is reconstructed on any genuine positive line,
including the source's small c-line. -/
theorem a03PhysicalLeadingTimeAmplitude_vertical_eq_VStar
    {T t c : ℝ} (hT : 0<T) (ht : 0<t) (hc : 0<c) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) :
    Integrable (fun v : ℝ => a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t) ∧
    verticalIntegral c (fun z => a03PhysicalLeadingTimeAmplitude T σ α Q z t)=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) := by
  have hy : 0<a03PhysicalQuadProduct Q/(T*t)^2 := by
    unfold a03PhysicalQuadProduct
    exact div_pos (Finset.prod_pos (fun j _ => hQ j)) (sq_pos_of_pos (mul_pos hT ht))
  have he : (fun z => a03PhysicalLeadingTimeAmplitude T σ α Q z t)=
      (fun z => (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrVStarKernel (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) z) :=
    funext (a03PhysicalLeadingTimeAmplitude_eq_VStarKernel hT ht σ α Q hQ)
  refine ⟨?_,?_⟩
  · apply ((bblrVStarKernel_vertical_integrable hy hc _ (rawMomentShifts T σ)
      (polarPoleKiller_BBLREntireWeight T σ _)).const_mul
        (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹).congr
    apply ae_of_all
    intro v
    exact (a03PhysicalLeadingTimeAmplitude_eq_VStarKernel hT ht σ α Q hQ _).symm
  · rw [he,bblrVStar_positive_contour hy hc _ (rawMomentShifts T σ) (polarPoleKiller_BBLREntireWeight T σ _)]
    unfold verticalIntegral
    rw [integral_const_mul]
    ring


def a03PhysicalLeadingVerticalCore (c T : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ)
    (t L : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ in Icc (-L) L,
    a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t

def a03PhysicalLeadingVerticalTail (c T : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ)
    (t L : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ in {v : ℝ | L < |v|},
    a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t

theorem a03PhysicalLeadingVerticalCore_eq {T t : ℝ} (hT : 0<T) (ht : 0<t)
    (c : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (L : ℝ) :
    a03PhysicalLeadingVerticalCore c T σ α Q t L=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrGaussianVStarCore c T σ (a03PhysicalQuadProduct Q) (T*t) L := by
  unfold a03PhysicalLeadingVerticalCore bblrGaussianVStarCore
  simp_rw [a03PhysicalLeadingTimeAmplitude_eq_VStarKernel hT ht σ α Q hQ]
  rw [integral_const_mul]
  ring

theorem a03PhysicalLeadingVerticalTail_eq {T t : ℝ} (hT : 0<T) (ht : 0<t)
    (c : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (L : ℝ) :
    a03PhysicalLeadingVerticalTail c T σ α Q t L=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrGaussianVStarTail c T σ (a03PhysicalQuadProduct Q) (T*t) L := by
  unfold a03PhysicalLeadingVerticalTail bblrGaussianVStarTail
  simp_rw [a03PhysicalLeadingTimeAmplitude_eq_VStarKernel hT ht σ α Q hQ]
  rw [integral_const_mul]
  ring

/-- Literal finite-window core plus the actual Gaussian frequency tail. -/
theorem a03PhysicalLeadingVerticalCore_add_tail {T t c : ℝ}
    (hT : 0<T) (ht : 0<t) (hc : 0<c) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (L : ℝ) :
    a03PhysicalLeadingVerticalCore c T σ α Q t L+
      a03PhysicalLeadingVerticalTail c T σ α Q t L=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) := by
  rw [a03PhysicalLeadingVerticalCore_eq hT ht c σ α Q hQ L,
    a03PhysicalLeadingVerticalTail_eq hT ht c σ α Q hQ L,←mul_add]
  congr 1
  exact (bblrGaussianVStar_core_add_tail hc (Finset.prod_pos (fun j _ => hQ j))
    (mul_pos hT ht).ne' T σ L).symm

private theorem physical_ratio_power {P T t c : ℝ} (hP : 0<P) (hT : 0<T) (ht : 0<t) :
    (P/(T*t)^2)^(-c)=P^(-c)*(T*t)^(2*c) := by
  have hTt : 0<T*t := mul_pos hT ht
  rw [Real.div_rpow hP.le (sq_nonneg _),Real.rpow_neg (sq_nonneg (T*t)),div_eq_mul_inv,inv_inv]
  have he : ((T*t)^2)^c=(T*t)^(2*c) := by
    rw [←Real.rpow_natCast (T*t) 2,←Real.rpow_mul hTt.le]
    norm_num
  rw [he,mul_comm]

theorem a03PhysicalLeadingTimeAmplitude_gaussian_bound {T c : ℝ} (hT : 0<T) (hc : 0<c)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j)
    (v t : ℝ) (ht : t∈Icc (1:ℝ) 2) :
    ‖a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t‖≤
      (‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
        polarGaussianConstant T σ c/c*(a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c))*
        ((1+|v|)^48*Real.exp (-(1/2)*v^2)) := by
  have htp : 0<t := zero_lt_one.trans_le ht.1
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  have hy : 0<a03PhysicalQuadProduct Q/(T*t)^2 := by positivity
  rw [a03PhysicalLeadingTimeAmplitude_eq_VStarKernel hT htp σ α Q hQ _,norm_mul]
  have hb := bblrGaussianVStarKernel_majorant hy hc T σ v
  rw [physical_ratio_power hP hT htp] at hb
  have htime : (T*t)^(2*c)≤(2*T)^(2*c) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [ht.2]) (by linarith)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hexp : Real.exp (-v^2)≤Real.exp (-(1/2)*v^2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg v])
  calc
    _≤‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
      ((polarGaussianConstant T σ c/c*((a03PhysicalQuadProduct Q)^(-c)*(T*t)^(2*c)))*
        (1+|v|)^48*Real.exp (-v^2)) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _≤‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
      ((polarGaussianConstant T σ c/c*((a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)))*
        (1+|v|)^48*Real.exp (-(1/2)*v^2)) := by gcongr
    _=_ := by ring

theorem a03PhysicalLeadingVerticalTail_gaussian_bound {T t c L : ℝ}
    (hT : 0<T) (ht : t∈Icc (1:ℝ) 2) (hc : 0<c) (hL : 0≤L)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) :
    ‖a03PhysicalLeadingVerticalTail c T σ α Q t L‖≤
      ‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
        (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        (a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)*Real.exp (-(1/2)*L^2) := by
  have htp : 0<t := zero_lt_one.trans_le ht.1
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  rw [a03PhysicalLeadingVerticalTail_eq hT htp c σ α Q hQ L,norm_mul]
  have hb := bblrGaussianVStarTail_norm_le hc hP (mul_pos hT htp).ne' hL T σ
  rw [physical_ratio_power hP hT htp] at hb
  have htime : (T*t)^(2*c)≤(2*T)^(2*c) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [ht.2]) (by linarith)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hGauss := gaussianTailConstant_nonneg 48
  calc
    _≤‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
      ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        ((a03PhysicalQuadProduct Q)^(-c)*(T*t)^(2*c))*Real.exp (-(1/2)*L^2)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _≤‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
      ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        ((a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c))*Real.exp (-(1/2)*L^2)) := by gcongr
    _=_ := by ring

end
end Sechstmoment

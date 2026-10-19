import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Sechstmoment.Numerator.U.ZeroModes.Transforms.ComplexLaplaceGamma

/-! Polynomial vertical growth of the actual Gamma--cosine Mellin factor.
The exponential saving is obtained from the genuine complex Laplace integral,
with its parameter approaching the imaginary axis at speed (1+|v|)^-1. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ComplexLaplaceGamma_norm_le {s r : ℂ} (hs : 0<s.re) (hr : 0<r.re) :
    ‖∫ u : ℝ in Ioi 0,(u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ))‖≤
      (1/r.re)^(s.re)*Real.Gamma s.re := by
  have h := norm_integral_le_of_norm_le
    (f:=fun u : ℝ => (u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ)))
    (a03LaplaceRealMajorant_integrable hs hr)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (a03ComplexLaplaceGammaIntegrand_norm s r hu).le)
  exact h.trans_eq (by simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr)

theorem a03Arg_ofReal_add_I {θ : ℝ} (hθ : 0<θ) :
    Complex.arg ((θ:ℂ)+I)=Real.pi/2-Real.arctan θ := by
  have hr : 0<((θ:ℂ)+I).re := by simpa using hθ
  have h := Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hr))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  rw [Complex.tan_arg] at h
  simp only [add_im,ofReal_im,I_im,zero_add,add_re,ofReal_re,I_re,add_zero,one_div] at h
  rw [←h,Real.arctan_inv_of_pos hθ]

theorem a03Gamma_vertical_exponential_bound_pos (c : ℝ) (hc : 0<c)
    (v : ℝ) (hv : 0≤v) :
    ‖Complex.Gamma ((c:ℂ)+(v:ℂ)*I)‖≤
      (Real.Gamma c*2^c*Real.exp 1)*(1+v)^c*Real.exp (-(Real.pi*v/2)) := by
  let θ : ℝ := (1+v)⁻¹
  let r : ℂ := (θ:ℂ)+I
  let s : ℂ := (c:ℂ)+(v:ℂ)*I
  have hθ : 0<θ := by dsimp [θ]; positivity
  have hθ1 : θ≤1 := by
    dsimp [θ]
    exact inv_le_one_of_one_le₀ (by linarith : (1:ℝ)≤1+v)
  have hr : 0<r.re := by simpa [r] using hθ
  have hs : 0<s.re := by simpa [s] using hc
  have hr0 : r≠0 := by intro he; rw [he,zero_re] at hr; linarith
  have hnorm : ‖r‖≤2 := by
    calc
      _≤‖(θ:ℂ)‖+‖I‖ := norm_add_le _ _
      _=θ+1 := by rw [Complex.norm_real,Real.norm_of_nonneg hθ.le,Complex.norm_I]
      _≤2 := by linarith
  have harg : Real.pi/2-θ≤Complex.arg r := by
    rw [a03Arg_ofReal_add_I hθ]
    linarith [Real.arctan_le_self hθ.le]
  have hθv : θ*v≤1 := by
    have he : θ*(1+v)=1 := by dsimp [θ]; exact inv_mul_cancel₀ (by positivity)
    nlinarith
  have heq : Complex.Gamma s=r^s*(∫u:ℝ in Ioi 0,(u:ℂ)^(s-1)*Complex.exp (-r*(u:ℂ))) := by
    rw [a03ComplexLaplaceGamma_eq hs hr,←mul_assoc,←Complex.cpow_add _ _ hr0,
      add_neg_cancel,Complex.cpow_zero,one_mul]
  have hLap := a03ComplexLaplaceGamma_norm_le hs hr
  have hsre : s.re=c := by simp [s]
  have hsim : s.im=v := by simp [s]
  have hrre : r.re=θ := by simp [r]
  rw [hsre,hrre] at hLap
  have hinv : 1/θ=1+v := by dsimp [θ]; simp
  rw [hinv] at hLap
  have hp : ‖r^s‖≤2^c*Real.exp (-(Real.pi*v/2)+1) := by
    rw [Complex.norm_cpow_of_ne_zero hr0,hsre,hsim,div_eq_mul_inv,←Real.exp_neg]
    apply mul_le_mul
    · exact Real.rpow_le_rpow (norm_nonneg _) hnorm hc.le
    · apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right harg hv
      nlinarith
    · positivity
    · positivity
  rw [heq,norm_mul]
  calc
    _≤(2^c*Real.exp (-(Real.pi*v/2)+1))*((1+v)^c*Real.Gamma c) :=
      mul_le_mul hp hLap (norm_nonneg _) (by positivity)
    _=_ := by rw [Real.exp_add]; ring

theorem a03Gamma_vertical_exponential_bound (c : ℝ) (hc : 0<c) (v : ℝ) :
    ‖Complex.Gamma ((c:ℂ)+(v:ℂ)*I)‖≤
      (Real.Gamma c*2^c*Real.exp 1)*(1+|v|)^c*Real.exp (-(Real.pi*|v|/2)) := by
  by_cases hv : 0≤v
  · simpa only [abs_of_nonneg hv] using a03Gamma_vertical_exponential_bound_pos c hc v hv
  · have hneg : 0≤-v := by linarith
    have he : (c:ℂ)+(v:ℂ)*I=conj ((c:ℂ)+((-v:ℝ):ℂ)*I) := by
      simp only [map_add,map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
      ring
    rw [he,Complex.Gamma_conj,Complex.norm_conj,abs_of_neg (lt_of_not_ge hv)]
    exact a03Gamma_vertical_exponential_bound_pos c hc (-v) hneg

theorem a03Complex_cos_norm_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖≤Real.exp |z.im| := by
  rw [Complex.cos,norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _≤‖Complex.exp (z*I)‖+‖Complex.exp (-z*I)‖ := norm_add_le _ _
    _=Real.exp (-z.im)+Real.exp z.im := by
      rw [Complex.norm_exp,Complex.norm_exp]
      simp
    _≤Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (neg_le_abs _)) (Real.exp_le_exp.mpr (le_abs_self _))
    _=_ := by ring

/-- Fixed positive-real-part Gamma--cosine factors have genuine polynomial
growth, uniformly over the complete imaginary axis. -/
theorem a03GammaCos_vertical_polynomial_bound (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ,∃ C : ℝ,0≤C ∧ ∀ v : ℝ,
      ‖Complex.Gamma ((c:ℂ)+(v:ℂ)*I)*
        Complex.cos (Real.pi*((c:ℂ)+(v:ℂ)*I)/2)‖≤C*(1+|v|)^N := by
  let C : ℝ := Real.Gamma c*2^c*Real.exp 1
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨⌈c⌉₊,C,hC,?_⟩
  intro v
  have hcos : ‖Complex.cos (Real.pi*((c:ℂ)+(v:ℂ)*I)/2)‖≤Real.exp (Real.pi*|v|/2) := by
    have h := a03Complex_cos_norm_le_exp_abs_im (Real.pi*((c:ℂ)+(v:ℂ)*I)/2)
    convert h using 1
    simp only [Complex.div_ofNat_im,mul_im,ofReal_im,ofReal_re,add_im,mul_im,ofReal_im,
      I_im,I_re,mul_one,mul_zero,add_re,ofReal_re,zero_add,add_zero]
    simp only [zero_mul,add_zero]
    rw [abs_div,abs_mul,abs_of_pos Real.pi_pos]
    norm_num
  rw [norm_mul]
  calc
    _≤(C*(1+|v|)^c*Real.exp (-(Real.pi*|v|/2)))*Real.exp (Real.pi*|v|/2) :=
      mul_le_mul (a03Gamma_vertical_exponential_bound c hc v) hcos (norm_nonneg _) (by positivity)
    _=C*(1+|v|)^c := by rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _≤C*(1+|v|)^(⌈c⌉₊:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (Nat.le_ceil c)) hC
    _=_ := by rw [Real.rpow_natCast]

end
end Sechstmoment.Source

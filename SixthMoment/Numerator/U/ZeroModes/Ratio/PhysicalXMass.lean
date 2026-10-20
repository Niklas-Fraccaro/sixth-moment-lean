import SixthMoment.Numerator.U.ZeroModes.Ratio.XEnvelopeMass

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioPhysicalXMajorant (T ε d c : ℝ) (α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (s : ℂ) (j : Fin 3) (x : ℝ) : ℝ :=
  x^(c-1)*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^d*(b:ℝ)^d*
    ((x/(g*a:ℕ))^(a03ZeroModeRatioResidualLeftLine ε j)*
      (x/(g*b:ℕ))^(a03ZeroModeRatioResidualRightLine ε j))*
        a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x

def a03ZeroModeRatioPhysicalXCoefficient (ε d : ℝ) (α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (s : ℂ) (j : Fin 3) : ℝ :=
  ‖A (g*a)‖*‖B (g*b)‖*(g:ℝ)^(-1+(α 1).re+(α 3).re-s.re-a03ZeroModeRatioSecondaryLine ε)*
    (a:ℝ)^(-1+(α 1).re+d-a03ZeroModeRatioResidualLeftLine ε j)*
      (b:ℝ)^(-1+(α 3).re+d-a03ZeroModeRatioResidualRightLine ε j)

theorem a03ZeroModeRatioPhysicalXCoefficient_nonneg (ε d : ℝ) (α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (s : ℂ) (j : Fin 3) :
    0≤a03ZeroModeRatioPhysicalXCoefficient ε d α g a b A B s j := by
  unfold a03ZeroModeRatioPhysicalXCoefficient
  positivity

theorem a03ZeroModeRatioPhysicalXMajorant_eq_power {T ε d c : ℝ}
    (α : MomentShifts) {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b)
    (A B : ℕ→ℂ) (s : ℂ) (j : Fin 3) {x : ℝ} (hx : 0<x) :
    a03ZeroModeRatioPhysicalXMajorant T ε d c α g a b A B s j x=
      a03ZeroModeRatioPhysicalXCoefficient ε d α g a b A B s j*
        (x^(c+a03ZeroModeRatioSecondaryLine ε-(α 1).re-(α 3).re-1)*
          a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x) := by
  have hn := a03ZeroModeRatioPhysicalPrefactor_gain_norm α hg ha hb A B hx s d
    (a03ZeroModeRatioResidualLeftLine ε j) (a03ZeroModeRatioResidualRightLine ε j)
      (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioResidualLine_sum ε j)
  unfold a03ZeroModeRatioPhysicalXMajorant a03ZeroModeRatioPhysicalXCoefficient
  calc
    _=x^(c-1)*
      (‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^d*(b:ℝ)^d*
        ((x/(g*a:ℕ))^(a03ZeroModeRatioResidualLeftLine ε j)*
          (x/(g*b:ℕ))^(a03ZeroModeRatioResidualRightLine ε j)))*
      a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x := by ring
    _=_ := by
      rw [hn]
      have hp : x^(c-1)*x^(a03ZeroModeRatioSecondaryLine ε-(α 1).re-(α 3).re)=
          x^(c+a03ZeroModeRatioSecondaryLine ε-(α 1).re-(α 3).re-1) := by
        rw [←Real.rpow_add hx]
        congr 1
        ring
      calc
        _=(‖A (g*a)‖*‖B (g*b)‖*(g:ℝ)^(-1+(α 1).re+(α 3).re-s.re-a03ZeroModeRatioSecondaryLine ε)*
          (a:ℝ)^(-1+(α 1).re+d-a03ZeroModeRatioResidualLeftLine ε j)*
          (b:ℝ)^(-1+(α 3).re+d-a03ZeroModeRatioResidualRightLine ε j))*
          (x^(c-1)*x^(a03ZeroModeRatioSecondaryLine ε-(α 1).re-(α 3).re))*
          a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x := by ring
        _=_ := by rw [hp]; ring

theorem a03ZeroModeRatioPhysicalXMajorant_integrable_and_mass
    {T η : ℝ} (hT : 0<T) (hη : 0<η) (hη1 : η≤1/16)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    (s : ℂ) (j : Fin 3) :
    IntegrableOn (a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) (1+η/4) α g a b A B s j) (Ioi 0) ∧
      (∫x in Ioi (0:ℝ),a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) (1+η/4) α g a b A B s j x)≤
        5*a03ZeroModeRatioPhysicalXCoefficient (η/4) (η/4) α g a b A B s j*
          (a03ZeroModeRatioPhysicalScale T g a b)^((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-(α 1).re-(α 3).re) := by
  have hY := a03ZeroModeRatioPhysicalScale_pos hT hg ha hb
  have hr := a03ZeroModeRatioResidual_xmass_exponent_range hη hη1
    ((Complex.abs_re_le_norm _).trans (hα 1)) ((Complex.abs_re_le_norm _).trans (hα 3))
  obtain ⟨hi,hbnd⟩ := a03ZeroModeRatioXEnvelope_weight_integral_uniform hY hr.1 hr.2
  have hC := a03ZeroModeRatioPhysicalXCoefficient_nonneg (η/4) (η/4) α g a b A B s j
  have hI : IntegrableOn (a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) (1+η/4) α g a b A B s j) (Ioi 0) := by
    have hc : IntegrableOn (fun x : ℝ =>
        a03ZeroModeRatioPhysicalXCoefficient (η/4) (η/4) α g a b A B s j*
          (x^((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-(α 1).re-(α 3).re-1)*
            a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x)) (Ioi 0) :=
      hi.const_mul (a03ZeroModeRatioPhysicalXCoefficient (η/4) (η/4) α g a b A B s j)
    apply hc.congr_fun _ measurableSet_Ioi
    intro x hx
    exact (a03ZeroModeRatioPhysicalXMajorant_eq_power α hg ha hb A B s j hx).symm
  refine ⟨hI,?_⟩
  calc
    _=a03ZeroModeRatioPhysicalXCoefficient (η/4) (η/4) α g a b A B s j*
        (∫x in Ioi (0:ℝ),x^((1+η/4)+a03ZeroModeRatioSecondaryLine (η/4)-(α 1).re-(α 3).re-1)*
          a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact a03ZeroModeRatioPhysicalXMajorant_eq_power α hg ha hb A B s j hx
    _≤_ := (mul_le_mul_of_nonneg_left hbnd hC).trans_eq (by ring)

theorem a03ZeroModeRatioPhysicalXMajorant_total_budget
    {T η : ℝ} (hT : 1≤T) (hη : 0<η) (hη1 : η≤1/16)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+η/4) (j : Fin 3) :
    T*T^(-(1+η/4))*
      (∫x in Ioi (0:ℝ),a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) (1+η/4) α g a b A B s j x)≤
        5*‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*(g:ℝ)^(-1:ℝ)*
          (a:ℝ)^(a03ZeroModeRatioResidualAmplifierLeftExponent η j-1)*
          (b:ℝ)^(a03ZeroModeRatioResidualAmplifierRightExponent η j-1) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hbnd := (a03ZeroModeRatioPhysicalXMajorant_integrable_and_mass hTp hη hη1 α hα hg ha hb A B s j).2
  have hnorm := a03ZeroModeRatioPhysicalScale_residual_budget hT hη
    ((Complex.abs_re_le_norm _).trans (hα 1)) ((Complex.abs_re_le_norm _).trans (hα 3)) hg ha hb j
  apply (mul_le_mul_of_nonneg_left hbnd (by positivity : 0≤T*T^(-(1+η/4)))).trans
  unfold a03ZeroModeRatioPhysicalXCoefficient
  rw [hs]
  convert mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0≤5*‖A (g*a)‖*‖B (g*b)‖) using 1 <;> ring

end
end SixthMoment.Source

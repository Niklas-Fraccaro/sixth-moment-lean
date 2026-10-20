import Sechstmoment.Arithmetic.Euler.Shifted.ScaledLimit
import Sechstmoment.Numerator.U.Replacement.GaussianCoefficientGrowth


namespace Sechstmoment
open Complex Filter Set Source
open scoped BigOperators Topology
noncomputable section

theorem complex_inverse_height_tendsto {ι : Type*} {l : Filter ι}
    {L : ι → ℝ} (hL : Tendsto L l atTop) :
    Tendsto (fun i => (L i : ℂ)⁻¹) l (𝓝 0) := by
  simpa only [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_zero] using
    (tendsto_inv_atTop_zero.comp hL).ofReal

theorem scaled_riemannZeta_moving_tendsto {ι : Type*} {l : Filter ι}
    {L : ι → ℝ} {w : ι → ℂ} {w₀ : ℂ}
    (hL : Tendsto L l atTop) (hw : Tendsto w l (𝓝 w₀)) (hw₀ : w₀ ≠ 0) :
    Tendsto (fun i => riemannZeta (1+w i/(L i:ℂ))/(L i:ℂ)) l (𝓝 (1/w₀)) := by
  have hsmall := hw.mul (complex_inverse_height_tendsto hL)
  simp only [mul_zero] at hsmall
  have harg : Tendsto (fun i => 1+w i/(L i:ℂ)) l (𝓝 1) := by
    simpa only [div_eq_mul_inv, add_zero] using tendsto_const_nhds.add hsmall
  have hreg := polarRegularizedZeta_continuousAt_one.tendsto.comp harg
  simp only [polarRegularizedZeta_one] at hreg
  apply (hreg.div hw hw₀).congr'
  filter_upwards [hL.eventually (eventually_gt_atTop (0:ℝ)),
    hw.eventually (eventually_ne_nhds hw₀)] with i hLi hwi
  exact (scaled_riemannZeta_eq_regularized hLi.ne' hwi).symm

theorem shiftedPolarEulerRest_moving_scaled_tendsto {ι : Type*} {l : Filter ι}
    {L : ι → ℝ} {ab : ι → PolarShiftSpace} {ab₀ : PolarShiftSpace}
    (hL : Tendsto L l atTop) (hab : Tendsto ab l (𝓝 ab₀)) :
    Tendsto (fun i => shiftedPolarEulerRest
      (scaledPolarShifts (L i) (ab i)).1
      (scaledPolarShifts (L i) (ab i)).2) l (𝓝 (arithmeticFactor:ℂ)) := by
  have hzero : Tendsto (fun i => scaledPolarShifts (L i) (ab i)) l
      (𝓝 (0:PolarShiftSpace)) := by
    simpa only [scaledPolarShifts, zero_smul] using
      (complex_inverse_height_tendsto hL).smul hab
  simpa only [Function.comp_def, shiftedPolarEulerRest_zero] using
    shiftedPolarEulerRest_continuousAt_zero.tendsto.comp hzero

theorem bblrSixShifts_continuous (m : Fin 6) :
    Continuous (fun σ : MomentShifts => bblrSixShifts σ m) := by
  fin_cases m <;> simp only [bblrSixShifts] <;> fun_prop

theorem bblrSixPhaseExponents_continuous (m : Fin 6) :
    Continuous (fun σ : MomentShifts => bblrSixPhaseExponents σ m) := by
  fin_cases m <;> simp only [bblrSixPhaseExponents] <;> fun_prop

theorem normalizedPurePolarRoot_continuous (k : PurePolarIndex) :
    Continuous (fun σ : MomentShifts => normalizedPurePolarRoot σ k) := by
  unfold normalizedPurePolarRoot
  exact (((continuous_apply _).comp (bblrSixShifts_continuous k.1)).add
    ((continuous_apply _).comp (bblrSixShifts_continuous k.1))).neg.div_const 2

theorem ninePolarArgument_continuous_shifts (u v z : ℂ) (ij : Fin 3 × Fin 3) :
    Continuous (fun σ : MomentShifts => ninePolarArgument u v z σ ij) := by
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [ninePolarArgument, polarLeftArguments, polarRightArguments] <;> fun_prop

theorem ninePolarZetaFactor_moving_tendsto {ι : Type*} {l : Filter ι}
    {L : ι → ℝ} {σ : ι → MomentShifts} {σ₀ : MomentShifts}
    (hL : Tendsto L l atTop) (hσ : Tendsto σ l (𝓝 σ₀)) (u v z : ℂ)
    (hsep : ∀ ij : Fin 3 × Fin 3, ninePolarArgument u v z σ₀ ij ≠ 0) :
    Tendsto (fun i => ninePolarZetaFactor (L i) u v z (σ i)) l
      (𝓝 (ninePolarRationalFactor u v z σ₀)) := by
  apply tendsto_finsetProd
  intro ij _
  exact scaled_riemannZeta_moving_tendsto hL
    ((ninePolarArgument_continuous_shifts u v z ij).tendsto σ₀ |>.comp hσ) (hsep ij)

end
end Sechstmoment

import SixthMoment.Numerator.V.Arithmetic.TimeWeightFamily


namespace SixthMoment.Source
open Complex Real
noncomputable section
set_option autoImplicit false

theorem timeWeight_residue_centered_scale (w : ℝ → ℂ) {T : ℝ} (hT : 0 < T)
    (σ z : ℂ) :
    mellin (noDPTimeWeight w T (z/(Real.log T:ℂ))) (1-σ/(Real.log T:ℂ))*
        ((T/(2*Real.pi):ℝ):ℂ)^(1-σ/(Real.log T:ℂ))/(T:ℂ) =
      (1/(2*Real.pi):ℂ)*Complex.exp (-(σ+z))*
        elementaryCenteredPhase T 1 (σ+z)*mellin w (1-(σ+z)/(Real.log T:ℂ)) := by
  let L : ℂ := (Real.log T:ℂ)
  let X : ℝ := T/(2*Real.pi)
  let ν : ℂ := σ+z
  have hX : 0 < X := div_pos hT (by positivity)
  have hXC : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hTC : (T:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hpow : (X:ℂ)^(-(z/L))*(X:ℂ)^(1-σ/L) = (X:ℂ)*(X:ℂ)^(-ν/L) := by
    rw [← Complex.cpow_add _ _ hXC]
    rw [show -(z/L)+(1-σ/L) = 1+(-ν/L) by dsimp only [ν]; ring]
    rw [Complex.cpow_add _ _ hXC,Complex.cpow_one]
  have hphase : Complex.exp (-ν)*elementaryCenteredPhase T 1 ν = (X:ℂ)^(-ν/L) := by
    dsimp only [elementaryCenteredPhase]
    simp only [mul_one]
    change Complex.exp (-ν)*(Complex.exp ν*(X:ℂ)^(-ν/L)) = _
    rw [← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  have harg : 1-σ/L-z/L = 1-ν/L := by dsimp only [ν]; ring
  have hratio : (X:ℂ)/(T:ℂ) = (1/(2*Real.pi):ℂ) := by
    dsimp only [X]
    push_cast
    field_simp [hTC]
  rw [noDPTimeWeight_mellin]
  change ((X:ℂ)^(-(z/L))*mellin w (1-σ/L-z/L))*(X:ℂ)^(1-σ/L)/(T:ℂ) = _
  rw [harg]
  calc
    _ = ((X:ℂ)^(-(z/L))*(X:ℂ)^(1-σ/L))/(T:ℂ)*mellin w (1-ν/L) := by ring
    _ = ((X:ℂ)/(T:ℂ))*(X:ℂ)^(-ν/L)*mellin w (1-ν/L) := by rw [hpow]; ring
    _ = (1/(2*Real.pi):ℂ)*(Complex.exp (-ν)*elementaryCenteredPhase T 1 ν)*
        mellin w (1-ν/L) := by rw [hratio,← hphase]
    _ = _ := by ring

end
end SixthMoment.Source

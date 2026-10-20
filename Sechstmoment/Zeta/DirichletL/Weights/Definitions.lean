import Sechstmoment.Zeta.DirichletL.GammaWeights
import Sechstmoment.Zeta.DirichletL.SquareSeries


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators Classical
noncomputable section

def dirichletParity {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ :=
  if χ.Even then 0 else 1

theorem dirichletParity_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) :
    dirichletParity χ ≤ 1 := by
  classical
  unfold dirichletParity
  split_ifs <;> omega

theorem dirichletParity_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    dirichletParity χ⁻¹ = dirichletParity χ := by
  have he : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_eq_one]
  simp only [dirichletParity, he]

theorem dirichletGammaFactor_eq_parity {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.gammaFactor s = (Real.pi : ℂ)^(-(s+(dirichletParity χ : ℂ))/2)*
      Complex.Gamma ((s+(dirichletParity χ : ℂ))/2) := by
  classical
  unfold DirichletCharacter.gammaFactor dirichletParity
  split_ifs <;> simp [Complex.Gammaℝ_def]

def squareSmoothGammaContour (s : ℂ) (a : ℕ) (x : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (w^2)*
    (Complex.Gamma ((s+(a : ℂ)+w)/2)/Complex.Gamma ((s+(a : ℂ))/2))^2*(x : ℂ)^(-w)

def squareSmoothWeight (s : ℂ) (a : ℕ) (x : ℝ) : ℂ :=
  (∫ v : ℝ, squareSmoothGammaContour s a x (2+(v : ℂ)*I)/(2+(v : ℂ)*I))/(2*Real.pi : ℂ)

theorem conductorGammaRatio_sq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) (w : ℂ) :
    (conductorGammaFactor χ (s+w)/conductorGammaFactor χ s)^2 =
      (N : ℂ)^w*(Real.pi : ℂ)^(-w)*
        (Complex.Gamma ((s+(dirichletParity χ : ℂ)+w)/2)/
          Complex.Gamma ((s+(dirichletParity χ : ℂ))/2))^2 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Complex.Gamma ((s+(dirichletParity χ : ℂ))/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    have ha : (0 : ℝ) ≤ dirichletParity χ := Nat.cast_nonneg _
    linarith
  have hNadd : (N : ℂ)^((s+w)/2) = (N : ℂ)^(s/2)*(N : ℂ)^(w/2) := by
    rw [← Complex.cpow_add _ _ hN]
    congr 1
    ring
  have hpadd : (Real.pi : ℂ)^(-(s+w+(dirichletParity χ : ℂ))/2) =
      (Real.pi : ℂ)^(-(s+(dirichletParity χ : ℂ))/2)*(Real.pi : ℂ)^(-w/2) := by
    rw [← Complex.cpow_add _ _ hp]
    congr 1
    ring
  have he : conductorGammaFactor χ (s+w)/conductorGammaFactor χ s =
      (N : ℂ)^(w/2)*(Real.pi : ℂ)^(-w/2)*
        (Complex.Gamma ((s+(dirichletParity χ : ℂ)+w)/2)/
          Complex.Gamma ((s+(dirichletParity χ : ℂ))/2)) := by
    unfold conductorGammaFactor
    rw [dirichletGammaFactor_eq_parity, dirichletGammaFactor_eq_parity, hNadd, hpadd]
    rw [show s+w+(dirichletParity χ : ℂ) = s+(dirichletParity χ : ℂ)+w by ring]
    field_simp [hN, hp, hΓ]
  rw [he, mul_pow, mul_pow]
  have hN2 : ((N : ℂ)^(w/2))^2 = (N : ℂ)^w := by
    rw [← Complex.cpow_mul_nat]
    congr 1
    ring
  have hp2 : ((Real.pi : ℂ)^(-w/2))^2 = (Real.pi : ℂ)^(-w) := by
    rw [← Complex.cpow_mul_nat]
    congr 1
    ring
  rw [hN2, hp2]

theorem squareSmooth_scale_power {N : ℕ} [NeZero N] (n : ℕ) (w : ℂ) :
    (N : ℂ)^w*(Real.pi : ℂ)^(-w)*(n : ℂ)^(-w) =
      ((Real.pi*(n : ℝ)/(N : ℝ) : ℝ) : ℂ)^(-w) := by
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (by positivity) (Nat.cast_nonneg N),
    Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (Nat.cast_nonneg n)]
  simp only [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv, inv_inv]
  ring

theorem dirichletSquareSeriesWeight_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    dirichletSquareSeriesWeight χ s n =
      squareSmoothWeight s (dirichletParity χ) (Real.pi*(n : ℝ)/(N : ℝ)) := by
  unfold dirichletSquareSeriesWeight squareSmoothWeight
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    dsimp only
    rw [dirichletSquareKernel, conductorGammaRatio_sq χ hs]
    unfold squareSmoothGammaContour
    rw [← squareSmooth_scale_power]
    ring

theorem dirichletL_square_eq_canonical_smooth_series {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (χ.LFunction s)^2 =
      (∑' n : ℕ, LSeries.term (dirichletDivisorCoefficients χ) s n *
        squareSmoothWeight s (dirichletParity χ) (Real.pi*(n : ℝ)/(N : ℝ))) +
      (dirichletSquareDualFactor χ s)^2 *
        (∑' n : ℕ, LSeries.term (dirichletDivisorCoefficients χ⁻¹) (1-s) n *
          squareSmoothWeight (1-s) (dirichletParity χ) (Real.pi*(n : ℝ)/(N : ℝ))) := by
  have h := dirichletL_square_eq_smooth_series χ hχ hprim hs0 hs1
  simp_rw [dirichletSquareSeriesWeight_eq χ hs0,
    dirichletSquareSeriesWeight_eq χ⁻¹ (by simp; linarith : 0 < (1-s).re),
    dirichletParity_inv] at h
  exact h

end
end Sechstmoment.Source

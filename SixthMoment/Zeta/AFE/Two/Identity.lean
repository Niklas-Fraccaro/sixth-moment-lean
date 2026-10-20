import SixthMoment.Zeta.AFE.Two.Gamma
import SixthMoment.Zeta.AFE.Two.Series

namespace SixthMoment
open Complex Real Source
open scoped BigOperators
noncomputable section

theorem d02SecondAFEPoleKiller_eq_correction {s r : ℂ}
    (hs : s≠0) (hs1 : s≠1) (hr : r≠0) (hr1 : r≠1) (z : ℂ) :
    d02SecondAFEPoleKiller s r z = Complex.exp (z^2)*secondPoleCorrection s r z := by
  rw [secondPoleCorrection_eq hs hs1 hr hr1]
  unfold d02SecondAFEPoleKiller d02SecondAFENormalization
  ring

theorem d02GammaRealPairRatio_eq {s r : ℂ} (hs : 0<s.re) (hr : 0<r.re) (z : ℂ) :
    (Gammaℝ (s+z)*Gammaℝ (r+z))/(Gammaℝ s*Gammaℝ r) =
      (Real.pi:ℂ)^(-z) *
        ((Gamma ((s+z)/2)/Gamma (s/2))*(Gamma ((r+z)/2)/Gamma (r/2))) := by
  have hpπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hgs : Gamma (s/2)≠0 :=
    Gamma_ne_zero_of_re_pos (by simp only [Complex.div_ofNat_re]; linarith)
  have hgr : Gamma (r/2)≠0 :=
    Gamma_ne_zero_of_re_pos (by simp only [Complex.div_ofNat_re]; linarith)
  have hps : (Real.pi:ℂ)^(-s/2)≠0 := cpow_ne_zero_iff.mpr (Or.inl hpπ)
  have hpr : (Real.pi:ℂ)^(-r/2)≠0 := cpow_ne_zero_iff.mpr (Or.inl hpπ)
  have hsplit (u : ℂ) : (Real.pi:ℂ)^(-(u+z)/2) =
      (Real.pi:ℂ)^(-u/2)*(Real.pi:ℂ)^(-z/2) := by
    rw [← Complex.cpow_add _ _ hpπ]
    congr 1
    ring
  have hpow : (Real.pi:ℂ)^(-z/2)*(Real.pi:ℂ)^(-z/2) = (Real.pi:ℂ)^(-z) := by
    rw [← Complex.cpow_add _ _ hpπ]
    congr 1
    ring
  simp only [Gammaℝ_def, hsplit]
  calc
    _ = ((Real.pi:ℂ)^(-z/2)*(Real.pi:ℂ)^(-z/2))*
        ((Gamma ((s+z)/2)/Gamma (s/2))*(Gamma ((r+z)/2)/Gamma (r/2))) := by
      field_simp
    _ = _ := by rw [hpow]

theorem d02SecondAFEKernel_eq_gammaKernel (t : ℝ) (α : SecondMomentShifts)
    (h0 : 0<(secondSourceZetaPoints t 0+α 0).re)
    (h1 : (secondSourceZetaPoints t 0+α 0).re<1)
    (h2 : 0<(secondSourceZetaPoints t 1+α 1).re)
    (h3 : (secondSourceZetaPoints t 1+α 1).re<1) (z : ℂ) :
    d02SecondAFEKernel (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) z =
        Complex.exp (z^2)/z * secondPoleCorrectedGammaQuotient t α z *
          (Real.pi:ℂ)^(-z) := by
  have hs0 : secondSourceZetaPoints t 0+α 0≠0 := by intro h; simp [h] at h0
  have hs1 : secondSourceZetaPoints t 0+α 0≠1 := by intro h; simp [h] at h1
  have hr0 : secondSourceZetaPoints t 1+α 1≠0 := by intro h; simp [h] at h2
  have hr1 : secondSourceZetaPoints t 1+α 1≠1 := by intro h; simp [h] at h3
  unfold d02SecondAFEKernel
  rw [mul_div_assoc, d02GammaRealPairRatio_eq h0 h2,
    d02SecondAFEPoleKiller_eq_correction hs0 hs1 hr0 hr1]
  unfold secondPoleCorrectedGammaQuotient secondGammaQuotient
  simp only [Fin.prod_univ_two]
  ring

theorem d02SecondAFEWeight_eq_gammaWeight (t : ℝ) (α : SecondMomentShifts)
    (h0 : 0<(secondSourceZetaPoints t 0+α 0).re)
    (h1 : (secondSourceZetaPoints t 0+α 0).re<1)
    (h2 : 0<(secondSourceZetaPoints t 1+α 1).re)
    (h3 : (secondSourceZetaPoints t 1+α 1).re<1) (x : ℝ) :
    d02SecondAFEWeight (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) x =
        (1/(2*Real.pi):ℂ)*∫ v : ℝ,
          Complex.exp ((1+(v:ℂ)*I)^2)/(1+(v:ℂ)*I) *
            secondPoleCorrectedGammaQuotient t α (1+(v:ℂ)*I) *
              (Real.pi:ℂ)^(-(1+(v:ℂ)*I))*(x:ℂ)^(-(1+(v:ℂ)*I)) := by
  unfold d02SecondAFEWeight
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only
    rw [d02SecondAFEKernel_eq_gammaKernel t α h0 h1 h2 h3]

end
end SixthMoment

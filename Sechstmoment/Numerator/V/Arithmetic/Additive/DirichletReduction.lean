import Sechstmoment.Numerator.V.Arithmetic.FourChiInsertion
import Sechstmoment.Numerator.V.Arithmetic.FourDirichletPNatMass
import Sechstmoment.Numerator.V.Arithmetic.SeriesReplacement
import Sechstmoment.Numerator.V.Chi.ShiftedGlobalChiKernel


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open NoDPGlobalLFactorization
open scoped BigOperators ContDiff
noncomputable section

def noDPFourChiMoment (w : ℝ → ℂ) (T c N : ℝ) (u : ℂ) (β : Fin 4 → ℂ) : ℂ :=
  (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
    (zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T))*
      ((N:ℂ)^((c:ℂ)+(t:ℂ)*I)*∏ j : Fin 4, riemannZeta ((c:ℂ)+(t:ℂ)*I+β j)))

def noDPAdditiveChiTerm (w : ℝ → ℂ) (T N : ℝ) (u : ℂ)
    (β : Fin 4 → ℂ) (m : ℕ+) : ℂ :=
  fourAF β m*(Complex.exp (I*((-2*Real.pi*((m:ℝ)/N):ℝ):ℂ))*
    noDPTimeWeight w T u (2*Real.pi*((m:ℝ)/N)/T))

theorem four_zeta_chi_additive_reduction {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 64 (100*Real.pi) ≤ T →
      4*(2*R+2) ≤ Real.log T → ∀ u : ℂ, ‖u‖ ≤ R/Real.log T →
      ∀ β : Fin 4 → ℂ, (∀ j, ‖β j‖ ≤ R/Real.log T) → ∀ N : ℝ, 0 < N →
      Summable (noDPAdditiveChiTerm w T N u β) ∧
      ‖noDPFourChiMoment w T (noDPRightLine T R) N u β-
        ∑' m : ℕ+, noDPAdditiveChiTerm w T N u β m‖ ≤
        C*N^(noDPRightLine T R)*T^(1/2:ℝ)*(Real.log T)^4 := by
  obtain ⟨D,hD,hkernel⟩ := smooth_dyadic_shifted_chi_global_error hw hws hR
  obtain ⟨E,hE,hmass⟩ := fourAF_scaled_log_line_absolute_mass_bound
  refine ⟨D*E,by positivity,?_⟩
  intro T hT hL u hu β hβ N hN
  have hT64 : 64 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by linarith
  have hL1 : 1 ≤ Real.log T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨hc,hsmall,_hcline⟩ := noDPRightLine_chi_shift_geometry hR hL hu
  have him : |u.im| ≤ T/2 := (Complex.abs_im_le_norm u).trans
    (hsmall.trans (by linarith))
  have hgap (j : Fin 4) : 1+1/Real.log T ≤ noDPRightLine T R+(β j).re := by
    simpa using noDPRightLine_shift_lower hL1 (hβ j) 0
  have hstrict (j : Fin 4) : 1 < noDPRightLine T R+(β j).re :=
    lt_of_lt_of_le (by linarith [one_div_pos.mpr hL0]) (hgap j)
  let F : ℕ+ → ℂ := fun m =>
    fourAF β m*noDPChiTimeTransform w T (noDPRightLine T R) u ((m:ℝ)/N)
  let G : ℕ+ → ℂ := noDPAdditiveChiTerm w T N u β
  let p : ℕ+ → ℝ := fun m =>
    (D*T^(1/2:ℝ))*(‖fourAF β m‖*((m:ℝ)/N)^(-noDPRightLine T R))
  have Hseries : HasSum F (noDPFourChiMoment w T (noDPRightLine T R) N u β) :=
    four_zeta_chi_time_series_insertion hw.continuous hws hT1 hN
      ⟨by linarith [hc.1],by linarith [hc.2]⟩ him hstrict
  obtain ⟨habs,Hmass⟩ := hmass T R hL1 β hβ N hN
  have hp : Summable p := habs.mul_left (D*T^(1/2:ℝ))
  have Hpoint (m : ℕ+) : ‖F m-G m‖ ≤ p m := by
    have hm : 0 < (m:ℝ)/N := div_pos (by exact_mod_cast m.pos) hN
    dsimp only [F,G,noDPAdditiveChiTerm,p]
    rw [← mul_sub,norm_mul]
    calc
      _ ≤ ‖fourAF β m‖*(D*((m:ℝ)/N)^(-noDPRightLine T R)*T^(1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left (hkernel T hT hL u hu _ hm) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨hG,Herror⟩ := summable_series_replacement_bound Hseries.summable hp Hpoint
  refine ⟨hG,?_⟩
  change ‖(noDPFourChiMoment w T (noDPRightLine T R) N u β)-(∑' m, G m)‖ ≤ _
  rw [← Hseries.tsum_eq]
  apply Herror.trans
  dsimp only [p]
  rw [tsum_mul_left]
  have H := mul_le_mul_of_nonneg_left Hmass
    (show 0 ≤ D*T^(1/2:ℝ) by positivity)
  convert H using 1; ring

end
end Sechstmoment.Source

import Sechstmoment.Numerator.U.MainTerm.DyadicSixPhaseLimit
import Sechstmoment.Numerator.U.MainTerm.PrincipalDominatedLimit


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualSixPrincipalMoment (T : ℝ) (σ : MomentShifts) (f g : ℝ → ℂ)
    (Φ : ℝ → ℝ) (δ : ℝ) : ℂ :=
  ∫ t : ℝ, ∑ m : Fin 6, (Φ (t/T):ℂ)*
    (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
    (((Real.log T:ℂ)/(2*π))^2*
      actualPrincipalProfileIntegral T σ m f g (Real.log T) δ δ)

def actualSixPrincipalPolarLimit (σ : MomentShifts) (f g : ℝ → ℂ)
    (Φ : ℝ → ℝ) (c : ℝ) : ℂ :=
  (∫ x : ℝ, (Φ x:ℂ))*∑ m : Fin 6, Complex.exp (bblrSixPhaseExponents σ m)*
    ((1/(2*π):ℂ)^2*∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
      ∂(volume.prod volume))

theorem actualSixPrincipalMoment_time_integrable {T : ℝ} (hT : 0 < T)
    (σ : MomentShifts) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (δ : ℝ) :
    Integrable (fun t : ℝ => ∑ m : Fin 6, (Φ (t/T):ℂ)*
      (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
      (((Real.log T:ℂ)/(2*π))^2*
        actualPrincipalProfileIntegral T σ m f g (Real.log T) δ δ)) := by
  apply integrable_finsetSum
  intro m _
  exact (dyadicComplexPowerWeight_integrable hT
    (bblrSixPhaseExponents (rawMomentShifts T σ) m) Φ hΦ).mul_const _

theorem actualSixPrincipalMoment_eq_time_products {T : ℝ} (hT : 0 < T)
    (σ : MomentShifts) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (δ : ℝ) :
    actualSixPrincipalMoment T σ f g Φ δ = ∑ m : Fin 6,
      (∫ t : ℝ, (Φ (t/T):ℂ)*
        (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m))*
      (((Real.log T:ℂ)/(2*π))^2*
        actualPrincipalProfileIntegral T σ m f g (Real.log T) δ δ) := by
  unfold actualSixPrincipalMoment
  rw [integral_finsetSum Finset.univ (fun m _ =>
    (dyadicComplexPowerWeight_integrable hT
      (bblrSixPhaseExponents (rawMomentShifts T σ) m) Φ hΦ).mul_const _)]
  apply Finset.sum_congr rfl
  intro m _
  exact integral_mul_const _ _

theorem actualSixPrincipalMoment_eventually_rescaled {R c δ : ℝ}
    (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hδ : 0 < δ)
    (σ : MomentShifts) (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop, actualSixPrincipalMoment T σ f g Φ δ = ∑ m : Fin 6,
      (∫ t : ℝ, (Φ (t/T):ℂ)*
        (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m))*
      ((1/(2*π):ℂ)^2*∫ y : ℝ × ℝ,
        actualPrincipalProfileRescaledKernel T σ m f g (Real.log T) c c y
          ∂(volume.prod volume)) := by
  have hcp : 0 < c := by linarith
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (4*c)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (c/δ))] with T hT hL hLδ
  have hLp : 0 < Real.log T := Real.log_pos hT
  have hεp : 0 < c/Real.log T := div_pos hcp hLp
  have hε1 : c/Real.log T < 1/4 := (div_lt_iff₀ hLp).mpr (by linarith)
  have hεδ : c/Real.log T ≤ δ := (div_le_iff₀ hLp).mpr (by
    have h := (div_lt_iff₀ hδ).mp hLδ
    linarith)
  have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ (c/Real.log T)/4 := by
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hLp.le]
    have hRc : R ≤ c/4 := by linarith
    calc
      _ ≤ (c/4)/Real.log T := div_le_div_of_nonneg_right ((hσ j).trans hRc) hLp.le
      _ = _ := by ring
  rw [actualSixPrincipalMoment_eq_time_products (zero_lt_one.trans hT) σ f g Φ hΦ δ]
  apply Finset.sum_congr rfl
  intro m _
  rw [actualPrincipalProfileIntegral_double_shift T σ m hf hfs hg hgs hLp hεp hε1 hraw hεδ,
    actualPrincipalProfileIntegral_log_rescaling T σ m hf hfs hg hgs hLp hεp hε1 hraw le_rfl le_rfl]

theorem actualSixPrincipalMoment_polar_limit {R c δ : ℝ}
    (hR : 0 ≤ R) (hc : 4*R+1 ≤ c) (hδ : 0 < δ)
    (σ : MomentShifts) (hσ : ∀ j : Fin 4, ‖σ j‖ ≤ R)
    (hρ : ∀ k : PurePolarIndex, normalizedPurePolarRoot σ k ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => actualSixPrincipalMoment T σ f g Φ δ/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop (𝓝 (actualSixPrincipalPolarLimit σ f g Φ c)) := by
  have hlim (m : Fin 6) :=
    (bblrSixPhaseWeight_normalized_tendsto σ m Φ hΦ).mul
      ((actualPrincipalProfileRescaledIntegral_polar_limit hR hc σ hσ m
        (fun ij => hρ (m,ij)) hf hfs hg hgs).const_mul ((1/(2*π):ℂ)^2))
  have hs := tendsto_finsetSum Finset.univ (fun m _ => hlim m)
  have heq : (∑ m : Fin 6,
      ((∫ x : ℝ, (Φ x:ℂ))*Complex.exp (bblrSixPhaseExponents σ m))*
        ((1/(2*π):ℂ)^2*∫ y : ℝ × ℝ, actualPrincipalPolarLimitKernel σ m f g c c y
          ∂(volume.prod volume))) = actualSixPrincipalPolarLimit σ f g Φ c := by
    unfold actualSixPrincipalPolarLimit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [heq] at hs
  apply hs.congr'
  filter_upwards [actualSixPrincipalMoment_eventually_rescaled hR hc hδ σ hσ hf hfs hg hgs Φ hΦ]
    with T hT
  rw [hT,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_div]
  ring

end
end Sechstmoment

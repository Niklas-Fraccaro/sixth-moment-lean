import SixthMoment.Denominator.Balanced.ZetaGaussianMomentError
import SixthMoment.Denominator.Unbalanced.ActualOffDiagonal

namespace SixthMoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04_profiles_uniform_absolute_bound (a : Fin 4 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j)) :
    ∃ F : ℝ,0≤F ∧ ∀ j x,|ρ j x|≤F := by
  have hb : ∀ j : Fin 4,∃ M : ℝ,0≤M ∧ ∀ x,|ρ j x|≤M :=
    fun j => d02Continuous_supported_norm_bound (hρ j) (hρs j)
  choose M hM hm using hb
  refine ⟨∑ j,M j,Finset.sum_nonneg (fun j _ => hM j),?_⟩
  intro j x
  exact (hm j x).trans (Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j))

theorem d04_oneSided_model_offDiagonal_normalized_uniform_small {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    (a : Fin 4 → ℝ) (ha : ∀ j,0≤a j) (haP : a 0+a 1+a 2<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    {R R' : ℝ} (hR : 0≤R) (hR' : 0≤R') {η : ℝ} (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ (σ : Fin 2 → ℂ) (τ : ℂ),
      (∀ j,‖σ j‖≤R) → ‖τ‖≤R' →
      ‖d04OneSidedModelOffDiagonal T a ρ σ τ Φ/(T*(Real.log T)^9 : ℂ)‖<η := by
  obtain ⟨F,hF,hρF⟩ := d04_profiles_uniform_absolute_bound a ρ hρ hρs
  obtain ⟨D,hD,hd⟩ := d04_oneSided_model_offDiagonal_uniform_power_bound
    hΦ hΦs a ha haP hR hR' hF 1
  have hb : ∀ᶠ T : ℝ in atTop,∀ u : (Fin 2 → ℂ) × ℂ,
      ((∀ j,‖u.1 j‖≤R) ∧ ‖u.2‖≤R') →
      ‖d04OneSidedModelOffDiagonal T a ρ u.1 u.2 Φ‖≤D*T^(-1 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (2*R)))] with T hT hL
    intro u hu
    exact hd T hT ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)
      ρ u.1 u.2 hρF hu.1 hu.2
  have hs := d02PowerHeight_normalized_uniform_small
    (fun T (u : (Fin 2 → ℂ) × ℂ) => d04OneSidedModelOffDiagonal T a ρ u.1 u.2 Φ)
    (fun u => (∀ j,‖u.1 j‖≤R) ∧ ‖u.2‖≤R') (by norm_num : (-1 : ℝ)<1) hb hη
  filter_upwards [hs] with T hT
  intro σ τ hσ hτ
  exact hT (σ,τ) ⟨hσ,hτ⟩

theorem d04_oneSided_model_offDiagonal_normalized_tendsto {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    (a : Fin 4 → ℝ) (ha : ∀ j,0≤a j) (haP : a 0+a 1+a 2<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (σ : ℝ → Fin 2 → ℂ) (τ : ℝ → ℂ)
    {R R' : ℝ} (hR : 0≤R) (hR' : 0≤R')
    (hσ : ∀ᶠ T : ℝ in atTop,∀ j,‖σ T j‖≤R)
    (hτ : ∀ᶠ T : ℝ in atTop,‖τ T‖≤R') :
    Tendsto (fun T : ℝ => d04OneSidedModelOffDiagonal T a ρ (σ T) (τ T) Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [d04_oneSided_model_offDiagonal_normalized_uniform_small
    hΦ hΦs a ha haP ρ hρ hρs hR hR' hη,hσ,hτ] with T hT hσT hτT
  simpa only [dist_eq_norm,sub_zero] using hT (σ T) (τ T) hσT hτT

end
end SixthMoment

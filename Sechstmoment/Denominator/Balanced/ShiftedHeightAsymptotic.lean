import Sechstmoment.Denominator.Balanced.FiniteGaussianDiagonalPhysical

/-! The actual balanced shifted zeta height moment: the proved Gamma,
long-sum and off-diagonal errors leave precisely the original D01 endpoint. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Filter Set Metric
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d02UnitCircleShift_norm_le {z w : ℂ}
    (hz : z∈sphere (0:ℂ) 1) (hw : w∈sphere (0:ℂ) 1) :
    ∀ j : Fin 2,‖(![z,w]:SecondMomentShifts) j‖≤1 := by
  intro j
  fin_cases j
  · change ‖z‖≤1
    exact (mem_sphere_zero_iff_norm.mp hz).le
  · change ‖w‖≤1
    exact (mem_sphere_zero_iff_norm.mp hw).le

theorem d02Balanced_length_saving_parameters (a : Fin 4 → ℝ)
    (ha : ∀ j,0<a j) (hS : (∑ j,a j)<1) :
    0<(1-(∑ j,a j))/8 ∧ (1-(∑ j,a j))/8≤1/4 ∧
      1/2+2*((1-(∑ j,a j))/8)+(∑ j,a j)/2<1 ∧
      0<(1-(∑ j,a j))/2 ∧ (1-(∑ j,a j))/2<1-(∑ j,a j) := by
  have hS0 : 0≤∑ j,a j := Finset.sum_nonneg (fun j _ => (ha j).le)
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem d02BalancedShiftedMoment_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ j,0<a j) (hS : (∑ j,a j)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {z w : ℂ} (hz : z∈sphere (0:ℂ) 1) (hw : w∈sphere (0:ℂ) 1) :
    Tendsto (fun T : ℝ => d02BalancedShiftedMoment T ![z,w] ρ Φ/
      (T*(Real.log T)^9:ℂ)) atTop
      (𝓝 (((arithmeticFactor*(∫ t : ℝ,Φ t):ℝ):ℂ)*d02BalancedShiftedEdgeIntegral ρ ![z,w])) := by
  let ε : ℝ := (1-(∑ j,a j))/8
  let δ : ℝ := (1-(∑ j,a j))/2
  obtain ⟨hε,hε1,hsaving,hδ,hδS⟩ := d02Balanced_length_saving_parameters a ha hS
  have hσ := d02UnitCircleShift_norm_le hz hw
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs j (subset_tsupport (ρ j) hn)).2
  have hAG := d02ActualMomentComparison_normalized_tendsto hε hε1 a hsaving
    ρ hρ hρs Φ hΦ.continuous hΦs hz hw
  have hGF := d02BalancedGaussianMoment_truncation_normalized_tendsto
    (R := 1) (ε := ε) (δ := δ) zero_le_one hε hε1 hδ a hS
    ρ hρ hρs Φ hΦ.continuous hΦs ![z,w] hσ
  have hO := d02GaussianFiniteOffDiagonalMoment_normalized_tendsto
    (R := 1) (δ := δ) zero_le_one a hδS ρ hρ hρs Φ hΦ hΦs ![z,w] hσ
  have hD := d02GaussianFiniteDiagonalMoment_normalized_tendsto
    (R := 1) (δ := δ) zero_le_one hδ.le a ρ hρ hρs Φ hΦ.continuous hΦs ![z,w] hσ
  have h := ((hAG.add hGF).add hO).add hD
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have he := d02BalancedGaussianFiniteMoment_diagonal_add_offDiagonal
    hT ![z,w] a ρ hcap Φ hΦ hΦs δ
  simp only [div_eq_mul_inv]
  rw [he]
  ring

theorem d02BalancedShiftedMoment_eventually_uniform_circle_bound
    (a : Fin 4 → ℝ) (ha : ∀ j,0<a j) (hS : (∑ j,a j)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ T : ℝ in atTop,∀ z∈sphere (0:ℂ) 1,∀ w∈sphere (0:ℂ) 1,
      ‖d02BalancedShiftedMoment T ![z,w] ρ Φ/(T*(Real.log T)^9:ℂ)‖≤B := by
  let ε : ℝ := (1-(∑ j,a j))/8
  let δ : ℝ := (1-(∑ j,a j))/2
  obtain ⟨hε,hε1,hsaving,hδ,hδS⟩ := d02Balanced_length_saving_parameters a ha hS
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs j (subset_tsupport (ρ j) hn)).2
  obtain ⟨C,_hC,herr⟩ := d02ZetaGaussianMomentError_uniform_bound
    (R := 1) (ε := ε) zero_le_one hε hε1 a ρ hρ hρs Φ hΦ.continuous hΦs
  have hsmall := d02PowerHeight_normalized_uniform_small
    (fun T σ => d02ZetaGaussianMomentError T σ ρ Φ)
    (fun σ => ∀ j,‖σ j‖≤1) hsaving herr (by norm_num : (0:ℝ)<1)
  obtain ⟨B,hB,hdiag⟩ := d02GaussianFiniteDiagonalMoment_normalized_uniform_bound
    (R := 1) (δ := δ) zero_le_one hδ.le a ρ hρ hρs Φ hΦ.continuous hΦs
  refine ⟨B+3,by positivity,?_⟩
  filter_upwards [hsmall,hdiag,
    d02ActualMomentComparison_eventually (ε := ε) hε hε1 a ρ hρ hρs Φ hΦ.continuous hΦs,
    d02BalancedGaussianMoment_truncation_normalized_eventually_norm_le_one
      (R := 1) (ε := ε) (δ := δ) zero_le_one hε hε1 hδ a hS
      ρ hρ hρs Φ hΦ.continuous hΦs,
    d02GaussianFiniteOffDiagonalMoment_normalized_uniform_small
      (R := 1) (δ := δ) zero_le_one a hδS ρ hρ hρs Φ hΦ hΦs
      (by norm_num : (0:ℝ)<1),eventually_gt_atTop (1:ℝ)]
      with T hsmall hdiag hcompare htail hoff hT
  intro z hz w hw
  have hσ := d02UnitCircleShift_norm_le hz hw
  have hAG : ‖(d02BalancedShiftedMoment T ![z,w] ρ Φ-
      d02BalancedGaussianMoment T ![z,w] ρ Φ)/(T*(Real.log T)^9:ℂ)‖≤1 := by
    rw [hcompare z hz w hw]
    exact (hsmall ![z,w] hσ).le
  have hGF := (htail ![z,w] hσ).2
  have hO := (hoff ![z,w] hσ).le
  have hD := hdiag ![z,w] hσ
  have hpartition := d02BalancedGaussianFiniteMoment_diagonal_add_offDiagonal
    hT ![z,w] a ρ hcap Φ hΦ hΦs δ
  have he : d02BalancedShiftedMoment T ![z,w] ρ Φ/(T*(Real.log T)^9:ℂ)=
      (((d02BalancedShiftedMoment T ![z,w] ρ Φ-d02BalancedGaussianMoment T ![z,w] ρ Φ)/
          (T*(Real.log T)^9:ℂ)+
        (d02BalancedGaussianMoment T ![z,w] ρ Φ-d02BalancedGaussianFiniteMoment T ![z,w] ρ Φ δ)/
          (T*(Real.log T)^9:ℂ))+
        d02GaussianFiniteOffDiagonalMoment T ![z,w] ρ Φ a δ/(T*(Real.log T)^9:ℂ))+
        d02GaussianFiniteDiagonalMoment T ![z,w] ρ Φ a δ/(T*(Real.log T)^9:ℂ) := by
    simp only [div_eq_mul_inv]
    rw [hpartition]
    ring
  rw [he]
  calc
    _ ≤ ((1+1)+1)+B := (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add hAG hGF)) hO)) hD)
    _ = B+3 := by ring

end
end Sechstmoment

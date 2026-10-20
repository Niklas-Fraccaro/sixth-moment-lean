import SixthMoment.Denominator.Balanced.ActualCircleFubini
import SixthMoment.Denominator.Balanced.GaussianMomentRegularity

namespace SixthMoment
open Complex Real Source MeasureTheory Filter Set Metric
open scoped BigOperators Topology
noncomputable section

def d02BalancedGaussianMoment (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*d02CenteredGaussianPair T t σ

theorem d02ActualMomentComparison_eventually {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/4)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∀ᶠ T : ℝ in atTop,∀ z∈sphere (0:ℂ) 1,∀ w∈sphere (0:ℂ) 1,
      d02BalancedShiftedMoment T ![z,w] ρ Φ-d02BalancedGaussianMoment T ![z,w] ρ Φ =
        d02ZetaGaussianMomentError T ![z,w] ρ Φ := by
  filter_upwards [d02CenteredGaussianMoment_eventually_integrable
    (R := 1) zero_le_one hε hε1 a ρ hρ hs Φ hΦ hΦs,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1:ℝ))] with T hG hT hL
  intro z hz w hw
  have hσ : ∀ j : Fin 2,‖(![z,w] : SecondMomentShifts) j‖≤1 := by
    intro j
    fin_cases j
    · change ‖z‖≤1
      exact (mem_sphere_zero_iff_norm.mp hz).le
    · change ‖w‖≤1
      exact (mem_sphere_zero_iff_norm.mp hw).le
  have hactual := d02BalancedShiftedMoment_integrable_of_mem_circles
    hT hL hz hw ρ a hs Φ hΦ hΦs
  have hmodel := hG ![z,w] hσ
  unfold d02BalancedShiftedMoment d02BalancedGaussianMoment d02ZetaGaussianMomentError
  change (∫ t : ℝ,(Φ (t/T):ℂ)*zetaCPlus T t z*zetaCMinus T t w*
      d02BalancedAmplifier T t ρ)-
    (∫ t : ℝ,(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
      d02CenteredGaussianPair T t ![z,w]) =
    ∫ t : ℝ,(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
      (zetaCPlus T t z*zetaCMinus T t w-d02CenteredGaussianPair T t ![z,w])
  rw [←integral_sub hactual hmodel]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change (Φ (t/T):ℂ)*zetaCPlus T t z*zetaCMinus T t w*d02BalancedAmplifier T t ρ-
      (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*d02CenteredGaussianPair T t ![z,w] = _
    ring

theorem d02ActualMomentComparison_normalized_tendsto {ε : ℝ}
    (hε : 0<ε) (hε1 : ε≤1/4) (a : Fin 4 → ℝ)
    (hsaving : 1/2+2*ε+(∑ i,a i)/2<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {z w : ℂ} (hz : z∈sphere (0:ℂ) 1) (hw : w∈sphere (0:ℂ) 1) :
    Tendsto (fun T : ℝ => (d02BalancedShiftedMoment T ![z,w] ρ Φ-
      d02BalancedGaussianMoment T ![z,w] ρ Φ)/(T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  have hσ : ∀ j : Fin 2,‖(![z,w] : SecondMomentShifts) j‖≤1 := by
    intro j
    fin_cases j
    · change ‖z‖≤1
      exact (mem_sphere_zero_iff_norm.mp hz).le
    · change ‖w‖≤1
      exact (mem_sphere_zero_iff_norm.mp hw).le
  apply (d02ZetaGaussianMomentError_normalized_tendsto zero_le_one hε hε1
    a hsaving ρ hρ hs Φ hΦ hΦs ![z,w] hσ).congr'
  filter_upwards [d02ActualMomentComparison_eventually hε hε1 a ρ hρ hs Φ hΦ hΦs] with T hT
  rw [hT z hz w hw]

end
end SixthMoment

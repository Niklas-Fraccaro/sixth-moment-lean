import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.DenselyOrdered
import Sechstmoment.Analysis.Beta.WeakConvergence
import Sechstmoment.Analysis.Profiles.Endpoint

namespace Sechstmoment

open Filter MeasureTheory

theorem vEndpointProfile_zero_below (η a : ℝ) (n : ℕ) {x : ℝ} (hx : x < 0) :
    vEndpointProfile η a n x = 0 := by
  apply Set.indicator_of_notMem
  exact fun h => (not_le_of_gt hx) h.1

theorem vEndpointProfile_support (η a : ℝ) (n : ℕ) :
    Function.support (vEndpointProfile η a n) ⊆ Set.Icc (0 : ℝ) η := by
  intro x hx
  by_contra h
  have hz : vEndpointProfile η a n x = 0 := Set.indicator_of_notMem h _
  exact hx hz

theorem vEndpointProfile_nonneg {η : ℝ} (hη : 0 < η) (a : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ vEndpointProfile η a n x := by
  unfold vEndpointProfile
  by_cases hx : x ∈ Set.Icc (0 : ℝ) η
  · rw [Set.indicator_of_mem hx]
    exact betaScaled_nonneg hη n _ hx
  · rw [Set.indicator_of_notMem hx]

theorem vEndpointProfile_integrable (η a : ℝ) (n : ℕ) :
    Integrable (vEndpointProfile η a n) volume := by
  have hi : IntegrableOn (betaScaledProfile η n (betaProfileIndex η a n))
      (Set.Icc (0 : ℝ) η) volume :=
    (betaScaled_continuous η n _).continuousOn.integrableOn_Icc
  exact hi.integrable_indicator measurableSet_Icc

theorem vEndpointProfile_mass {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (haη : a ≤ η)
    (n : ℕ) : (∫ x : ℝ, vEndpointProfile η a n x) = 1 := by
  unfold vEndpointProfile
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hη.le,
    betaScaled_mass hη.ne' (betaProfileIndex_le hη ha haη n)]

theorem vEndpointProfile_test_integral {η : ℝ} (hη : 0 < η) (a : ℝ) (n : ℕ)
    (g : ℝ → ℝ) :
    (∫ x : ℝ, g x * vEndpointProfile η a n x) =
      ∫ x in (0 : ℝ)..η, g x * betaScaledProfile η n (betaProfileIndex η a n) x := by
  have he (x : ℝ) : g x * vEndpointProfile η a n x =
      (Set.Icc (0 : ℝ) η).indicator
        (fun x => g x * betaScaledProfile η n (betaProfileIndex η a n) x) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) η
    · simp [vEndpointProfile, Set.indicator_of_mem hx]
    · simp [vEndpointProfile, Set.indicator_of_notMem hx]
  simp_rw [he]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hη.le]

theorem vEndpointProfile_continuous_test_tendsto {η a : ℝ} (hη : 0 < η)
    (ha : 0 ≤ a) (haη : a ≤ η) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) η)) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, g x * vEndpointProfile η a n x)
      atTop (nhds (g a)) := by
  simp_rw [vEndpointProfile_test_integral hη]
  exact betaProfile_continuous_test_tendsto hη ha haη g hg

theorem vEndpointProfile_continuous_of_endpoints {η a : ℝ} (hη : 0 < η) (n : ℕ)
    (he : betaScaledProfile η n (betaProfileIndex η a n) 0 = 0 ∧
      betaScaledProfile η n (betaProfileIndex η a n) η = 0) :
    Continuous (vEndpointProfile η a n) := by
  unfold vEndpointProfile
  apply (betaScaled_continuous η n _).indicator
  intro x hx
  rw [frontier_Icc hη.le] at hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact he.1
  · have hxη : x = η := Set.mem_singleton_iff.mp hx
    subst x
    exact he.2

theorem vEndpointProfile_continuous_eventually {η a : ℝ} (hη : 0 < η)
    (ha : 0 < a) (haη : a < η) :
    ∀ᶠ n : ℕ in atTop, Continuous (vEndpointProfile η a n) := by
  filter_upwards [betaProfile_endpoints_eventually hη ha haη] with n hn
  exact vEndpointProfile_continuous_of_endpoints hη n hn

end Sechstmoment

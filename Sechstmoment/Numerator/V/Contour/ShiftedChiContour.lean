import Sechstmoment.Numerator.V.Contour.AlmostHolomorphicContour
import Sechstmoment.Numerator.V.Contour.ShiftedChiFactor


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped Topology BigOperators ContDiff
noncomputable section

theorem shiftedChiProfileFactor_smooth_shift {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T → ∀ a b : ℝ, ∀ f g : ℝ → ℝ,
      (∀ x, a < x → f x = 0) → (∀ x, b < x → g x = 0) →
      ∀ u : ℂ, ‖u‖ ≤ 1/8 → ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ c : ℝ, c ∈ Icc (1/2 : ℝ) (5/4) →
      ‖(∫ t in T/2..3*T, shiftedChiProfileFactor T u α f g ((c : ℂ)+(t : ℂ)*I)*
          almostHolomorphicWeight w K T c t)-
        (∫ t in T/2..3*T, shiftedChiProfileFactor T u α f g ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T))‖ ≤
        C*profileContourMass T a f*profileContourMass T b g*T^13/T^(K+1) := by
  obtain ⟨A,hA,hbound⟩ := shiftedChiProfileFactor_norm_bound
  obtain ⟨D,hD,hshift⟩ := almostHolomorphic_vertical_shift_bound hw hws K
  refine ⟨3*A*4^12*D,by positivity,?_⟩
  intro T hT a b f g hf hg u hu α hα c hc
  have hTpos : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hgeo (s : ℂ) (hs : s ∈ Icc (1/2 : ℝ) c ×ℂ Icc (T/2) (3*T)) :
      s.re ∈ Icc (1/2 : ℝ) (5/4) ∧ 40 ≤ |s.im| ∧ 1+|s.im| ≤ 4*T := by
    have ht : 0 ≤ s.im := by linarith [hs.2.1]
    rw [abs_of_nonneg ht]
    exact ⟨⟨hs.1.1,hs.1.2.trans hc.2⟩,by linarith [hs.2.1],by linarith [hs.2.2]⟩
  have hhol : ∀ s ∈ Icc (1/2 : ℝ) c ×ℂ Icc (T/2) (3*T),
      DifferentiableAt ℂ (shiftedChiProfileFactor T u α f g) s := by
    intro s hs
    have hh := hgeo s hs
    exact shiftedChiProfileFactor_differentiableAt hT1 a b f g hf hg α hh.2.1 hu hα
  let M : ℝ := A*(4*T)^12*profileContourMass T a f*profileContourMass T b g
  have hMf := profileContourMass_nonneg T a f
  have hMg := profileContourMass_nonneg T b g
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (mul_nonneg (by positivity) (profileContourMass_nonneg T a f))
      (profileContourMass_nonneg T b g)
  have hnorm : ∀ s ∈ Icc (1/2 : ℝ) c ×ℂ Icc (T/2) (3*T),
      ‖shiftedChiProfileFactor T u α f g s‖ ≤ M := by
    intro s hs
    have hh := hgeo s hs
    exact (hbound T hT1 a b f g hf hg u hu α hα s hh.1 hh.2.1).trans (by
      dsimp only [M]
      gcongr
      exact hh.2.2)
  have h := hshift T hTpos c ⟨hc.1,by linarith [hc.2]⟩
    (shiftedChiProfileFactor T u α f g) hhol M hM hnorm
  calc
    _ ≤ (c-1/2)*(3*T)*M*D/T^(K+1) := h
    _ ≤ 1*(3*T)*M*D/T^(K+1) := by
      gcongr
      linarith [hc.2]
    _ = _ := by dsimp only [M]; ring

theorem shiftedChiProfileFactor_smooth_shift_integral {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 80 ≤ T → ∀ a b : ℝ, ∀ f g : ℝ → ℝ,
      (∀ x, a < x → f x = 0) → (∀ x, b < x → g x = 0) →
      ∀ u : ℂ, ‖u‖ ≤ 1/8 → ∀ α : Fin 4 → ℂ, (∀ j, ‖α j‖ ≤ 1/8) →
      ∀ c : ℝ, c ∈ Icc (1/2 : ℝ) (5/4) →
      ‖(∫ t : ℝ, shiftedChiProfileFactor T u α f g ((c : ℂ)+(t : ℂ)*I)*
          almostHolomorphicWeight w K T c t)-
        (∫ t : ℝ, shiftedChiProfileFactor T u α f g ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T))‖ ≤
        C*profileContourMass T a f*profileContourMass T b g*T^13/T^(K+1) := by
  obtain ⟨C,hC,hbound⟩ := shiftedChiProfileFactor_smooth_shift hw hws K
  refine ⟨C,hC,?_⟩
  intro T hT a b f g hf hg u hu α hα c hc
  have hTpos : 0 < T := by linarith
  have hright := almostHolomorphicWeight_integral_eq_interval hws K hTpos c
    (fun t => shiftedChiProfileFactor T u α f g ((c : ℂ)+(t : ℂ)*I))
  have hleft := almostHolomorphicWeight_integral_eq_interval hws K hTpos (1/2)
    (fun t => shiftedChiProfileFactor T u α f g ((1/2 : ℂ)+(t : ℂ)*I))
  simp only [almostHolomorphicWeight_left_boundary] at hleft
  rw [hright,hleft]
  exact hbound T hT a b f g hf hg u hu α hα c hc

end
end Sechstmoment.Source

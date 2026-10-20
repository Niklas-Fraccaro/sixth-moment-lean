import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Polynomial
import Sechstmoment.Analysis.Harmonic.Simplex


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

def reversedPolynomial (η : ℝ) (P : ℝ[X]) (t : ℝ) : ℂ := ((P.eval (t/η):ℝ):ℂ)

theorem reversedPolynomial_hasDerivAt (η : ℝ) (P : ℝ[X]) (t : ℝ) :
    HasDerivAt (reversedPolynomial η P) ((P.derivative.eval (t/η)/η:ℝ):ℂ) t := by
  unfold reversedPolynomial
  convert (((P.hasDerivAt (t/η)).comp t ((hasDerivAt_id t).div_const η)).ofReal_comp) using 1 <;>
    simp [div_eq_mul_inv]

theorem reversedPolynomial_regular (η : ℝ) (P : ℝ[X]) :
    ∃ B D : ℝ, RegularProfile η (reversedPolynomial η P) B D := by
  have hc : Continuous (reversedPolynomial η P) := by unfold reversedPolynomial; fun_prop
  have hdc : Continuous (fun t : ℝ => ((P.derivative.eval (t/η)/η:ℝ):ℂ)) := by fun_prop
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) η)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) η)).exists_bound_of_continuousOn hdc.continuousOn
  refine ⟨max 0 B,max 0 D,regularProfile_of_bounds (le_max_left _ _) (le_max_left _ _) ?_ ?_⟩
  · intro x hx
    exact (hB x hx).trans (le_max_right _ _)
  · intro x hx y hy
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (0:ℝ) η).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (reversedPolynomial_hasDerivAt η P t).hasDerivWithinAt)
        (fun t ht => (hD t ht).trans (le_max_right _ _)) hy hx

def polynomialTripleSum (η L : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) (d : ℕ) : ℂ :=
  rawIter L [ν₁,ν₂,ν₃] (reversedPolynomial η P) (clippedTime η L d)

def polynomialSimplexIntegral (η : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) : ℂ :=
  continuousIter [ν₁,ν₂,ν₃] (reversedPolynomial η P) η

theorem polynomialSimplexIntegral_eq (η : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) :
    polynomialSimplexIntegral η P ν₁ ν₂ ν₃ =
      ∫ x in 0..η, ∫ y in 0..(η-x), ∫ z in 0..(η-x-y),
        ((P.eval ((η-x-y-z)/η):ℝ):ℂ)*expKernel ν₃ z*expKernel ν₂ y*expKernel ν₁ x := by
  change (∫ x in 0..η,
    (∫ y in 0..(η-x),
      (∫ z in 0..(η-x-y), ((P.eval ((η-x-y-z)/η):ℝ):ℂ)*expKernel ν₃ z)*
        expKernel ν₂ y)*expKernel ν₁ x) = _
  simp_rw [← intervalIntegral.integral_mul_const]

theorem polynomial_simplex_asymptotic {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (P : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ ν₁ ν₂ ν₃ : ℂ,
      ‖ν₁‖ ≤ R → ‖ν₂‖ ≤ R → ‖ν₃‖ ≤ R → ∀ d : ℕ, 1 ≤ d →
      ‖polynomialTripleSum η L P ν₁ ν₂ ν₃ d -
          (L:ℂ)^3*polynomialSimplexIntegral η P ν₁ ν₂ ν₃‖ ≤ C*(1+Real.log d)*L^2 := by
  obtain ⟨B,D,hf⟩ := reversedPolynomial_regular η P
  let C := iterError η R B D 3+(iterBounds η R B D 3).2
  have hC : 0 ≤ C := add_nonneg (iterError_nonneg hη hR hf.bound_nonneg hf.lip_nonneg 3)
    (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).2
  refine ⟨C+1,by positivity,?_⟩
  intro L hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  apply (triple_simplex_error hf hη hR hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ hd).trans
  change C*(1+Real.log d)*L^2 ≤ (C+1)*(1+Real.log d)*L^2
  have hweight : 0 ≤ 1+Real.log d := add_nonneg zero_le_one (Real.log_nonneg hdR)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hweight) (sq_nonneg L)

end
end Sechstmoment.Source.NoDPHarmonic

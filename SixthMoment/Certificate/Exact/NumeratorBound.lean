import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import SixthMoment.Certificate.Exact.Numerator
import SixthMoment.Numerator.Kernels.Polynomial

namespace SixthMoment
open _root_.SixthMoment.Finite

noncomputable def finiteNumerator : ℚ := (numeratorInteger : ℚ)/(numeratorDenominator : ℚ)

theorem finite_numerator_exact : finiteNumerator = 113594834240035712716790007950896352346564964277539700957066386812058172921265035962343/2460937500000000000000000000000000000000000000000000000000000000000000000000000000 := by
  unfold finiteNumerator
  rw [numerator_integer_exact]
  norm_num [numeratorDenominator, Finite.base]

theorem finite_numerator_gt_lower : (46159 : ℚ) < finiteNumerator := by
  unfold finiteNumerator
  rw [numerator_integer_exact]
  norm_num [numeratorDenominator, Finite.base]

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option Elab.async false

theorem numerator_integer_integral_0 (A B : Nat) :
    (numeratorMonomialInteger 0 A B : ℝ)/(numeratorDenominator : ℝ) =
      ∫ t in (0 : ℝ)..((A : ℝ)/100000000),
        numeratorIntegrand 0 ((A : ℝ)/100000000) ((B : ℝ)/100000000) t := by
  rw [numerator_integral_0]
  norm_num [numeratorMonomialInteger, numeratorTerms, numeratorTerms0, sum,
    numeratorDenominator, Finite.base, numeratorClosed0]
  ring

theorem numerator_integer_integral_1 (A B : Nat) :
    (numeratorMonomialInteger 1 A B : ℝ)/(numeratorDenominator : ℝ) =
      ∫ t in (0 : ℝ)..((A : ℝ)/100000000),
        numeratorIntegrand 1 ((A : ℝ)/100000000) ((B : ℝ)/100000000) t := by
  rw [numerator_integral_1]
  norm_num [numeratorMonomialInteger, numeratorTerms, numeratorTerms1, sum,
    numeratorDenominator, Finite.base, numeratorClosed1]
  ring

theorem numerator_integer_integral_2 (A B : Nat) :
    (numeratorMonomialInteger 2 A B : ℝ)/(numeratorDenominator : ℝ) =
      ∫ t in (0 : ℝ)..((A : ℝ)/100000000),
        numeratorIntegrand 2 ((A : ℝ)/100000000) ((B : ℝ)/100000000) t := by
  rw [numerator_integral_2]
  norm_num [numeratorMonomialInteger, numeratorTerms, numeratorTerms2, sum,
    numeratorDenominator, Finite.base, numeratorClosed2]
  ring

theorem numerator_integer_integral_3 (A B : Nat) :
    (numeratorMonomialInteger 3 A B : ℝ)/(numeratorDenominator : ℝ) =
      ∫ t in (0 : ℝ)..((A : ℝ)/100000000),
        numeratorIntegrand 3 ((A : ℝ)/100000000) ((B : ℝ)/100000000) t := by
  rw [numerator_integral_3]
  norm_num [numeratorMonomialInteger, numeratorTerms, numeratorTerms3, sum,
    numeratorDenominator, Finite.base, numeratorClosed3]
  ring

theorem numerator_integer_integral_4 (A B : Nat) :
    (numeratorMonomialInteger 4 A B : ℝ)/(numeratorDenominator : ℝ) =
      ∫ t in (0 : ℝ)..((A : ℝ)/100000000),
        numeratorIntegrand 4 ((A : ℝ)/100000000) ((B : ℝ)/100000000) t := by
  rw [numerator_integral_4]
  norm_num [numeratorMonomialInteger, numeratorTerms, numeratorTerms4, sum,
    numeratorDenominator, Finite.base, numeratorClosed4]
  ring

end SixthMoment

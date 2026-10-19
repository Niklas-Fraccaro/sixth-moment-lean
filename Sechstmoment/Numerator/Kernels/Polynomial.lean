import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Sechstmoment.Analysis.Integration.PolynomialIntegral
import Sechstmoment.Analysis.Simplex.PolynomialAverage
import Std

namespace Sechstmoment
open scoped BigOperators

noncomputable def numeratorP (u v : ℝ) : ℝ := u*v*(1-u)*(1-v)*(1-u-v)/12
noncomputable def numeratorIntegrand (r : Nat) (a b t : ℝ) : ℝ :=
  numeratorP (b-t) (a-t) *
    simplexMonomialAverage r (-1/2) (a-t-1/2) (1/2-b+t) (1/2)

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def numeratorCoefficients0 (a b : ℝ) : Fin 10 → ℝ :=
  ![(1 : ℝ)/12*a*b + (-1 : ℝ)/6*a*b^2 + (1 : ℝ)/12*a*b^3 + (-1 : ℝ)/6*a^2*b + (1 : ℝ)/4*a^2*b^2 + (-1 : ℝ)/12*a^2*b^3 + (1 : ℝ)/12*a^3*b + (-1 : ℝ)/12*a^3*b^2,
    (-1 : ℝ)/12*b + (1 : ℝ)/6*b^2 + (-1 : ℝ)/12*b^3 + (-1 : ℝ)/12*a + (2 : ℝ)/3*a*b + (-3 : ℝ)/4*a*b^2 + (1 : ℝ)/6*a*b^3 + (1 : ℝ)/6*a^2 + (-3 : ℝ)/4*a^2*b + (1 : ℝ)/2*a^2*b^2 + (-1 : ℝ)/12*a^3 + (1 : ℝ)/6*a^3*b,
    (1 : ℝ)/12 + (-1 : ℝ)/2*b + (1 : ℝ)/2*b^2 + (-1 : ℝ)/12*b^3 + (-1 : ℝ)/2*a + (3 : ℝ)/2*a*b + (-3 : ℝ)/4*a*b^2 + (1 : ℝ)/2*a^2 + (-3 : ℝ)/4*a^2*b + (-1 : ℝ)/12*a^3,
    (1 : ℝ)/3 + (-5 : ℝ)/6*b + (1 : ℝ)/3*b^2 + (-5 : ℝ)/6*a + (1 : ℝ)*a*b + (1 : ℝ)/3*a^2,
    (5 : ℝ)/12 + (-5 : ℝ)/12*b + (-5 : ℝ)/12*a,
    (1 : ℝ)/6,
    0,
    0,
    0,
    0]

noncomputable def numeratorClosed0 (a b : ℝ) : ℝ :=
  (1 : ℝ)/24*a^2*b + (-1 : ℝ)/12*a^2*b^2 + (1 : ℝ)/24*a^2*b^3 + (-1 : ℝ)/72*a^3 + (1 : ℝ)/24*a^3*b^2 + (-1 : ℝ)/36*a^3*b^3

theorem numerator_integrand_0 (a b t : ℝ) :
    numeratorIntegrand 0 a b t = ∑ k : Fin 10, numeratorCoefficients0 a b k * t^k.val := by
  norm_num [numeratorIntegrand, numeratorP, simplexMonomialAverage, homogeneousFour,
    Finite.factorial, numeratorCoefficients0, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

theorem numerator_integral_0 (a b : ℝ) :
    (∫ t in (0 : ℝ)..a, numeratorIntegrand 0 a b t) = numeratorClosed0 a b := by
  simp_rw [numerator_integrand_0]
  rw [integral_finite_polynomial]
  norm_num [numeratorCoefficients0, numeratorClosed0, Fin.sum_univ_succ]
  ring

noncomputable def numeratorCoefficients1 (a b : ℝ) : Fin 10 → ℝ :=
  ![(-1 : ℝ)/48*a*b^2 + (1 : ℝ)/24*a*b^3 + (-1 : ℝ)/48*a*b^4 + (1 : ℝ)/48*a^2*b + (-1 : ℝ)/24*a^2*b^3 + (1 : ℝ)/48*a^2*b^4 + (-1 : ℝ)/24*a^3*b + (1 : ℝ)/24*a^3*b^2 + (1 : ℝ)/48*a^4*b + (-1 : ℝ)/48*a^4*b^2,
    (1 : ℝ)/48*b^2 + (-1 : ℝ)/24*b^3 + (1 : ℝ)/48*b^4 + (-1 : ℝ)/8*a*b^2 + (1 : ℝ)/6*a*b^3 + (-1 : ℝ)/24*a*b^4 + (-1 : ℝ)/48*a^2 + (1 : ℝ)/8*a^2*b + (-1 : ℝ)/12*a^2*b^3 + (1 : ℝ)/24*a^3 + (-1 : ℝ)/6*a^3*b + (1 : ℝ)/12*a^3*b^2 + (-1 : ℝ)/48*a^4 + (1 : ℝ)/24*a^4*b,
    (-1 : ℝ)/48*b + (1 : ℝ)/8*b^2 + (-1 : ℝ)/8*b^3 + (1 : ℝ)/48*b^4 + (1 : ℝ)/48*a + (-1 : ℝ)/4*a*b^2 + (1 : ℝ)/6*a*b^3 + (-1 : ℝ)/8*a^2 + (1 : ℝ)/4*a^2*b + (1 : ℝ)/8*a^3 + (-1 : ℝ)/6*a^3*b + (-1 : ℝ)/48*a^4,
    (-1 : ℝ)/12*b + (5 : ℝ)/24*b^2 + (-1 : ℝ)/12*b^3 + (1 : ℝ)/12*a + (-1 : ℝ)/6*a*b^2 + (-5 : ℝ)/24*a^2 + (1 : ℝ)/6*a^2*b + (1 : ℝ)/12*a^3,
    (-5 : ℝ)/48*b + (5 : ℝ)/48*b^2 + (5 : ℝ)/48*a + (-5 : ℝ)/48*a^2,
    (-1 : ℝ)/24*b + (1 : ℝ)/24*a,
    0,
    0,
    0,
    0]

noncomputable def numeratorClosed1 (a b : ℝ) : ℝ :=
  (-1 : ℝ)/96*a^2*b^2 + (1 : ℝ)/48*a^2*b^3 + (-1 : ℝ)/96*a^2*b^4 + (1 : ℝ)/72*a^3*b + (-1 : ℝ)/48*a^3*b^2 + (1 : ℝ)/144*a^3*b^4 + (-1 : ℝ)/288*a^4 + (1 : ℝ)/96*a^4*b^2 + (-1 : ℝ)/144*a^4*b^3

theorem numerator_integrand_1 (a b t : ℝ) :
    numeratorIntegrand 1 a b t = ∑ k : Fin 10, numeratorCoefficients1 a b k * t^k.val := by
  norm_num [numeratorIntegrand, numeratorP, simplexMonomialAverage, homogeneousFour,
    Finite.factorial, numeratorCoefficients1, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

theorem numerator_integral_1 (a b : ℝ) :
    (∫ t in (0 : ℝ)..a, numeratorIntegrand 1 a b t) = numeratorClosed1 a b := by
  simp_rw [numerator_integrand_1]
  rw [integral_finite_polynomial]
  norm_num [numeratorCoefficients1, numeratorClosed1, Fin.sum_univ_succ]
  ring

noncomputable def numeratorCoefficients2 (a b : ℝ) : Fin 10 → ℝ :=
  ![(1 : ℝ)/240*a*b + (-1 : ℝ)/80*a*b^2 + (1 : ℝ)/48*a*b^3 + (-1 : ℝ)/48*a*b^4 + (1 : ℝ)/120*a*b^5 + (-1 : ℝ)/80*a^2*b + (1 : ℝ)/48*a^2*b^2 + (-1 : ℝ)/48*a^2*b^3 + (1 : ℝ)/48*a^2*b^4 + (-1 : ℝ)/120*a^2*b^5 + (1 : ℝ)/48*a^3*b + (-1 : ℝ)/48*a^3*b^2 + (-1 : ℝ)/48*a^4*b + (1 : ℝ)/48*a^4*b^2 + (1 : ℝ)/120*a^5*b + (-1 : ℝ)/120*a^5*b^2,
    (-1 : ℝ)/240*b + (1 : ℝ)/80*b^2 + (-1 : ℝ)/48*b^3 + (1 : ℝ)/48*b^4 + (-1 : ℝ)/120*b^5 + (-1 : ℝ)/240*a + (1 : ℝ)/20*a*b + (-5 : ℝ)/48*a*b^2 + (1 : ℝ)/8*a*b^3 + (-1 : ℝ)/12*a*b^4 + (1 : ℝ)/60*a*b^5 + (1 : ℝ)/80*a^2 + (-5 : ℝ)/48*a^2*b + (1 : ℝ)/8*a^2*b^2 + (-1 : ℝ)/12*a^2*b^3 + (1 : ℝ)/24*a^2*b^4 + (-1 : ℝ)/48*a^3 + (1 : ℝ)/8*a^3*b + (-1 : ℝ)/12*a^3*b^2 + (1 : ℝ)/48*a^4 + (-1 : ℝ)/12*a^4*b + (1 : ℝ)/24*a^4*b^2 + (-1 : ℝ)/120*a^5 + (1 : ℝ)/60*a^5*b,
    (1 : ℝ)/240 + (-3 : ℝ)/80*b + (1 : ℝ)/12*b^2 + (-5 : ℝ)/48*b^3 + (1 : ℝ)/16*b^4 + (-1 : ℝ)/120*b^5 + (-3 : ℝ)/80*a + (5 : ℝ)/24*a*b + (-5 : ℝ)/16*a*b^2 + (1 : ℝ)/4*a*b^3 + (-1 : ℝ)/12*a*b^4 + (1 : ℝ)/12*a^2 + (-5 : ℝ)/16*a^2*b + (1 : ℝ)/4*a^2*b^2 + (-1 : ℝ)/12*a^2*b^3 + (-5 : ℝ)/48*a^3 + (1 : ℝ)/4*a^3*b + (-1 : ℝ)/12*a^3*b^2 + (1 : ℝ)/16*a^4 + (-1 : ℝ)/12*a^4*b + (-1 : ℝ)/120*a^5,
    (1 : ℝ)/40 + (-1 : ℝ)/8*b + (5 : ℝ)/24*b^2 + (-1 : ℝ)/6*b^3 + (1 : ℝ)/24*b^4 + (-1 : ℝ)/8*a + (5 : ℝ)/12*a*b + (-5 : ℝ)/12*a*b^2 + (1 : ℝ)/6*a*b^3 + (5 : ℝ)/24*a^2 + (-5 : ℝ)/12*a^2*b + (1 : ℝ)/6*a^2*b^2 + (-1 : ℝ)/6*a^3 + (1 : ℝ)/6*a^3*b + (1 : ℝ)/24*a^4,
    (1 : ℝ)/16 + (-5 : ℝ)/24*b + (11 : ℝ)/48*b^2 + (-1 : ℝ)/12*b^3 + (-5 : ℝ)/24*a + (5 : ℝ)/12*a*b + (-5 : ℝ)/24*a*b^2 + (11 : ℝ)/48*a^2 + (-5 : ℝ)/24*a^2*b + (-1 : ℝ)/12*a^3,
    (1 : ℝ)/12 + (-7 : ℝ)/40*b + (11 : ℝ)/120*b^2 + (-7 : ℝ)/40*a + (1 : ℝ)/6*a*b + (11 : ℝ)/120*a^2,
    (7 : ℝ)/120 + (-7 : ℝ)/120*b + (-7 : ℝ)/120*a,
    (1 : ℝ)/60,
    0,
    0]

noncomputable def numeratorClosed2 (a b : ℝ) : ℝ :=
  (1 : ℝ)/480*a^2*b + (-1 : ℝ)/160*a^2*b^2 + (1 : ℝ)/96*a^2*b^3 + (-1 : ℝ)/96*a^2*b^4 + (1 : ℝ)/240*a^2*b^5 + (-1 : ℝ)/1440*a^3 + (-1 : ℝ)/288*a^3*b^2 + (1 : ℝ)/144*a^3*b^3 + (-1 : ℝ)/360*a^3*b^5 + (1 : ℝ)/144*a^4*b + (-1 : ℝ)/96*a^4*b^2 + (1 : ℝ)/288*a^4*b^4 + (-1 : ℝ)/720*a^5 + (1 : ℝ)/240*a^5*b^2 + (-1 : ℝ)/360*a^5*b^3

theorem numerator_integrand_2 (a b t : ℝ) :
    numeratorIntegrand 2 a b t = ∑ k : Fin 10, numeratorCoefficients2 a b k * t^k.val := by
  norm_num [numeratorIntegrand, numeratorP, simplexMonomialAverage, homogeneousFour,
    Finite.factorial, numeratorCoefficients2, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

theorem numerator_integral_2 (a b : ℝ) :
    (∫ t in (0 : ℝ)..a, numeratorIntegrand 2 a b t) = numeratorClosed2 a b := by
  simp_rw [numerator_integrand_2]
  rw [integral_finite_polynomial]
  norm_num [numeratorCoefficients2, numeratorClosed2, Fin.sum_univ_succ]
  ring

noncomputable def numeratorCoefficients3 (a b : ℝ) : Fin 10 → ℝ :=
  ![(-1 : ℝ)/320*a*b^2 + (1 : ℝ)/96*a*b^3 + (-1 : ℝ)/64*a*b^4 + (1 : ℝ)/80*a*b^5 + (-1 : ℝ)/240*a*b^6 + (1 : ℝ)/320*a^2*b + (-1 : ℝ)/96*a^2*b^3 + (1 : ℝ)/64*a^2*b^4 + (-1 : ℝ)/80*a^2*b^5 + (1 : ℝ)/240*a^2*b^6 + (-1 : ℝ)/96*a^3*b + (1 : ℝ)/96*a^3*b^2 + (1 : ℝ)/64*a^4*b + (-1 : ℝ)/64*a^4*b^2 + (-1 : ℝ)/80*a^5*b + (1 : ℝ)/80*a^5*b^2 + (1 : ℝ)/240*a^6*b + (-1 : ℝ)/240*a^6*b^2,
    (1 : ℝ)/320*b^2 + (-1 : ℝ)/96*b^3 + (1 : ℝ)/64*b^4 + (-1 : ℝ)/80*b^5 + (1 : ℝ)/240*b^6 + (-1 : ℝ)/32*a*b^2 + (1 : ℝ)/12*a*b^3 + (-3 : ℝ)/32*a*b^4 + (1 : ℝ)/20*a*b^5 + (-1 : ℝ)/120*a*b^6 + (-1 : ℝ)/320*a^2 + (1 : ℝ)/32*a^2*b + (-1 : ℝ)/16*a^2*b^3 + (1 : ℝ)/16*a^2*b^4 + (-1 : ℝ)/40*a^2*b^5 + (1 : ℝ)/96*a^3 + (-1 : ℝ)/12*a^3*b + (1 : ℝ)/16*a^3*b^2 + (-1 : ℝ)/64*a^4 + (3 : ℝ)/32*a^4*b + (-1 : ℝ)/16*a^4*b^2 + (1 : ℝ)/80*a^5 + (-1 : ℝ)/20*a^5*b + (1 : ℝ)/40*a^5*b^2 + (-1 : ℝ)/240*a^6 + (1 : ℝ)/120*a^6*b,
    (-1 : ℝ)/320*b + (1 : ℝ)/32*b^2 + (-7 : ℝ)/96*b^3 + (5 : ℝ)/64*b^4 + (-3 : ℝ)/80*b^5 + (1 : ℝ)/240*b^6 + (1 : ℝ)/320*a + (-1 : ℝ)/8*a*b^2 + (1 : ℝ)/4*a*b^3 + (-3 : ℝ)/16*a*b^4 + (1 : ℝ)/20*a*b^5 + (-1 : ℝ)/32*a^2 + (1 : ℝ)/8*a^2*b + (-1 : ℝ)/8*a^2*b^3 + (1 : ℝ)/16*a^2*b^4 + (7 : ℝ)/96*a^3 + (-1 : ℝ)/4*a^3*b + (1 : ℝ)/8*a^3*b^2 + (-5 : ℝ)/64*a^4 + (3 : ℝ)/16*a^4*b + (-1 : ℝ)/16*a^4*b^2 + (3 : ℝ)/80*a^5 + (-1 : ℝ)/20*a^5*b + (-1 : ℝ)/240*a^6,
    (-1 : ℝ)/48*b + (11 : ℝ)/96*b^2 + (-3 : ℝ)/16*b^3 + (1 : ℝ)/8*b^4 + (-1 : ℝ)/40*b^5 + (1 : ℝ)/48*a + (-1 : ℝ)/4*a*b^2 + (1 : ℝ)/3*a*b^3 + (-1 : ℝ)/8*a*b^4 + (-11 : ℝ)/96*a^2 + (1 : ℝ)/4*a^2*b + (-1 : ℝ)/12*a^2*b^3 + (3 : ℝ)/16*a^3 + (-1 : ℝ)/3*a^3*b + (1 : ℝ)/12*a^3*b^2 + (-1 : ℝ)/8*a^4 + (1 : ℝ)/8*a^4*b + (1 : ℝ)/40*a^5,
    (-11 : ℝ)/192*b + (13 : ℝ)/64*b^2 + (-5 : ℝ)/24*b^3 + (1 : ℝ)/16*b^4 + (11 : ℝ)/192*a + (-1 : ℝ)/4*a*b^2 + (1 : ℝ)/6*a*b^3 + (-13 : ℝ)/64*a^2 + (1 : ℝ)/4*a^2*b + (5 : ℝ)/24*a^3 + (-1 : ℝ)/6*a^3*b + (-1 : ℝ)/16*a^4,
    (-13 : ℝ)/160*b + (7 : ℝ)/40*b^2 + (-1 : ℝ)/12*b^3 + (13 : ℝ)/160*a + (-1 : ℝ)/10*a*b^2 + (-7 : ℝ)/40*a^2 + (1 : ℝ)/10*a^2*b + (1 : ℝ)/12*a^3,
    (-7 : ℝ)/120*b + (7 : ℝ)/120*b^2 + (7 : ℝ)/120*a + (-7 : ℝ)/120*a^2,
    (-1 : ℝ)/60*b + (1 : ℝ)/60*a,
    0,
    0]

noncomputable def numeratorClosed3 (a b : ℝ) : ℝ :=
  (-1 : ℝ)/640*a^2*b^2 + (1 : ℝ)/192*a^2*b^3 + (-1 : ℝ)/128*a^2*b^4 + (1 : ℝ)/160*a^2*b^5 + (-1 : ℝ)/480*a^2*b^6 + (1 : ℝ)/480*a^3*b + (-1 : ℝ)/192*a^3*b^2 + (1 : ℝ)/144*a^3*b^3 + (-1 : ℝ)/192*a^3*b^4 + (1 : ℝ)/720*a^3*b^6 + (-1 : ℝ)/1920*a^4 + (-1 : ℝ)/384*a^4*b^2 + (1 : ℝ)/192*a^4*b^3 + (-1 : ℝ)/480*a^4*b^5 + (1 : ℝ)/240*a^5*b + (-1 : ℝ)/160*a^5*b^2 + (1 : ℝ)/480*a^5*b^4 + (-1 : ℝ)/1440*a^6 + (1 : ℝ)/480*a^6*b^2 + (-1 : ℝ)/720*a^6*b^3

theorem numerator_integrand_3 (a b t : ℝ) :
    numeratorIntegrand 3 a b t = ∑ k : Fin 10, numeratorCoefficients3 a b k * t^k.val := by
  norm_num [numeratorIntegrand, numeratorP, simplexMonomialAverage, homogeneousFour,
    Finite.factorial, numeratorCoefficients3, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

theorem numerator_integral_3 (a b : ℝ) :
    (∫ t in (0 : ℝ)..a, numeratorIntegrand 3 a b t) = numeratorClosed3 a b := by
  simp_rw [numerator_integrand_3]
  rw [integral_finite_polynomial]
  norm_num [numeratorCoefficients3, numeratorClosed3, Fin.sum_univ_succ]
  ring

noncomputable def numeratorCoefficients4 (a b : ℝ) : Fin 10 → ℝ :=
  ![(1 : ℝ)/2240*a*b + (-1 : ℝ)/560*a*b^2 + (1 : ℝ)/192*a*b^3 + (-1 : ℝ)/96*a*b^4 + (1 : ℝ)/80*a*b^5 + (-1 : ℝ)/120*a*b^6 + (1 : ℝ)/420*a*b^7 + (-1 : ℝ)/560*a^2*b + (1 : ℝ)/320*a^2*b^2 + (-1 : ℝ)/192*a^2*b^3 + (1 : ℝ)/96*a^2*b^4 + (-1 : ℝ)/80*a^2*b^5 + (1 : ℝ)/120*a^2*b^6 + (-1 : ℝ)/420*a^2*b^7 + (1 : ℝ)/192*a^3*b + (-1 : ℝ)/192*a^3*b^2 + (-1 : ℝ)/96*a^4*b + (1 : ℝ)/96*a^4*b^2 + (1 : ℝ)/80*a^5*b + (-1 : ℝ)/80*a^5*b^2 + (-1 : ℝ)/120*a^6*b + (1 : ℝ)/120*a^6*b^2 + (1 : ℝ)/420*a^7*b + (-1 : ℝ)/420*a^7*b^2,
    (-1 : ℝ)/2240*b + (1 : ℝ)/560*b^2 + (-1 : ℝ)/192*b^3 + (1 : ℝ)/96*b^4 + (-1 : ℝ)/80*b^5 + (1 : ℝ)/120*b^6 + (-1 : ℝ)/420*b^7 + (-1 : ℝ)/2240*a + (1 : ℝ)/140*a*b + (-7 : ℝ)/320*a*b^2 + (5 : ℝ)/96*a*b^3 + (-1 : ℝ)/12*a*b^4 + (3 : ℝ)/40*a*b^5 + (-1 : ℝ)/30*a*b^6 + (1 : ℝ)/210*a*b^7 + (1 : ℝ)/560*a^2 + (-7 : ℝ)/320*a^2*b + (1 : ℝ)/32*a^2*b^2 + (-1 : ℝ)/24*a^2*b^3 + (1 : ℝ)/16*a^2*b^4 + (-1 : ℝ)/20*a^2*b^5 + (1 : ℝ)/60*a^2*b^6 + (-1 : ℝ)/192*a^3 + (5 : ℝ)/96*a^3*b + (-1 : ℝ)/24*a^3*b^2 + (1 : ℝ)/96*a^4 + (-1 : ℝ)/12*a^4*b + (1 : ℝ)/16*a^4*b^2 + (-1 : ℝ)/80*a^5 + (3 : ℝ)/40*a^5*b + (-1 : ℝ)/20*a^5*b^2 + (1 : ℝ)/120*a^6 + (-1 : ℝ)/30*a^6*b + (1 : ℝ)/60*a^6*b^2 + (-1 : ℝ)/420*a^7 + (1 : ℝ)/210*a^7*b,
    (1 : ℝ)/2240 + (-3 : ℝ)/560*b + (3 : ℝ)/160*b^2 + (-3 : ℝ)/64*b^3 + (7 : ℝ)/96*b^4 + (-1 : ℝ)/16*b^5 + (1 : ℝ)/40*b^6 + (-1 : ℝ)/420*b^7 + (-3 : ℝ)/560*a + (7 : ℝ)/160*a*b + (-7 : ℝ)/64*a*b^2 + (5 : ℝ)/24*a*b^3 + (-1 : ℝ)/4*a*b^4 + (3 : ℝ)/20*a*b^5 + (-1 : ℝ)/30*a*b^6 + (3 : ℝ)/160*a^2 + (-7 : ℝ)/64*a^2*b + (1 : ℝ)/8*a^2*b^2 + (-1 : ℝ)/8*a^2*b^3 + (1 : ℝ)/8*a^2*b^4 + (-1 : ℝ)/20*a^2*b^5 + (-3 : ℝ)/64*a^3 + (5 : ℝ)/24*a^3*b + (-1 : ℝ)/8*a^3*b^2 + (7 : ℝ)/96*a^4 + (-1 : ℝ)/4*a^4*b + (1 : ℝ)/8*a^4*b^2 + (-1 : ℝ)/16*a^5 + (3 : ℝ)/20*a^5*b + (-1 : ℝ)/20*a^5*b^2 + (1 : ℝ)/40*a^6 + (-1 : ℝ)/30*a^6*b + (-1 : ℝ)/420*a^7,
    (1 : ℝ)/280 + (-13 : ℝ)/480*b + (1 : ℝ)/12*b^2 + (-1 : ℝ)/6*b^3 + (3 : ℝ)/16*b^4 + (-1 : ℝ)/10*b^5 + (1 : ℝ)/60*b^6 + (-13 : ℝ)/480*a + (7 : ℝ)/48*a*b + (-7 : ℝ)/24*a*b^2 + (5 : ℝ)/12*a*b^3 + (-1 : ℝ)/3*a*b^4 + (1 : ℝ)/10*a*b^5 + (1 : ℝ)/12*a^2 + (-7 : ℝ)/24*a^2*b + (1 : ℝ)/4*a^2*b^2 + (-1 : ℝ)/6*a^2*b^3 + (1 : ℝ)/12*a^2*b^4 + (-1 : ℝ)/6*a^3 + (5 : ℝ)/12*a^3*b + (-1 : ℝ)/6*a^3*b^2 + (3 : ℝ)/16*a^4 + (-1 : ℝ)/3*a^4*b + (1 : ℝ)/12*a^4*b^2 + (-1 : ℝ)/10*a^5 + (1 : ℝ)/10*a^5*b + (1 : ℝ)/60*a^6,
    (13 : ℝ)/960 + (-5 : ℝ)/64*b + (19 : ℝ)/96*b^2 + (-7 : ℝ)/24*b^3 + (5 : ℝ)/24*b^4 + (-1 : ℝ)/20*b^5 + (-5 : ℝ)/64*a + (7 : ℝ)/24*a*b + (-7 : ℝ)/16*a*b^2 + (5 : ℝ)/12*a*b^3 + (-1 : ℝ)/6*a*b^4 + (19 : ℝ)/96*a^2 + (-7 : ℝ)/16*a^2*b + (1 : ℝ)/4*a^2*b^2 + (-1 : ℝ)/12*a^2*b^3 + (-7 : ℝ)/24*a^3 + (5 : ℝ)/12*a^3*b + (-1 : ℝ)/12*a^3*b^2 + (5 : ℝ)/24*a^4 + (-1 : ℝ)/6*a^4*b + (-1 : ℝ)/20*a^5,
    (1 : ℝ)/32 + (-11 : ℝ)/80*b + (21 : ℝ)/80*b^2 + (-1 : ℝ)/4*b^3 + (1 : ℝ)/12*b^4 + (-11 : ℝ)/80*a + (7 : ℝ)/20*a*b + (-7 : ℝ)/20*a*b^2 + (1 : ℝ)/6*a*b^3 + (21 : ℝ)/80*a^2 + (-7 : ℝ)/20*a^2*b + (1 : ℝ)/10*a^2*b^2 + (-1 : ℝ)/4*a^3 + (1 : ℝ)/6*a^3*b + (1 : ℝ)/12*a^4,
    (11 : ℝ)/240 + (-7 : ℝ)/48*b + (11 : ℝ)/60*b^2 + (-1 : ℝ)/12*b^3 + (-7 : ℝ)/48*a + (7 : ℝ)/30*a*b + (-7 : ℝ)/60*a*b^2 + (11 : ℝ)/60*a^2 + (-7 : ℝ)/60*a^2*b + (-1 : ℝ)/12*a^3,
    (1 : ℝ)/24 + (-3 : ℝ)/35*b + (11 : ℝ)/210*b^2 + (-3 : ℝ)/35*a + (1 : ℝ)/15*a*b + (11 : ℝ)/210*a^2,
    (3 : ℝ)/140 + (-3 : ℝ)/140*b + (-3 : ℝ)/140*a,
    (1 : ℝ)/210]

noncomputable def numeratorClosed4 (a b : ℝ) : ℝ :=
  (1 : ℝ)/4480*a^2*b + (-1 : ℝ)/1120*a^2*b^2 + (1 : ℝ)/384*a^2*b^3 + (-1 : ℝ)/192*a^2*b^4 + (1 : ℝ)/160*a^2*b^5 + (-1 : ℝ)/240*a^2*b^6 + (1 : ℝ)/840*a^2*b^7 + (-1 : ℝ)/13440*a^3 + (-1 : ℝ)/640*a^3*b^2 + (1 : ℝ)/192*a^3*b^3 + (-1 : ℝ)/144*a^3*b^4 + (1 : ℝ)/240*a^3*b^5 + (-1 : ℝ)/1260*a^3*b^7 + (1 : ℝ)/480*a^4*b + (-1 : ℝ)/192*a^4*b^2 + (1 : ℝ)/144*a^4*b^3 + (-1 : ℝ)/192*a^4*b^4 + (1 : ℝ)/720*a^4*b^6 + (-1 : ℝ)/2400*a^5 + (-1 : ℝ)/480*a^5*b^2 + (1 : ℝ)/240*a^5*b^3 + (-1 : ℝ)/600*a^5*b^5 + (1 : ℝ)/360*a^6*b + (-1 : ℝ)/240*a^6*b^2 + (1 : ℝ)/720*a^6*b^4 + (-1 : ℝ)/2520*a^7 + (1 : ℝ)/840*a^7*b^2 + (-1 : ℝ)/1260*a^7*b^3

theorem numerator_integrand_4 (a b t : ℝ) :
    numeratorIntegrand 4 a b t = ∑ k : Fin 10, numeratorCoefficients4 a b k * t^k.val := by
  norm_num [numeratorIntegrand, numeratorP, simplexMonomialAverage, homogeneousFour,
    Finite.factorial, numeratorCoefficients4, Fin.sum_univ_succ, Finset.sum_range_succ]
  ring

theorem numerator_integral_4 (a b : ℝ) :
    (∫ t in (0 : ℝ)..a, numeratorIntegrand 4 a b t) = numeratorClosed4 a b := by
  simp_rw [numerator_integrand_4]
  rw [integral_finite_polynomial]
  norm_num [numeratorCoefficients4, numeratorClosed4, Fin.sum_univ_succ]
  ring

end Sechstmoment

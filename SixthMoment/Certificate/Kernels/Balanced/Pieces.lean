import SixthMoment.Certificate.Kernels.Balanced.DensityPolynomial
import SixthMoment.Certificate.Kernels.Balanced.PolytopeDensityBridge

namespace SixthMoment
open scoped BigOperators

theorem denominatorRealInner_polynomialOn (p q : Fin 5 → ℝ) (delta A B l u : ℝ) :
    PolynomialOn 9 (fun t => denominatorRealInner p q delta (A+B*t)) l u := by
  have h := polynomialOn_affine A B l u
  have h0 := ((h.pow 1).const_mul (2*innerCoefficient p q delta 0)).mono (by omega : 1*1 ≤ 9)
  have h2 := ((h.pow 3).const_mul (2*innerCoefficient p q delta 2/3)).mono (by omega : 3*1 ≤ 9)
  have h4 := ((h.pow 5).const_mul (2*innerCoefficient p q delta 4/5)).mono (by omega : 5*1 ≤ 9)
  have h6 := ((h.pow 7).const_mul (2*innerCoefficient p q delta 6/7)).mono (by omega : 7*1 ≤ 9)
  have h8 := (h.pow 9).const_mul (2*innerCoefficient p q delta 8/9)
  apply (((h0.add h2).add h4).add h6).add h8 |>.congr
  intro t _
  dsimp only [denominatorRealInner]
  rw [denominator_inner_integral]
  ring

noncomputable def denominatorZeroIntegrand (p q : Fin 5 → ℝ) (a b c d t : ℝ) : ℝ :=
  realW6 t a b c d/6*
    denominatorRealInner p q ((a+b-c-d)/2) ((1-a-b-c-d+2*t)/2)

theorem denominatorZeroIntegrand_polynomialOn (p q : Fin 5 → ℝ) {a b c d l u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hl : 0 ≤ l) (hu : u ≤ min (a+b) (c+d))
    (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 12 (fun t => denominatorZeroIntegrand p q a b c d t) l u := by
  have hi : PolynomialOn 9 (fun t => denominatorRealInner p q ((a+b-c-d)/2)
      ((1-a-b-c-d+2*t)/2)) l u := by
    apply (denominatorRealInner_polynomialOn p q ((a+b-c-d)/2)
      ((1-a-b-c-d)/2) 1 l u).congr
    intro t _
    congr 1
    ring
  have hw := realW6_polynomialOn ha hb hc hd hl hu hk
  apply ((hw.mul hi).const_mul (1/6)).congr
  intro t _
  dsimp only [denominatorZeroIntegrand]
  ring

theorem denominatorZero_subinterval_quadrature (p q : Fin 5 → ℝ) {a b c d l u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hl : 0 ≤ l) (hu : u ≤ min (a+b) (c+d)) (hlu : l ≤ u)
    (hk : AvoidsDenominatorKnots a b c d l u) :
    (∫ t in l..u, denominatorZeroIntegrand p q a b c d t) =
      (u-l)*(∑ j : Fin 13, ncWeight j*
        denominatorZeroIntegrand p q a b c d (l+(u-l)*(j.val/12))) :=
  polynomialOn_nc_interval_exact hlu
    (denominatorZeroIntegrand_polynomialOn p q ha hb hc hd hl hu hk)

theorem denominatorZeroIntegrand_continuousOn (p q : Fin 5 → ℝ) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ContinuousOn (fun t => denominatorZeroIntegrand p q a b c d t)
      (Set.Icc 0 (min (a+b) (c+d))) := by
  have hw : Continuous (fun t => realW6Formula t a b c d) := by
    dsimp only [realW6Formula]
    fun_prop
  have hi := denominatorRealInner_continuous p q ((a+b-c-d)/2)
    (fun t => (1-a-b-c-d+2*t)/2) (by fun_prop)
  apply ((hw.div_const 6).mul hi).continuousOn.congr
  intro t ht
  dsimp only [denominatorZeroIntegrand]
  rw [realW6_eq_formula ha hb hc hd ht.1 ht.2]
  rfl

theorem denominatorZeroIntegrand_intervalIntegrable (p q : Fin 5 → ℝ) {a b c d l u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hl : l ∈ Set.Icc 0 (min (a+b) (c+d)))
    (hu : u ∈ Set.Icc 0 (min (a+b) (c+d))) :
    IntervalIntegrable (fun t => denominatorZeroIntegrand p q a b c d t)
      MeasureTheory.volume l u := by
  apply ContinuousOn.intervalIntegrable
  apply (denominatorZeroIntegrand_continuousOn p q ha hb hc hd).mono
  intro t ht
  change min l u ≤ t ∧ t ≤ max l u at ht
  exact ⟨(le_min hl.1 hu.1).trans ht.1, ht.2.trans (max_le hl.2 hu.2)⟩

end SixthMoment

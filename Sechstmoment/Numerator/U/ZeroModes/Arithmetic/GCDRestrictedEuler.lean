import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDPrimitiveBijection


namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03GCDZetaQuotient (w z s : ℂ) : ℂ :=
  riemannZeta (1+w+z+s)*riemannZeta (1+w)*riemannZeta (1+z)/riemannZeta (2+w+z)

def a03GCDPrimeCorrectionProduct (q : ℕ) (w z s : ℂ) : ℂ :=
  ∏ p∈q.primeFactors, bblrEtaCorrection p (w+z+s) z (w+z)

theorem a03GCDPrimeCorrectionProduct_eq (q : ℕ) (w z s : ℂ) :
    a03GCDPrimeCorrectionProduct q w z s=
      (∏ p∈q.primeFactors, (1-(p:ℂ)^(-(1+w+z+s))))*
      (∏ p∈q.primeFactors, (1-(p:ℂ)^(-(1+z))))/
      (∏ p∈q.primeFactors, (1-(p:ℂ)^(-(2+w+z)))) := by
  unfold a03GCDPrimeCorrectionProduct bblrEtaCorrection
  rw [←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  congr 2 <;> congr 1 <;> ring

theorem a03RestrictedGCDSeries_eq_zeta_mul_corrections {A B : ℕ}
    (hA : A≠0) (hB : B≠0) (hAB : A.Coprime B)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (ht : 1<(1+w+z+s).re) :
    a03RestrictedGCDSeries A B w z s=
      a03GCDZetaQuotient w z s*a03GCDPrimeCorrectionProduct A w z s*
        a03GCDPrimeCorrectionProduct B z w s := by
  have hW : 1<(1+w).re := by simp only [add_re,one_re]; linarith
  have hZ : 1<(1+z).re := by simp only [add_re,one_re]; linarith
  have h2 : 1<(2+w+z).re := by simp only [add_re]; norm_num; linarith
  have hdenZ := riemannZeta_ne_zero_of_one_lt_re h2
  have hdenA : (∏ p∈A.primeFactors, (1-(p:ℂ)^(-(2+w+z))))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp =>
      Complex.one_sub_prime_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) h2)
  have hdenB : (∏ p∈B.primeFactors, (1-(p:ℂ)^(-(2+w+z))))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp =>
      Complex.one_sub_prime_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp) h2)
  rw [a03RestrictedGCDSeries_eq_coprimeZeta_quotient hA hB hw hz ht,
    a03CoprimeZeta_eq_zeta_mul_primeProduct (mul_ne_zero hA hB) ht,
    a03CoprimeZeta_eq_zeta_mul_primeProduct hB hW,
    a03CoprimeZeta_eq_zeta_mul_primeProduct hA hZ,
    a03CoprimeZeta_eq_zeta_mul_primeProduct (mul_ne_zero hA hB) h2,
    Nat.primeFactors_mul hA hB,Finset.prod_union hAB.disjoint_primeFactors,
    Finset.prod_union hAB.disjoint_primeFactors,
    a03GCDPrimeCorrectionProduct_eq,a03GCDPrimeCorrectionProduct_eq]
  unfold a03GCDZetaQuotient
  have hs' : 1+z+w+s=1+w+z+s := by ring
  have h2' : 2+z+w=2+w+z := by ring
  rw [hs',h2']
  field_simp [hdenZ,hdenA,hdenB]

end
end Sechstmoment

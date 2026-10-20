import Sechstmoment.Arithmetic.Euler.Local.Prime.PrincipalEulerPositivity


namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem finite_local_factorization {ι : Type*} (s : Finset ι)
    (a b c d t : ι → ℂ) (r : ι → ℝ) (h : ι → ℕ)
    (hr : ∀ i∈s, 0≤r i) (ha : ∀ i∈s, ‖a i‖≤r i) (hb : ∀ i∈s, ‖b i‖≤r i)
    (hc : ∀ i∈s, ‖c i‖≤r i) (hd : ∀ i∈s, ‖d i‖≤r i) (ht : ∀ i∈s, r i*‖t i‖<1) :
    (∏ i∈s,numerator (a i) (b i) (c i) (d i) (h i) (t i))=
      (∏ i∈s,denom (a i) (b i) (c i) (d i) (t i))*(∏ i∈s,localSeries (a i) (b i) (c i) (d i) (t i) (h i)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (local_series_factorization _ _ _ _ _ _ (hr i hi) (ha i hi) (hb i hi) (hc i hi) (hd i hi) (ht i hi) _).symm

end Sechstmoment.Source.NoDPLocal

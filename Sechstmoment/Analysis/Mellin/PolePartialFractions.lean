import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange

/-! Exact partial fractions at the separated Mellin poles. -/

namespace Sechstmoment.Source
open Complex Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem separated_pole_partial_fractions {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (p : ι → ℂ) (hp : Function.Injective p) (z : ℂ) (hz : ∀ i, z ≠ p i) :
    (∏ i : ι, (z-p i))⁻¹ =
      ∑ i : ι, (((Finset.univ : Finset ι).erase i).prod (fun j : ι => p i-p j))⁻¹/(z-p i) := by
  classical
  have H := congrArg (Polynomial.eval z)
    (Lagrange.sum_basis (s := Finset.univ) hp.injOn Finset.univ_nonempty)
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_one,Lagrange.basis,
    Polynomial.eval_prod,Lagrange.basisDivisor,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X] at H
  calc
    _ = (∑ i : ι, ((Finset.univ : Finset ι).erase i).prod
        (fun j : ι => (p i-p j)⁻¹*(z-p j)))/(∏ i : ι, (z-p i)) := by
      rw [H,one_div]
    _ = ∑ i : ι, (((Finset.univ : Finset ι).erase i).prod
        (fun j : ι => (p i-p j)⁻¹*(z-p j)))/(∏ i : ι, (z-p i)) := by
      simp only [div_eq_mul_inv,Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hB : ((Finset.univ : Finset ι).erase i).prod (fun j : ι => z-p j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hz j))
      have hD : (∏ j : ι, (z-p j)) =
          (z-p i)*((Finset.univ : Finset ι).erase i).prod (fun j : ι => z-p j) :=
        (Finset.mul_prod_erase Finset.univ (fun j => z-p j) (Finset.mem_univ i)).symm
      rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,hD,mul_div_mul_right _ _ hB]

end
end Sechstmoment.Source

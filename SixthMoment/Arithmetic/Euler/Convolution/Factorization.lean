import SixthMoment.Arithmetic.Euler.Convolution.OriginalEulerProduct

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

theorem swap_complement_product {R : Type*} [CommMonoid R] (i : Fin 4) (f : Fin 4 → R) :
    f (Equiv.swap 0 i 1) * (f (Equiv.swap 0 i 2) * f (Equiv.swap 0 i 3)) =
      ∏ j ∈ Finset.univ.erase i, f j := by
  have H0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have H1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have H2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have H3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  fin_cases i <;> simp [H0,H1,H2,H3,Equiv.swap_apply_def,mul_assoc,mul_comm,mul_left_comm]

def tripleCoeffAt (i : Fin 4) (s : Fin 4 → ℂ) (n : ℕ) : ℂ := tripleCoeff (reindexShifts i s) n
def originalFactorAt (i : Fin 4) (s : Fin 4 → ℂ) (n : ℕ) : ℂ := originalFactor (reindexShifts i s) n
def originalCoeffAt (i : Fin 4) (s : Fin 4 → ℂ) (a b : ℕ) : ℂ := originalCoeff (reindexShifts i s) a b
def originalTermAt (i : Fin 4) (s : Fin 4 → ℂ) (u v : ℂ) : ℕ × ℕ → ℂ :=
  originalTerm (reindexShifts i s) u v
def originalDirichletAt (i : Fin 4) (s : Fin 4 → ℂ) (u v : ℂ) : ℂ :=
  originalDirichlet (reindexShifts i s) u v
def sixZetaAt (i : Fin 4) (s : Fin 4 → ℂ) (u v : ℂ) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, riemannZeta (1+u+s j) * riemannZeta (1+v+s j)

theorem tripleAF_reindex_product (i : Fin 4) (s : Fin 4 → ℂ) :
    tripleAF (reindexShifts i s) = ∏ j ∈ Finset.univ.erase i, powerAF (1+s j) := by
  exact swap_complement_product i (fun j => powerAF (1+s j))

theorem sixZetaAt_eq_triples (i : Fin 4) (s : Fin 4 → ℂ) (u v : ℂ) :
    sixZetaAt i s u v = tripleZeta (reindexShifts i s) u * tripleZeta (reindexShifts i s) v := by
  unfold sixZetaAt
  rw [Finset.prod_mul_distrib, ← swap_complement_product i (fun j => riemannZeta (1+u+s j)),
    ← swap_complement_product i (fun j => riemannZeta (1+v+s j))]
  rfl

theorem originalCoeffAt_factor (i : Fin 4) (s : Fin 4 → ℂ) (a b : ℕ) :
    originalCoeffAt i s a b = ((a*b:ℕ):ℂ)^(-s i) * originalFactorAt i s (a*b) := by
  exact originalCoeff_factor (reindexShifts i s) a b

theorem originalCoeffAt_convolution (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (a b : ℕ) :
    originalCoeffAt i s a b = ∑ d ∈ a.divisors, ∑ e ∈ b.divisors,
      gammaAt i s (d,e) * tripleCoeffAt i s (a/d) * tripleCoeffAt i s (b/e) :=
  originalCoeff_convolution _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j)) a b

theorem originalFactorAt_convolution (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (a b : ℕ) :
    ((a*b:ℕ):ℂ)^(-s i) * originalFactorAt i s (a*b) =
      ∑ d ∈ a.divisors, ∑ e ∈ b.divisors,
        gammaAt i s (d,e) * tripleCoeffAt i s (a/d) * tripleCoeffAt i s (b/e) := by
  rw [← originalCoeffAt_factor]
  exact originalCoeffAt_convolution i s ρ hρ0 hρ hs a b

theorem originalTermAt_hasSum (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    HasSum (originalTermAt i s u v) (restDirichletAt i s u v * sixZetaAt i s u v) := by
  rw [sixZetaAt_eq_triples]
  exact originalTerm_hasSum _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j)) u v hu hv

theorem originalTermAt_absolute (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) : Summable (fun q => ‖originalTermAt i s u v q‖) :=
  (originalTermAt_hasSum i s ρ hρ0 hρ hs u v hu hv).summable.norm

theorem originalFactorAt_hasSum (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    HasSum (fun q : ℕ × ℕ => ((q.1*q.2:ℕ):ℂ)^(-s i) * originalFactorAt i s (q.1*q.2) *
      (q.1:ℂ)^(-u) * (q.2:ℂ)^(-v))
      (restDirichletAt i s u v *
        ∏ j ∈ Finset.univ.erase i, riemannZeta (1+u+s j) * riemannZeta (1+v+s j)) := by
  have H := originalTermAt_hasSum i s ρ hρ0 hρ hs u v hu hv
  convert H using 1
  · funext q
    exact congrArg (fun z : ℂ => z * (q.1:ℂ)^(-u) * (q.2:ℂ)^(-v))
      (originalCoeffAt_factor i s q.1 q.2).symm
  · rfl

theorem originalDirichletAt_six_zeta (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    originalDirichletAt i s u v = restDirichletAt i s u v *
      ∏ j ∈ Finset.univ.erase i, riemannZeta (1+u+s j) * riemannZeta (1+v+s j) :=
  (originalTermAt_hasSum i s ρ hρ0 hρ hs u v hu hv).tsum_eq

theorem originalDirichletAt_euler_hasProd (i : Fin 4) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    HasProd (fun p : Nat.Primes => doubleSeries (primeOriginalWeight p.val (reindexShifts i s))
      ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v))) (originalDirichletAt i s u v) :=
  originalDirichlet_euler_hasProd _ ρ hρ0 hρ (fun j => hs (Equiv.swap 0 i j)) u v hu hv

theorem sixZetaAt_zero (i : Fin 4) (u v : ℂ) :
    sixZetaAt i (fun _ => 0) u v = riemannZeta (1+u)^3 * riemannZeta (1+v)^3 := by
  rw [sixZetaAt_eq_triples]
  simp only [tripleZeta,reindexShifts,Function.comp_apply,add_zero]
  ring

theorem originalDirichletAt_zero_shifts (i : Fin 4) (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    originalDirichletAt i (fun _ => 0) u v = restDirichletAt i (fun _ => 0) u v *
      (riemannZeta (1+u)^3 * riemannZeta (1+v)^3) := by
  rw [← sixZetaAt_zero i u v]
  exact originalDirichletAt_six_zeta i (fun _ => 0) 0 (by norm_num) (by norm_num)
    (by intro j; simp) u v hu hv

theorem global_six_zeta_chapter_complete (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    ∀ i : Fin 4,
      (∀ a b : ℕ, ((a*b:ℕ):ℂ)^(-s i) * originalFactorAt i s (a*b) =
        ∑ d ∈ a.divisors, ∑ e ∈ b.divisors,
          gammaAt i s (d,e) * tripleCoeffAt i s (a/d) * tripleCoeffAt i s (b/e)) ∧
      (∀ u v : ℂ, ρ < u.re → ρ < v.re →
        Summable (fun q => ‖originalTermAt i s u v q‖) ∧
        HasSum (originalTermAt i s u v) (restDirichletAt i s u v * sixZetaAt i s u v) ∧
        HasProd (fun p : Nat.Primes => doubleSeries (primeOriginalWeight p.val (reindexShifts i s))
          ((p.val:ℂ)^(-u)) ((p.val:ℂ)^(-v))) (originalDirichletAt i s u v)) := by
  intro i
  refine ⟨originalFactorAt_convolution i s ρ hρ0 hρ hs, ?_⟩
  intro u v hu hv
  exact ⟨originalTermAt_absolute i s ρ hρ0 hρ hs u v hu hv,
    originalTermAt_hasSum i s ρ hρ0 hρ hs u v hu hv,
    originalDirichletAt_euler_hasProd i s ρ hρ0 hρ hs u v hu hv⟩

end
end SixthMoment.Source.NoDPGlobalConvolution

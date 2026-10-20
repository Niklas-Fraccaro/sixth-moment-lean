import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FunProp
import SixthMoment.Analysis.Simplex.Linearity
import SixthMoment.Analysis.Simplex.PolynomialAverage

namespace SixthMoment
open scoped BigOperators

structure DirichletTerm where
  i : Nat
  j : Nat
  k : Nat
  l : Nat
  coefficient : Nat
  deriving DecidableEq, Repr

noncomputable def dirichletTermFunction (tr : DirichletTerm) (q₀ q₁ q₂ q₃ x y z : ℝ) : ℝ :=
  ((tr.coefficient : ℝ)*q₀^tr.i*q₁^tr.j*q₂^tr.k*q₃^tr.l) *
    (x^tr.i*y^tr.j*z^tr.k*(1-x-y-z)^tr.l)

noncomputable def simplexDot (q₀ q₁ q₂ q₃ x y z : ℝ) : ℝ :=
  q₀*x+q₁*y+q₂*z+q₃*(1-x-y-z)

theorem simplexExpectation_term (tr : DirichletTerm) (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (dirichletTermFunction tr q₀ q₁ q₂ q₃) =
      ((tr.coefficient : ℝ)*q₀^tr.i*q₁^tr.j*q₂^tr.k*q₃^tr.l) *
      (6*(Nat.factorial tr.i : ℝ)*Nat.factorial tr.j*Nat.factorial tr.k*Nat.factorial tr.l /
        Nat.factorial (tr.i+tr.j+tr.k+tr.l+3)) := by
  unfold dirichletTermFunction
  rw [simplexExpectation_const_mul, simplexExpectation_monomial]

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option Elab.async false

def dirichletTerms0 : Fin 1 → DirichletTerm :=
  ![⟨0,0,0,0,1⟩]

theorem dirichlet_moment_0 (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^0) =
      simplexMonomialAverage 0 q₀ q₁ q₂ q₃ := by
  have he : (fun x y z : ℝ => (simplexDot q₀ q₁ q₂ q₃ x y z)^0) =
      (fun x y z : ℝ => ∑ i : Fin 1, dirichletTermFunction (dirichletTerms0 i) q₀ q₁ q₂ q₃ x y z) := by
    funext x y z
    norm_num [simplexDot, dirichletTermFunction, dirichletTerms0, Fin.sum_univ_succ]
  rw [he, simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_term]
    norm_num [dirichletTerms0, Fin.sum_univ_succ, simplexMonomialAverage, homogeneousFour,
      Finite.factorial, Nat.factorial, Finset.sum_range_succ]
  · intro i
    dsimp [dirichletTermFunction]
    fun_prop

def dirichletTerms1 : Fin 4 → DirichletTerm :=
  ![⟨0,0,0,1,1⟩, ⟨0,0,1,0,1⟩, ⟨0,1,0,0,1⟩, ⟨1,0,0,0,1⟩]

theorem dirichlet_moment_1 (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^1) =
      simplexMonomialAverage 1 q₀ q₁ q₂ q₃ := by
  have he : (fun x y z : ℝ => (simplexDot q₀ q₁ q₂ q₃ x y z)^1) =
      (fun x y z : ℝ => ∑ i : Fin 4, dirichletTermFunction (dirichletTerms1 i) q₀ q₁ q₂ q₃ x y z) := by
    funext x y z
    norm_num [simplexDot, dirichletTermFunction, dirichletTerms1, Fin.sum_univ_succ]
    ring
  rw [he, simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_term]
    norm_num [dirichletTerms1, Fin.sum_univ_succ, simplexMonomialAverage, homogeneousFour,
      Finite.factorial, Nat.factorial, Finset.sum_range_succ]
    ring
  · intro i
    dsimp [dirichletTermFunction]
    fun_prop

def dirichletTerms2 : Fin 10 → DirichletTerm :=
  ![⟨0,0,0,2,1⟩, ⟨0,0,1,1,2⟩, ⟨0,0,2,0,1⟩, ⟨0,1,0,1,2⟩, ⟨0,1,1,0,2⟩, ⟨0,2,0,0,1⟩, ⟨1,0,0,1,2⟩, ⟨1,0,1,0,2⟩, ⟨1,1,0,0,2⟩, ⟨2,0,0,0,1⟩]

theorem dirichlet_moment_2 (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^2) =
      simplexMonomialAverage 2 q₀ q₁ q₂ q₃ := by
  have he : (fun x y z : ℝ => (simplexDot q₀ q₁ q₂ q₃ x y z)^2) =
      (fun x y z : ℝ => ∑ i : Fin 10, dirichletTermFunction (dirichletTerms2 i) q₀ q₁ q₂ q₃ x y z) := by
    funext x y z
    norm_num [simplexDot, dirichletTermFunction, dirichletTerms2, Fin.sum_univ_succ]
    ring
  rw [he, simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_term]
    norm_num [dirichletTerms2, Fin.sum_univ_succ, simplexMonomialAverage, homogeneousFour,
      Finite.factorial, Nat.factorial, Finset.sum_range_succ]
    ring
  · intro i
    dsimp [dirichletTermFunction]
    fun_prop

def dirichletTerms3 : Fin 20 → DirichletTerm :=
  ![⟨0,0,0,3,1⟩, ⟨0,0,1,2,3⟩, ⟨0,0,2,1,3⟩, ⟨0,0,3,0,1⟩, ⟨0,1,0,2,3⟩, ⟨0,1,1,1,6⟩, ⟨0,1,2,0,3⟩, ⟨0,2,0,1,3⟩, ⟨0,2,1,0,3⟩, ⟨0,3,0,0,1⟩, ⟨1,0,0,2,3⟩, ⟨1,0,1,1,6⟩, ⟨1,0,2,0,3⟩, ⟨1,1,0,1,6⟩, ⟨1,1,1,0,6⟩, ⟨1,2,0,0,3⟩, ⟨2,0,0,1,3⟩, ⟨2,0,1,0,3⟩, ⟨2,1,0,0,3⟩, ⟨3,0,0,0,1⟩]

theorem dirichlet_moment_3 (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^3) =
      simplexMonomialAverage 3 q₀ q₁ q₂ q₃ := by
  have he : (fun x y z : ℝ => (simplexDot q₀ q₁ q₂ q₃ x y z)^3) =
      (fun x y z : ℝ => ∑ i : Fin 20, dirichletTermFunction (dirichletTerms3 i) q₀ q₁ q₂ q₃ x y z) := by
    funext x y z
    norm_num [simplexDot, dirichletTermFunction, dirichletTerms3, Fin.sum_univ_succ]
    ring
  rw [he, simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_term]
    norm_num [dirichletTerms3, Fin.sum_univ_succ, simplexMonomialAverage, homogeneousFour,
      Finite.factorial, Nat.factorial, Finset.sum_range_succ]
    ring
  · intro i
    dsimp [dirichletTermFunction]
    fun_prop

def dirichletTerms4 : Fin 35 → DirichletTerm :=
  ![⟨0,0,0,4,1⟩, ⟨0,0,1,3,4⟩, ⟨0,0,2,2,6⟩, ⟨0,0,3,1,4⟩, ⟨0,0,4,0,1⟩, ⟨0,1,0,3,4⟩, ⟨0,1,1,2,12⟩, ⟨0,1,2,1,12⟩, ⟨0,1,3,0,4⟩, ⟨0,2,0,2,6⟩, ⟨0,2,1,1,12⟩, ⟨0,2,2,0,6⟩, ⟨0,3,0,1,4⟩, ⟨0,3,1,0,4⟩, ⟨0,4,0,0,1⟩, ⟨1,0,0,3,4⟩, ⟨1,0,1,2,12⟩, ⟨1,0,2,1,12⟩, ⟨1,0,3,0,4⟩, ⟨1,1,0,2,12⟩, ⟨1,1,1,1,24⟩, ⟨1,1,2,0,12⟩, ⟨1,2,0,1,12⟩, ⟨1,2,1,0,12⟩, ⟨1,3,0,0,4⟩, ⟨2,0,0,2,6⟩, ⟨2,0,1,1,12⟩, ⟨2,0,2,0,6⟩, ⟨2,1,0,1,12⟩, ⟨2,1,1,0,12⟩, ⟨2,2,0,0,6⟩, ⟨3,0,0,1,4⟩, ⟨3,0,1,0,4⟩, ⟨3,1,0,0,4⟩, ⟨4,0,0,0,1⟩]

theorem dirichlet_moment_4 (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^4) =
      simplexMonomialAverage 4 q₀ q₁ q₂ q₃ := by
  have he : (fun x y z : ℝ => (simplexDot q₀ q₁ q₂ q₃ x y z)^4) =
      (fun x y z : ℝ => ∑ i : Fin 35, dirichletTermFunction (dirichletTerms4 i) q₀ q₁ q₂ q₃ x y z) := by
    funext x y z
    norm_num [simplexDot, dirichletTermFunction, dirichletTerms4, Fin.sum_univ_succ]
    ring
  rw [he, simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_term]
    norm_num [dirichletTerms4, Fin.sum_univ_succ, simplexMonomialAverage, homogeneousFour,
      Finite.factorial, Nat.factorial, Finset.sum_range_succ]
    ring
  · intro i
    dsimp [dirichletTermFunction]
    fun_prop

theorem dirichlet_moment_le_four (r : Fin 5) (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => (simplexDot q₀ q₁ q₂ q₃ x y z)^r.val) =
      simplexMonomialAverage r.val q₀ q₁ q₂ q₃ := by
  fin_cases r
  · exact dirichlet_moment_0 _ _ _ _
  · exact dirichlet_moment_1 _ _ _ _
  · exact dirichlet_moment_2 _ _ _ _
  · exact dirichlet_moment_3 _ _ _ _
  · exact dirichlet_moment_4 _ _ _ _

end SixthMoment

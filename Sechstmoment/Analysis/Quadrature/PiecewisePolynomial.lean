import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FunProp
import Sechstmoment.Analysis.Quadrature.Interval

namespace Sechstmoment
open scoped BigOperators

def PolynomialOn (n : Nat) (f : ℝ → ℝ) (l u : ℝ) : Prop :=
  ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ ∀ t ∈ Set.Icc l u, p.eval t = f t

theorem PolynomialOn.mono {n m : Nat} {f : ℝ → ℝ} {l u : ℝ}
    (h : PolynomialOn n f l u) (hn : n ≤ m) : PolynomialOn m f l u := by
  obtain ⟨p,hp,he⟩ := h
  exact ⟨p,hp.trans hn,he⟩

theorem PolynomialOn.congr {n : Nat} {f g : ℝ → ℝ} {l u : ℝ}
    (h : PolynomialOn n f l u) (he : ∀ t ∈ Set.Icc l u, f t = g t) :
    PolynomialOn n g l u := by
  obtain ⟨p,hp,hf⟩ := h
  exact ⟨p,hp,fun t ht => (hf t ht).trans (he t ht)⟩

theorem polynomialOn_const (c l u : ℝ) : PolynomialOn 0 (fun _ => c) l u := by
  exact ⟨Polynomial.C c, by simp, by simp⟩

theorem polynomialOn_id (l u : ℝ) : PolynomialOn 1 (fun t => t) l u := by
  exact ⟨Polynomial.X, Polynomial.natDegree_X_le, by simp⟩

theorem PolynomialOn.add {n : Nat} {f g : ℝ → ℝ} {l u : ℝ}
    (hf : PolynomialOn n f l u) (hg : PolynomialOn n g l u) :
    PolynomialOn n (fun t => f t+g t) l u := by
  obtain ⟨p,hp,he⟩ := hf
  obtain ⟨q,hq,hf⟩ := hg
  refine ⟨p+q, Polynomial.natDegree_add_le_of_degree_le hp hq, ?_⟩
  intro t ht
  simp only [Polynomial.eval_add, he t ht, hf t ht]

theorem PolynomialOn.sub {n : Nat} {f g : ℝ → ℝ} {l u : ℝ}
    (hf : PolynomialOn n f l u) (hg : PolynomialOn n g l u) :
    PolynomialOn n (fun t => f t-g t) l u := by
  obtain ⟨p,hp,he⟩ := hf
  obtain ⟨q,hq,hf⟩ := hg
  refine ⟨p-q, (Polynomial.natDegree_sub_le p q).trans (max_le hp hq), ?_⟩
  intro t ht
  simp only [Polynomial.eval_sub, he t ht, hf t ht]

theorem PolynomialOn.mul {n m : Nat} {f g : ℝ → ℝ} {l u : ℝ}
    (hf : PolynomialOn n f l u) (hg : PolynomialOn m g l u) :
    PolynomialOn (n+m) (fun t => f t*g t) l u := by
  obtain ⟨p,hp,he⟩ := hf
  obtain ⟨q,hq,hf⟩ := hg
  refine ⟨p*q, Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq), ?_⟩
  intro t ht
  simp only [Polynomial.eval_mul, he t ht, hf t ht]

theorem PolynomialOn.const_mul {n : Nat} {f : ℝ → ℝ} {l u : ℝ}
    (hf : PolynomialOn n f l u) (c : ℝ) :
    PolynomialOn n (fun t => c*f t) l u := by
  simpa using (polynomialOn_const c l u).mul hf

theorem PolynomialOn.pow {n : Nat} {f : ℝ → ℝ} {l u : ℝ}
    (hf : PolynomialOn n f l u) (k : Nat) :
    PolynomialOn (k*n) (fun t => (f t)^k) l u := by
  obtain ⟨p,hp,he⟩ := hf
  refine ⟨p^k, Polynomial.natDegree_pow_le_of_le k hp, ?_⟩
  intro t ht
  simp only [Polynomial.eval_pow, he t ht]

theorem polynomialOn_affine (a b l u : ℝ) :
    PolynomialOn 1 (fun t => a+b*t) l u := by
  exact ((polynomialOn_const a l u).mono (by omega)).add
    ((polynomialOn_id l u).const_mul b)

theorem polynomialOn_hinge_right (k l u : ℝ) (hk : k ≤ l ∨ u ≤ k) :
    PolynomialOn 1 (fun t => max (t-k) 0) l u := by
  rcases hk with hk | hk
  · apply ((polynomialOn_id l u).sub ((polynomialOn_const k l u).mono (by omega))).congr
    intro t ht
    exact (max_eq_left (by linarith [ht.1])).symm
  · apply ((polynomialOn_const 0 l u).mono (by omega)).congr
    intro t ht
    exact (max_eq_right (by linarith [ht.2])).symm

theorem polynomialOn_hinge_left (k l u : ℝ) (hk : k ≤ l ∨ u ≤ k) :
    PolynomialOn 1 (fun t => max (k-t) 0) l u := by
  rcases hk with hk | hk
  · apply ((polynomialOn_const 0 l u).mono (by omega)).congr
    intro t ht
    exact (max_eq_right (by linarith [ht.1])).symm
  · apply (((polynomialOn_const k l u).mono (by omega)).sub (polynomialOn_id l u)).congr
    intro t ht
    exact (max_eq_left (by linarith [ht.2])).symm

theorem polynomial_nc_interval_exact (p : Polynomial ℝ) (hp : p.natDegree ≤ 12)
    (l u : ℝ) :
    (∫ t in l..u, p.eval t) =
      (u-l)*(∑ j : Fin 13, ncWeight j*p.eval (l+(u-l)*(j.val/12))) := by
  have he (t : ℝ) : p.eval t = ∑ k : Fin 13, p.coeff k.val*t^k.val := by
    rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < 13),
      ← Fin.sum_univ_eq_sum_range]
  simp_rw [he]
  exact nc_interval_integral_exact _ l u

theorem polynomialOn_nc_interval_exact {f : ℝ → ℝ} {l u : ℝ}
    (hlu : l ≤ u) (hf : PolynomialOn 12 f l u) :
    (∫ t in l..u, f t) =
      (u-l)*(∑ j : Fin 13, ncWeight j*f (l+(u-l)*(j.val/12))) := by
  obtain ⟨p,hp,he⟩ := hf
  have hn (j : Fin 13) : l+(u-l)*(j.val/12) ∈ Set.Icc l u := by
    have hj : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have hj12 : (j.val : ℝ) ≤ 12 := by exact_mod_cast (by omega : j.val ≤ 12)
    constructor <;> nlinarith
  calc
    (∫ t in l..u, f t) = ∫ t in l..u, p.eval t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hlu] at ht
      exact (he t ht).symm
    _ = (u-l)*(∑ j : Fin 13, ncWeight j*p.eval (l+(u-l)*(j.val/12))) :=
      polynomial_nc_interval_exact p hp l u
    _ = _ := by simp_rw [he _ (hn _)]

end Sechstmoment

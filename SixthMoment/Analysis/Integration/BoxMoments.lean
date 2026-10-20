import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FunProp
import SixthMoment.Analysis.Integration.PolynomialIntegral

namespace SixthMoment
open scoped BigOperators

structure TriplePowerTerm where
  i : Nat
  j : Nat
  k : Nat
  coefficient : Nat

noncomputable def boxIntegral (r s t : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in -(r/2)..r/2, ∫ y in -(s/2)..s/2, ∫ z in -(t/2)..t/2, f x y z

noncomputable def symmetricPowerIntegral (r : ℝ) (k : Nat) : ℝ :=
  ∫ x in -(r/2)..r/2, x^k

theorem boxIntegral_terms {n : Nat} (tr : Fin n → TriplePowerTerm) (r s t : ℝ) :
    boxIntegral r s t (fun x y z => ∑ a : Fin n,
      (tr a).coefficient*x^(tr a).i*y^(tr a).j*z^(tr a).k) =
      ∑ a : Fin n, (tr a).coefficient*symmetricPowerIntegral r (tr a).i*
        symmetricPowerIntegral s (tr a).j*symmetricPowerIntegral t (tr a).k := by
  have hz (x y : ℝ) :
      (∫ z in -(t/2)..t/2, ∑ a : Fin n,
        (tr a).coefficient*x^(tr a).i*y^(tr a).j*z^(tr a).k) =
      ∑ a : Fin n, (tr a).coefficient*x^(tr a).i*y^(tr a).j*
        symmetricPowerIntegral t (tr a).k := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul, symmetricPowerIntegral]
    · intro a _
      apply Continuous.intervalIntegrable
      fun_prop
  have hy (x : ℝ) :
      (∫ y in -(s/2)..s/2, ∑ a : Fin n,
        (tr a).coefficient*x^(tr a).i*y^(tr a).j*symmetricPowerIntegral t (tr a).k) =
      ∑ a : Fin n, (tr a).coefficient*x^(tr a).i*
        symmetricPowerIntegral s (tr a).j*symmetricPowerIntegral t (tr a).k := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        symmetricPowerIntegral]
    · intro a _
      apply Continuous.intervalIntegrable
      fun_prop
  unfold boxIntegral
  simp_rw [hz, hy]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      symmetricPowerIntegral]
  · intro a _
    apply Continuous.intervalIntegrable
    fun_prop

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def triplePowerTerms0 : Fin 1 → TriplePowerTerm :=
  ![⟨0,0,0,1⟩]

theorem box_power_0 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^0) =
      (1 : ℝ)/1*r^1*s^1*t^1 := by
  have he : (fun x y z : ℝ => (x+y+z)^0) =
      (fun x y z : ℝ => ∑ a : Fin 1,
        (triplePowerTerms0 a).coefficient*x^(triplePowerTerms0 a).i*
          y^(triplePowerTerms0 a).j*z^(triplePowerTerms0 a).k) := by
    funext x y z
    norm_num [triplePowerTerms0, Fin.sum_univ_succ]

  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms0, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]


def triplePowerTerms1 : Fin 3 → TriplePowerTerm :=
  ![⟨0,0,1,1⟩, ⟨0,1,0,1⟩, ⟨1,0,0,1⟩]

theorem box_power_1 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^1) =
      (0 : ℝ) := by
  have he : (fun x y z : ℝ => (x+y+z)^1) =
      (fun x y z : ℝ => ∑ a : Fin 3,
        (triplePowerTerms1 a).coefficient*x^(triplePowerTerms1 a).i*
          y^(triplePowerTerms1 a).j*z^(triplePowerTerms1 a).k) := by
    funext x y z
    norm_num [triplePowerTerms1, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms1, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]


def triplePowerTerms2 : Fin 6 → TriplePowerTerm :=
  ![⟨0,0,2,1⟩, ⟨0,1,1,2⟩, ⟨0,2,0,1⟩, ⟨1,0,1,2⟩, ⟨1,1,0,2⟩, ⟨2,0,0,1⟩]

theorem box_power_2 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^2) =
      (1 : ℝ)/12*r^1*s^1*t^3 +
      (1 : ℝ)/12*r^1*s^3*t^1 +
      (1 : ℝ)/12*r^3*s^1*t^1 := by
  have he : (fun x y z : ℝ => (x+y+z)^2) =
      (fun x y z : ℝ => ∑ a : Fin 6,
        (triplePowerTerms2 a).coefficient*x^(triplePowerTerms2 a).i*
          y^(triplePowerTerms2 a).j*z^(triplePowerTerms2 a).k) := by
    funext x y z
    norm_num [triplePowerTerms2, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms2, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms3 : Fin 10 → TriplePowerTerm :=
  ![⟨0,0,3,1⟩, ⟨0,1,2,3⟩, ⟨0,2,1,3⟩, ⟨0,3,0,1⟩, ⟨1,0,2,3⟩, ⟨1,1,1,6⟩, ⟨1,2,0,3⟩, ⟨2,0,1,3⟩, ⟨2,1,0,3⟩, ⟨3,0,0,1⟩]

theorem box_power_3 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^3) =
      (0 : ℝ) := by
  have he : (fun x y z : ℝ => (x+y+z)^3) =
      (fun x y z : ℝ => ∑ a : Fin 10,
        (triplePowerTerms3 a).coefficient*x^(triplePowerTerms3 a).i*
          y^(triplePowerTerms3 a).j*z^(triplePowerTerms3 a).k) := by
    funext x y z
    norm_num [triplePowerTerms3, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms3, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms4 : Fin 15 → TriplePowerTerm :=
  ![⟨0,0,4,1⟩, ⟨0,1,3,4⟩, ⟨0,2,2,6⟩, ⟨0,3,1,4⟩, ⟨0,4,0,1⟩, ⟨1,0,3,4⟩, ⟨1,1,2,12⟩, ⟨1,2,1,12⟩, ⟨1,3,0,4⟩, ⟨2,0,2,6⟩, ⟨2,1,1,12⟩, ⟨2,2,0,6⟩, ⟨3,0,1,4⟩, ⟨3,1,0,4⟩, ⟨4,0,0,1⟩]

theorem box_power_4 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^4) =
      (1 : ℝ)/80*r^1*s^1*t^5 +
      (1 : ℝ)/24*r^1*s^3*t^3 +
      (1 : ℝ)/80*r^1*s^5*t^1 +
      (1 : ℝ)/24*r^3*s^1*t^3 +
      (1 : ℝ)/24*r^3*s^3*t^1 +
      (1 : ℝ)/80*r^5*s^1*t^1 := by
  have he : (fun x y z : ℝ => (x+y+z)^4) =
      (fun x y z : ℝ => ∑ a : Fin 15,
        (triplePowerTerms4 a).coefficient*x^(triplePowerTerms4 a).i*
          y^(triplePowerTerms4 a).j*z^(triplePowerTerms4 a).k) := by
    funext x y z
    norm_num [triplePowerTerms4, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms4, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms5 : Fin 21 → TriplePowerTerm :=
  ![⟨0,0,5,1⟩, ⟨0,1,4,5⟩, ⟨0,2,3,10⟩, ⟨0,3,2,10⟩, ⟨0,4,1,5⟩, ⟨0,5,0,1⟩, ⟨1,0,4,5⟩, ⟨1,1,3,20⟩, ⟨1,2,2,30⟩, ⟨1,3,1,20⟩, ⟨1,4,0,5⟩, ⟨2,0,3,10⟩, ⟨2,1,2,30⟩, ⟨2,2,1,30⟩, ⟨2,3,0,10⟩, ⟨3,0,2,10⟩, ⟨3,1,1,20⟩, ⟨3,2,0,10⟩, ⟨4,0,1,5⟩, ⟨4,1,0,5⟩, ⟨5,0,0,1⟩]

theorem box_power_5 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^5) =
      (0 : ℝ) := by
  have he : (fun x y z : ℝ => (x+y+z)^5) =
      (fun x y z : ℝ => ∑ a : Fin 21,
        (triplePowerTerms5 a).coefficient*x^(triplePowerTerms5 a).i*
          y^(triplePowerTerms5 a).j*z^(triplePowerTerms5 a).k) := by
    funext x y z
    norm_num [triplePowerTerms5, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms5, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms6 : Fin 28 → TriplePowerTerm :=
  ![⟨0,0,6,1⟩, ⟨0,1,5,6⟩, ⟨0,2,4,15⟩, ⟨0,3,3,20⟩, ⟨0,4,2,15⟩, ⟨0,5,1,6⟩, ⟨0,6,0,1⟩, ⟨1,0,5,6⟩, ⟨1,1,4,30⟩, ⟨1,2,3,60⟩, ⟨1,3,2,60⟩, ⟨1,4,1,30⟩, ⟨1,5,0,6⟩, ⟨2,0,4,15⟩, ⟨2,1,3,60⟩, ⟨2,2,2,90⟩, ⟨2,3,1,60⟩, ⟨2,4,0,15⟩, ⟨3,0,3,20⟩, ⟨3,1,2,60⟩, ⟨3,2,1,60⟩, ⟨3,3,0,20⟩, ⟨4,0,2,15⟩, ⟨4,1,1,30⟩, ⟨4,2,0,15⟩, ⟨5,0,1,6⟩, ⟨5,1,0,6⟩, ⟨6,0,0,1⟩]

theorem box_power_6 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^6) =
      (1 : ℝ)/448*r^1*s^1*t^7 +
      (1 : ℝ)/64*r^1*s^3*t^5 +
      (1 : ℝ)/64*r^1*s^5*t^3 +
      (1 : ℝ)/448*r^1*s^7*t^1 +
      (1 : ℝ)/64*r^3*s^1*t^5 +
      (5 : ℝ)/96*r^3*s^3*t^3 +
      (1 : ℝ)/64*r^3*s^5*t^1 +
      (1 : ℝ)/64*r^5*s^1*t^3 +
      (1 : ℝ)/64*r^5*s^3*t^1 +
      (1 : ℝ)/448*r^7*s^1*t^1 := by
  have he : (fun x y z : ℝ => (x+y+z)^6) =
      (fun x y z : ℝ => ∑ a : Fin 28,
        (triplePowerTerms6 a).coefficient*x^(triplePowerTerms6 a).i*
          y^(triplePowerTerms6 a).j*z^(triplePowerTerms6 a).k) := by
    funext x y z
    norm_num [triplePowerTerms6, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms6, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms7 : Fin 36 → TriplePowerTerm :=
  ![⟨0,0,7,1⟩, ⟨0,1,6,7⟩, ⟨0,2,5,21⟩, ⟨0,3,4,35⟩, ⟨0,4,3,35⟩, ⟨0,5,2,21⟩, ⟨0,6,1,7⟩, ⟨0,7,0,1⟩, ⟨1,0,6,7⟩, ⟨1,1,5,42⟩, ⟨1,2,4,105⟩, ⟨1,3,3,140⟩, ⟨1,4,2,105⟩, ⟨1,5,1,42⟩, ⟨1,6,0,7⟩, ⟨2,0,5,21⟩, ⟨2,1,4,105⟩, ⟨2,2,3,210⟩, ⟨2,3,2,210⟩, ⟨2,4,1,105⟩, ⟨2,5,0,21⟩, ⟨3,0,4,35⟩, ⟨3,1,3,140⟩, ⟨3,2,2,210⟩, ⟨3,3,1,140⟩, ⟨3,4,0,35⟩, ⟨4,0,3,35⟩, ⟨4,1,2,105⟩, ⟨4,2,1,105⟩, ⟨4,3,0,35⟩, ⟨5,0,2,21⟩, ⟨5,1,1,42⟩, ⟨5,2,0,21⟩, ⟨6,0,1,7⟩, ⟨6,1,0,7⟩, ⟨7,0,0,1⟩]

theorem box_power_7 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^7) =
      (0 : ℝ) := by
  have he : (fun x y z : ℝ => (x+y+z)^7) =
      (fun x y z : ℝ => ∑ a : Fin 36,
        (triplePowerTerms7 a).coefficient*x^(triplePowerTerms7 a).i*
          y^(triplePowerTerms7 a).j*z^(triplePowerTerms7 a).k) := by
    funext x y z
    norm_num [triplePowerTerms7, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms7, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

def triplePowerTerms8 : Fin 45 → TriplePowerTerm :=
  ![⟨0,0,8,1⟩, ⟨0,1,7,8⟩, ⟨0,2,6,28⟩, ⟨0,3,5,56⟩, ⟨0,4,4,70⟩, ⟨0,5,3,56⟩, ⟨0,6,2,28⟩, ⟨0,7,1,8⟩, ⟨0,8,0,1⟩, ⟨1,0,7,8⟩, ⟨1,1,6,56⟩, ⟨1,2,5,168⟩, ⟨1,3,4,280⟩, ⟨1,4,3,280⟩, ⟨1,5,2,168⟩, ⟨1,6,1,56⟩, ⟨1,7,0,8⟩, ⟨2,0,6,28⟩, ⟨2,1,5,168⟩, ⟨2,2,4,420⟩, ⟨2,3,3,560⟩, ⟨2,4,2,420⟩, ⟨2,5,1,168⟩, ⟨2,6,0,28⟩, ⟨3,0,5,56⟩, ⟨3,1,4,280⟩, ⟨3,2,3,560⟩, ⟨3,3,2,560⟩, ⟨3,4,1,280⟩, ⟨3,5,0,56⟩, ⟨4,0,4,70⟩, ⟨4,1,3,280⟩, ⟨4,2,2,420⟩, ⟨4,3,1,280⟩, ⟨4,4,0,70⟩, ⟨5,0,3,56⟩, ⟨5,1,2,168⟩, ⟨5,2,1,168⟩, ⟨5,3,0,56⟩, ⟨6,0,2,28⟩, ⟨6,1,1,56⟩, ⟨6,2,0,28⟩, ⟨7,0,1,8⟩, ⟨7,1,0,8⟩, ⟨8,0,0,1⟩]

theorem box_power_8 (r s t : ℝ) :
    boxIntegral r s t (fun x y z => (x+y+z)^8) =
      (1 : ℝ)/2304*r^1*s^1*t^9 +
      (1 : ℝ)/192*r^1*s^3*t^7 +
      (7 : ℝ)/640*r^1*s^5*t^5 +
      (1 : ℝ)/192*r^1*s^7*t^3 +
      (1 : ℝ)/2304*r^1*s^9*t^1 +
      (1 : ℝ)/192*r^3*s^1*t^7 +
      (7 : ℝ)/192*r^3*s^3*t^5 +
      (7 : ℝ)/192*r^3*s^5*t^3 +
      (1 : ℝ)/192*r^3*s^7*t^1 +
      (7 : ℝ)/640*r^5*s^1*t^5 +
      (7 : ℝ)/192*r^5*s^3*t^3 +
      (7 : ℝ)/640*r^5*s^5*t^1 +
      (1 : ℝ)/192*r^7*s^1*t^3 +
      (1 : ℝ)/192*r^7*s^3*t^1 +
      (1 : ℝ)/2304*r^9*s^1*t^1 := by
  have he : (fun x y z : ℝ => (x+y+z)^8) =
      (fun x y z : ℝ => ∑ a : Fin 45,
        (triplePowerTerms8 a).coefficient*x^(triplePowerTerms8 a).i*
          y^(triplePowerTerms8 a).j*z^(triplePowerTerms8 a).k) := by
    funext x y z
    norm_num [triplePowerTerms8, Fin.sum_univ_succ]
    ring
  rw [he, boxIntegral_terms]
  norm_num [triplePowerTerms8, Fin.sum_univ_succ, symmetricPowerIntegral, integral_pow]
  ring

end SixthMoment

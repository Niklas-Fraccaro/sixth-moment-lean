import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
import SixthMoment.Analysis.Alternants.JointLimits
import Std


namespace SixthMoment
open Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

theorem exponentialAlternant_translate (x q : Fin 4 → ℂ) (c : ℂ) :
    exponentialAlternant (fun i => x i+c) q =
      Complex.exp (c*(2+∑ j, q j))*exponentialAlternant x q := by
  have hmat : expAlternantMatrix (fun i => x i+c) q =
      expAlternantMatrix x q * Matrix.diagonal (fun j => Complex.exp (c*q j)) := by
    ext i j
    simp only [expAlternantMatrix, Matrix.mul_diagonal]
    rw [add_mul, Complex.exp_add]
  have hv : fourVandermonde (fun i => x i+c) = fourVandermonde x := by
    unfold fourVandermonde
    simp only [add_sub_add_right_eq_sub]
  have hs : (∏ j : Fin 4, Complex.exp (c*q j)) = Complex.exp (c*∑ j, q j) := by
    rw [← Complex.exp_sum, Finset.mul_sum]
  unfold exponentialAlternant
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, hs, hv]
  rw [show (x 0+c)+(x 1+c) = (x 0+x 1)+2*c by ring, Complex.exp_add]
  rw [show c*(2+∑ j, q j) = 2*c+c*(∑ j, q j) by ring, Complex.exp_add]
  simp only [Complex.exp_add]
  ring

theorem exponentialAlternant_relative_tendsto {α : Type*} {L : Filter α}
    (q : Fin 4 → ℂ) (z : ℂ) (hz : z ≠ 0) (e u w : α → ℂ)
    (he : Tendsto e L (𝓝 0)) (hu : Tendsto u L (𝓝 z)) (hw : Tendsto w L (𝓝 0))
    (hne : ∀ᶠ x in L, e x ≠ 0 ∧ w x ≠ 0 ∧ w x ≠ e x) :
    Tendsto (fun x => exponentialAlternant (![0,e x,u x,w x]) q)
      L (𝓝 (confluentExpGenerator q z)) := by
  have hpair : Tendsto (fun x => (e x,w x)) L
      (𝓝[{p : ℂ × ℂ | p.2 ≠ p.1}] (0,0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨he.prodMk_nhds hw, hne.mono (fun _ h => h.2.2)⟩
  have hmat : Tendsto (fun x => jointSlopeExpMatrix q (e x) (u x) (w x))
      L (𝓝 (secondSlopeExpMatrix q z 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i
    all_goals simp only [jointSlopeExpMatrix, secondSlopeExpMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
    · exact tendsto_const_nhds
    · simpa only [expFirstSlope_zero, Function.comp_def] using
        ((expFirstSlope_continuous (q j)).tendsto 0).comp he
    · exact ((Complex.continuous_exp.comp (continuous_id.mul_const (q j))).tendsto z).comp hu
    · simpa only [expSecondSlope_zero, Function.comp_def] using
        (expFirstSlope_tendsto_twoPointSlope (q j)).comp hpair
  have hdet : Tendsto (fun x => (jointSlopeExpMatrix q (e x) (u x) (w x)).det)
      L (𝓝 (secondSlopeExpMatrix q z 0).det) :=
    (continuous_id.matrix_det : Continuous
      (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.det)).continuousAt.tendsto.comp hmat
  have hexp : Tendsto (fun x => Complex.exp (e x)) L (𝓝 1) := by
    simpa only [Complex.exp_zero, Function.comp_def] using
      (Complex.continuous_exp.tendsto 0).comp he
  have hden : Tendsto (fun x => u x*(u x-e x)*(w x-u x))
      L (𝓝 (z*(z-0)*(0-z))) := (hu.mul (hu.sub he)).mul (hw.sub hu)
  have hd : z*(z-0)*(0-z) ≠ 0 := by
    simpa only [sub_zero, zero_sub] using mul_ne_zero (mul_ne_zero hz hz) (neg_ne_zero.mpr hz)
  have ht := (hexp.mul hdet).div hden hd
  simp only [one_mul] at ht
  have hv : (secondSlopeExpMatrix q z 0).det / (z*(z-0)*(0-z)) =
      confluentExpGenerator q z := by
    rw [secondSlopeExpMatrix_det_zero, confluentExpGenerator]
    field_simp
    ring
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [hne] with x hx
  exact (exponentialAlternant_joint_regular q (e x) (u x) (w x) hx.1 hx.2.1 hx.2.2).symm

theorem exponentialAlternant_joint_shift_limit (q : Fin 4 → ℂ) (z : ℂ)
    (hz : z ≠ 0) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0]))
      (𝓝 (confluentExpGenerator q z)) := by
  let L := 𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0])
  have hx (j : Fin 4) : Tendsto (fun x : Fin 4 → ℂ => x j) L (𝓝 ((![0,0,z,0] : Fin 4 → ℂ) j)) :=
    (continuous_apply j).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun x : Fin 4 → ℂ => x 1-x 0) L (𝓝 0) := by
    simpa using (hx 1).sub (hx 0)
  have hu : Tendsto (fun x : Fin 4 → ℂ => x 2-x 0) L (𝓝 z) := by
    simpa using (hx 2).sub (hx 0)
  have hw : Tendsto (fun x : Fin 4 → ℂ => x 3-x 0) L (𝓝 0) := by
    simpa using (hx 3).sub (hx 0)
  have hne : ∀ᶠ x : Fin 4 → ℂ in L,
      x 1-x 0 ≠ 0 ∧ x 3-x 0 ≠ 0 ∧ x 3-x 0 ≠ x 1-x 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    refine ⟨sub_ne_zero.mpr (hx.ne (by decide)), sub_ne_zero.mpr (hx.ne (by decide)), ?_⟩
    exact fun h => hx.ne (by decide : (3 : Fin 4) ≠ 1) (sub_left_inj.mp h)
  have ht := exponentialAlternant_relative_tendsto q z hz
    (fun x : Fin 4 → ℂ => x 1-x 0) (fun x => x 2-x 0) (fun x => x 3-x 0) he hu hw hne
  have hc : Tendsto (fun x : Fin 4 → ℂ => Complex.exp (x 0*(2+∑ j, q j))) L (𝓝 1) := by
    have h0 : Tendsto (fun x : Fin 4 → ℂ => x 0) L (𝓝 0) := by simpa using hx 0
    have hm : Tendsto (fun x : Fin 4 → ℂ => x 0*(2+∑ j, q j)) L (𝓝 0) := by
      simpa using h0.mul_const (2+∑ j, q j)
    simpa [Function.comp_def] using (Complex.continuous_exp.tendsto 0).comp hm
  have hall := hc.mul ht
  simp only [one_mul] at hall
  apply hall.congr'
  exact Eventually.of_forall (fun x => by
    have hr : (fun i : Fin 4 => (![0,x 1-x 0,x 2-x 0,x 3-x 0] : Fin 4 → ℂ) i+x 0) = x := by
      funext i
      fin_cases i <;> simp
    simpa only [hr] using (exponentialAlternant_translate
      (![0,x 1-x 0,x 2-x 0,x 3-x 0]) q (x 0)).symm)

theorem exponentialAlternant_joint_shift_limit_eq_simplex (q : Fin 4 → ℂ) (z : ℂ)
    (hq : Function.Injective q) (hz : z ≠ 0) :
    Tendsto (fun x : Fin 4 → ℂ => exponentialAlternant x q)
      (𝓝[{x : Fin 4 → ℂ | Function.Injective x}] (![0,0,z,0]))
      (𝓝 (fourVandermonde q/12*simplexExpGenerator q z)) := by
  simpa only [confluentExpGenerator_eq_simplex q z hq hz] using
    exponentialAlternant_joint_shift_limit q z hz

end SixthMoment

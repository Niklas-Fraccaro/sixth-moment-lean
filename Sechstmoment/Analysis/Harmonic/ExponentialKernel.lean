import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Sechstmoment.Analysis.Harmonic.LogQuadrature

/-! Compact-interval bounds for the actual shifted exponential kernels. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

structure RegularProfile (η : ℝ) (f : ℝ → ℂ) (B D : ℝ) : Prop where
  bound_nonneg : 0 ≤ B
  lip_nonneg : 0 ≤ D
  continuous : ContinuousOn f (Icc 0 η)
  norm_le : ∀ x ∈ Icc 0 η, ‖f x‖ ≤ B
  norm_sub_le : ∀ x ∈ Icc 0 η, ∀ y ∈ Icc 0 η, ‖f x-f y‖ ≤ D*|x-y|

theorem regularProfile_of_bounds {η B D : ℝ} {f : ℝ → ℂ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hbound : ∀ x ∈ Icc 0 η, ‖f x‖ ≤ B)
    (hLip : ∀ x ∈ Icc 0 η, ∀ y ∈ Icc 0 η, ‖f x-f y‖ ≤ D*|x-y|) :
    RegularProfile η f B D := by
  have hl : LipschitzOnWith ⟨D,hD⟩ f (Icc 0 η) :=
    LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
      change dist (f x) (f y) ≤ D*dist x y
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hLip x hx y hy)
  exact ⟨hB,hD,hl.continuousOn,hbound,hLip⟩

def expKernel (ν : ℂ) (x : ℝ) : ℂ := Complex.exp (-ν*(x:ℂ))
def kernelBound (η R : ℝ) : ℝ := Real.exp (R*η)

theorem kernelBound_pos (η R : ℝ) : 0 < kernelBound η R := Real.exp_pos _

theorem kernelBound_one_le {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R) :
    1 ≤ kernelBound η R := Real.one_le_exp_iff.mpr (mul_nonneg hR hη)

theorem expKernel_continuous (ν : ℂ) : Continuous (expKernel ν) := by
  unfold expKernel
  fun_prop

theorem expKernel_hasDerivAt (ν : ℂ) (x : ℝ) :
    HasDerivAt (expKernel ν) (expKernel ν x * (-ν)) x := by
  unfold expKernel
  convert ((hasDerivAt_id x).ofReal_comp.const_mul (-ν)).cexp using 1 <;> simp

theorem expKernel_norm {η R : ℝ} (hR : 0 ≤ R) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    {x : ℝ} (hx : x ∈ Icc 0 η) : ‖expKernel ν x‖ ≤ kernelBound η R := by
  have hn : ‖-ν*(x:ℂ)‖ ≤ R*η := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact mul_le_mul hν hx.2 hx.1 hR
  rw [expKernel, Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hn)

theorem expKernel_norm_sub {η R : ℝ} (hR : 0 ≤ R) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    {x y : ℝ} (hx : x ∈ Icc 0 η) (hy : y ∈ Icc 0 η) :
    ‖expKernel ν x-expKernel ν y‖ ≤ (R*kernelBound η R)*|x-y| := by
  have hb (u : ℝ) (hu : u ∈ Icc 0 η) : ‖expKernel ν u * (-ν)‖ ≤ R*kernelBound η R := by
    rw [norm_mul,norm_neg]
    exact (mul_le_mul (expKernel_norm hR hν hu) hν (norm_nonneg _) (kernelBound_pos η R).le).trans_eq
      (by ring)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) η).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (expKernel_hasDerivAt ν u).hasDerivWithinAt) hb hy hx

theorem regularProfile_section {η R B D t : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hR : 0 ≤ R) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    (ht : t ∈ Icc 0 η) :
    RegularProfile t (fun x => f (t-x)*expKernel ν x)
      (B*kernelBound η R) (kernelBound η R*(D+B*R)) := by
  have harg (x : ℝ) (hx : x ∈ Icc 0 t) : t-x ∈ Icc 0 η := by
    constructor <;> linarith [hx.1,hx.2,ht.2]
  have hxη (x : ℝ) (hx : x ∈ Icc 0 t) : x ∈ Icc 0 η := ⟨hx.1,hx.2.trans ht.2⟩
  have hB := hf.bound_nonneg
  have hD := hf.lip_nonneg
  have hE := (kernelBound_pos η R).le
  apply regularProfile_of_bounds (by positivity) (by positivity)
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul (hf.norm_le _ (harg x hx)) (expKernel_norm hR hν (hxη x hx))
      (norm_nonneg _) hB
  · intro x hx y hy
    have hid : f (t-x)*expKernel ν x-f (t-y)*expKernel ν y =
        (f (t-x)-f (t-y))*expKernel ν x + f (t-y)*(expKernel ν x-expKernel ν y) := by ring
    have hxy : |(t-x)-(t-y)| = |x-y| := by
      rw [show (t-x)-(t-y) = -(x-y) by ring, abs_neg]
    have hfxy := hf.norm_sub_le _ (harg x hx) _ (harg y hy)
    rw [hxy] at hfxy
    rw [hid]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (D*|x-y|)*kernelBound η R + B*((R*kernelBound η R)*|x-y|) :=
        add_le_add (mul_le_mul hfxy (expKernel_norm hR hν (hxη x hx))
          (norm_nonneg _) (by positivity))
          (mul_le_mul (hf.norm_le _ (harg y hy)) (expKernel_norm_sub hR hν (hxη x hx) (hxη y hy))
            (norm_nonneg _) hB)
      _ = _ := by ring

end
end Sechstmoment.Source.NoDPHarmonic

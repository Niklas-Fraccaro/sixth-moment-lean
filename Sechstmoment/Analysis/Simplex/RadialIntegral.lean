import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Analysis.Simplex.Exponential

/-! Fubini on the genuine triangular integration region. -/

namespace Sechstmoment
open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 0

theorem triangular_integral_swap_from (L H : ℝ) (hH : L ≤ H)
    (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) :
    (∫ x : ℝ in L..H, ∫ y : ℝ in x..H, f x y) =
      ∫ y : ℝ in L..H, ∫ x : ℝ in L..y, f x y := by
  classical
  let K := Icc L H
  let S := {p : ℝ × ℝ | p.1 ≤ p.2}
  let g : ℝ × ℝ → ℂ := S.indicator (Function.uncurry f)
  have hS : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hi : Integrable (Function.uncurry f)
      ((volume.restrict K).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hg : Integrable g ((volume.restrict K).prod (volume.restrict K)) := hi.indicator hS
  have hs := MeasureTheory.integral_integral_swap (f := fun x y => g (x,y)) hg
  have hleft (x : ℝ) (hx : x ∈ K) :
      (∫ y in K, g (x,y)) = ∫ y in x..H, f x y := by
    have hsection : (fun y => g (x,y)) = (Ici x).indicator (f x) := by
      funext y
      simp [g, S, indicator_apply]
    rw [hsection, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici x ∩ K = Icc x H := by
      ext y
      simp only [mem_inter_iff, mem_Ici, K, mem_Icc]
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · exact fun h => ⟨h.1,le_trans hx.1 h.1,h.2⟩
    rw [hset, intervalIntegral.integral_of_le hx.2, integral_Icc_eq_integral_Ioc]
  have hright (y : ℝ) (hy : y ∈ K) :
      (∫ x in K, g (x,y)) = ∫ x in L..y, f x y := by
    have hsection : (fun x => g (x,y)) = (Iic y).indicator (fun x => f x y) := by
      funext x
      simp [g, S, indicator_apply]
    rw [hsection, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic y ∩ K = Icc L y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, K, mem_Icc]
      constructor
      · exact fun h => ⟨h.2.1,h.1⟩
      · exact fun h => ⟨h.2,h.1,le_trans h.2 hy.2⟩
    rw [hset, intervalIntegral.integral_of_le hy.1, integral_Icc_eq_integral_Ioc]
  have hL : (∫ x in K, ∫ y in K, g (x,y)) =
      ∫ x in L..H, ∫ y in x..H, f x y := by
    rw [intervalIntegral.integral_of_le hH, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc hleft
  have hR : (∫ y in K, ∫ x in K, g (x,y)) =
      ∫ y in L..H, ∫ x in L..y, f x y := by
    rw [intervalIntegral.integral_of_le hH, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc hright
  exact hL.symm.trans (hs.trans hR)

theorem triangular_integral_swap (H : ℝ) (hH : 0 ≤ H)
    (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) :
    (∫ x : ℝ in 0..H, ∫ y : ℝ in x..H, f x y) =
      ∫ y : ℝ in 0..H, ∫ x : ℝ in 0..y, f x y :=
  triangular_integral_swap_from 0 H hH f hf

/-- Genuine radial slicing of a tetrahedron. This is two triangle Fubini steps,
followed by translation, and holds without distinctness assumptions on a kernel. -/
theorem radial_simplex_integral (H : ℝ) (hH : 0 ≤ H)
    (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    (∫ a in (0:ℝ)..H, ∫ x in (0:ℝ)..a, ∫ y in (0:ℝ)..a-x, f a x y) =
      ∫ x in (0:ℝ)..H, ∫ y in (0:ℝ)..H-x,
        ∫ w in (0:ℝ)..H-x-y, f (x+y+w) x y := by
  have hg : Continuous (Function.uncurry (fun x a : ℝ =>
      ∫ y in (0:ℝ)..a-x, f a x y)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · exact hf.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ =>
        (p.1.2,p.1.1,p.2)) by fun_prop)
    · fun_prop
  rw [← triangular_integral_swap H hH _ hg]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc 0 H := by simpa [Set.uIcc_of_le hH] using hx
  have hxH : x ≤ H := hx'.2
  have htrans (a : ℝ) :
      (∫ y in (0:ℝ)..a-x, f a x y) = ∫ b in x..a, f a x (b-x) := by
    convert intervalIntegral.integral_comp_add_right
      (fun b : ℝ => f a x (b-x)) (a := 0) (b := a-x) x using 1 <;> simp
  simp_rw [htrans]
  have hj : Continuous (Function.uncurry (fun b a : ℝ => f a x (b-x))) := by
    exact hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,x,p.1-x)) by fun_prop)
  rw [← triangular_integral_swap_from x H hxH _ hj]
  have hout := intervalIntegral.integral_comp_add_right
    (fun b : ℝ => ∫ a in b..H, f a x (b-x)) (a := 0) (b := H-x) x
  simp only [zero_add, sub_add_cancel] at hout
  rw [← hout]
  apply intervalIntegral.integral_congr
  intro y _
  have hin := intervalIntegral.integral_comp_add_right
    (fun a : ℝ => f a x y) (a := 0) (b := H-x-y) (x+y)
  have he : H-x-y+(x+y) = H := by ring
  simp only [zero_add, he] at hin
  simpa [add_comm, add_left_comm, add_assoc] using hin.symm

end Sechstmoment

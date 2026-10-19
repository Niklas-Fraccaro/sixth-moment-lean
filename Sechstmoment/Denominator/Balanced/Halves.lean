import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Sechstmoment.Certificate.Kernels.Balanced.PolytopeDensityBridge
import Sechstmoment.Denominator.Balanced.Geometry

/-! Genuine interval changes of variables for the balanced direct and dual
halves.  The free-edge interval from the sharp logarithmic cut becomes the
negative and positive halves of the original symmetric interval in (4.2).
This algebraic and measure-theoretic identity does not assert an AFE. -/

namespace Sechstmoment
open MeasureTheory
noncomputable section

/-- The same reflection identity applies to complex shifted generators,
before any polynomial differentiation. -/
theorem d02_reflected_halves_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Continuous f) (h : ℝ) :
    (∫ u in (0:ℝ)..h, f (u-h))+(∫ u in (0:ℝ)..h, f (h-u)) =
      ∫ x in -h..h, f x := by
  rw [intervalIntegral.integral_comp_sub_right f h,
    intervalIntegral.integral_comp_sub_left f h]
  simp only [zero_sub,sub_self,sub_zero]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-h) 0) (hf.intervalIntegrable 0 h)

def d02BalancedDirectHalf (p q : Fin 5 → ℝ) (delta h : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..h,
    evalDegreeFour p (delta-(u-h))*evalDegreeFour q (-delta-(u-h))

def d02BalancedDualHalf (p q : Fin 5 → ℝ) (delta h : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..h,
    evalDegreeFour p (delta-(h-u))*evalDegreeFour q (-delta-(h-u))

theorem d02BalancedDirectHalf_eq (p q : Fin 5 → ℝ) (delta h : ℝ) :
    d02BalancedDirectHalf p q delta h =
      ∫ x in -h..(0:ℝ), evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x) := by
  unfold d02BalancedDirectHalf
  simpa using intervalIntegral.integral_comp_sub_right
    (fun x => evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x))
    (a := (0:ℝ)) (b := h) h

theorem d02BalancedDualHalf_eq (p q : Fin 5 → ℝ) (delta h : ℝ) :
    d02BalancedDualHalf p q delta h =
      ∫ x in (0:ℝ)..h, evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x) := by
  unfold d02BalancedDualHalf
  simpa using intervalIntegral.integral_comp_sub_left
    (fun x => evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x))
    (a := (0:ℝ)) (b := h) h

/-- Reflection of the literal free edge fills the whole symmetric interval,
with its original Lebesgue normalization and polynomial signs. -/
theorem d02BalancedHalves_eq_inner (p q : Fin 5 → ℝ) (delta h : ℝ) :
    d02BalancedDirectHalf p q delta h+d02BalancedDualHalf p q delta h =
      denominatorRealInner p q delta h := by
  rw [d02BalancedDirectHalf_eq,d02BalancedDualHalf_eq]
  have hc : Continuous (fun x : ℝ =>
      evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x)) := by
    unfold evalDegreeFour
    fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-h) 0) (hc.intervalIntegrable 0 h)

def d02BalancedDirectSlice (p q : Fin 5 → ℝ) (a b c d : ℝ) (R : Fin 4 → ℝ) : ℝ :=
  ∫ u in (0:ℝ)..(d02BalancedWidth a b c d R/2),
    evalDegreeFour p (1/2-(d01RowColumnSums (d02BalancedEdges a b c d R u)).1 0)*
      evalDegreeFour q (1/2-(d01RowColumnSums (d02BalancedEdges a b c d R u)).2 0)

def d02BalancedDualSlice (p q : Fin 5 → ℝ) (a b c d : ℝ) (R : Fin 4 → ℝ) : ℝ :=
  ∫ u in (0:ℝ)..(d02BalancedWidth a b c d R/2),
    evalDegreeFour p ((d01RowColumnSums (d02BalancedEdges a b c d R u)).2 0-1/2)*
      evalDegreeFour q ((d01RowColumnSums (d02BalancedEdges a b c d R u)).1 0-1/2)

theorem d02BalancedDirectSlice_eq (p q : Fin 5 → ℝ) (a b c d : ℝ) (R : Fin 4 → ℝ) :
    d02BalancedDirectSlice p q a b c d R =
      d02BalancedDirectHalf p q (d02ProfileDelta a b c d)
        (d02BalancedWidth a b c d R/2) := by
  unfold d02BalancedDirectSlice d02BalancedDirectHalf
  apply intervalIntegral.integral_congr
  intro u _
  have h1 := congrArg Prod.fst (d02BalancedEdges_centered_arguments a b c d R u)
  have h2 := congrArg Prod.snd (d02BalancedEdges_centered_arguments a b c d R u)
  dsimp only [d02DirectCoordinate] at h1 h2
  dsimp only
  rw [h1,h2]

theorem d02BalancedDualSlice_eq (p q : Fin 5 → ℝ) (a b c d : ℝ) (R : Fin 4 → ℝ) :
    d02BalancedDualSlice p q a b c d R =
      d02BalancedDualHalf p q (d02ProfileDelta a b c d)
        (d02BalancedWidth a b c d R/2) := by
  unfold d02BalancedDualSlice d02BalancedDualHalf
  apply intervalIntegral.integral_congr
  intro u _
  have h1 := congrArg Prod.fst (d02BalancedEdges_dual_arguments a b c d R u)
  have h2 := congrArg Prod.snd (d02BalancedEdges_dual_arguments a b c d R u)
  dsimp only [d02DualCoordinate] at h1 h2
  dsimp only
  rw [h1,h2]

/-- Both original slice integrands use the actual row/column sum map. -/
theorem d02BalancedSlices_eq_inner (p q : Fin 5 → ℝ) (a b c d : ℝ) (R : Fin 4 → ℝ) :
    d02BalancedDirectSlice p q a b c d R+d02BalancedDualSlice p q a b c d R =
      denominatorRealInner p q (d02ProfileDelta a b c d)
        (d02BalancedWidth a b c d R/2) := by
  rw [d02BalancedDirectSlice_eq,d02BalancedDualSlice_eq,d02BalancedHalves_eq_inner]

/-- The slice geometry uses the same width as the independently defined
original denominator kernel. -/
theorem d02BalancedHalves_eq_kernel (p q : Fin 5 → ℝ) (a b c d : ℝ) :
    (∫ R in denominatorRegion a b c d,
      d02BalancedDirectHalf p q (d02ProfileDelta a b c d)
        (d02BalancedWidth a b c d R/2)+
      d02BalancedDualHalf p q (d02ProfileDelta a b c d)
        (d02BalancedWidth a b c d R/2)) =
      denominatorZeroKernel p q a b c d := by
  simp_rw [d02BalancedHalves_eq_inner]
  unfold denominatorZeroKernel
  apply setIntegral_congr_fun (denominatorRegion_closed a b c d).measurableSet
  intro R _
  dsimp only
  have hw : d02BalancedWidth a b c d R/2 =
      (1-a-b-c-d+2*(R 0+R 1+R 2+R 3))/2 := by
    unfold d02BalancedWidth d02ProfileSum d02InteriorSum
    ring
  rw [hw]
  rfl

end
end Sechstmoment

import Sechstmoment.Certificate.Kernels.Balanced.IntegerInnerBridge
import Sechstmoment.Certificate.Kernels.Balanced.Pieces

namespace Sechstmoment
open scoped BigOperators
open _root_.Sechstmoment.Finite

theorem scale_real_pos : (0 : ℝ) < (Finite.scale : ℝ) := by
  norm_num [Finite.scale, Finite.base]

theorem denominator_integer_width (A B C D t : Int) :
    (((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2 : Int) : ℝ) =
      ((Finite.scale : ℝ)-24*A-24*B-24*C-24*D+2*t)/2 := by
  have hi : (Finite.scale-24*A-24*B-24*C-24*D+2*t)/2*2 =
      Finite.scale-24*A-24*B-24*C-24*D+2*t := by
    apply Int.ediv_mul_cancel
    refine ⟨12*(Finite.base : Int)-12*A-12*B-12*C-12*D+t, ?_⟩
    unfold Finite.scale
    ring
  have hr : (((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2 : Int) : ℝ)*2 =
      (Finite.scale : ℝ)-24*A-24*B-24*C-24*D+2*t := by exact_mod_cast hi
  linarith

theorem denominator_integer_node (p q : List Int) (A B C D t : Int) :
    denominatorZeroIntegrand (fun k => (coef p k.val : ℝ))
      (fun k => (coef q k.val : ℝ))
      (24*A/(Finite.scale : ℝ)) (24*B/(Finite.scale : ℝ))
      (24*C/(Finite.scale : ℝ)) (24*D/(Finite.scale : ℝ))
      (t/(Finite.scale : ℝ)) =
      ((Finite.w6 t (24*A) (24*B) (24*C) (24*D)*
        integerInner p q (12*(A+B-C-D))
          ((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2) : Int) : ℝ)/
          (6*315*(Finite.scale : ℝ)^12) := by
  have hM : (Finite.scale : ℝ) ≠ 0 := ne_of_gt scale_real_pos
  have hd : (24*(A : ℝ)/(Finite.scale : ℝ)+24*B/(Finite.scale : ℝ)-
      24*C/(Finite.scale : ℝ)-24*D/(Finite.scale : ℝ))/2 =
      ((12*(A+B-C-D) : Int) : ℝ)/(Finite.scale : ℝ) := by
    push_cast
    field_simp
    ring
  have hh : (1-24*(A : ℝ)/(Finite.scale : ℝ)-24*B/(Finite.scale : ℝ)-
      24*C/(Finite.scale : ℝ)-24*D/(Finite.scale : ℝ)+2*((t : ℝ)/(Finite.scale : ℝ)))/2 =
      (((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2 : Int) : ℝ)/(Finite.scale : ℝ) := by
    rw [denominator_integer_width]
    field_simp
  have hw : realW6 ((t : ℝ)/(Finite.scale : ℝ))
      (24*A/(Finite.scale : ℝ)) (24*B/(Finite.scale : ℝ))
      (24*C/(Finite.scale : ℝ)) (24*D/(Finite.scale : ℝ)) =
      ((Finite.w6 t (24*A) (24*B) (24*C) (24*D) : Int) : ℝ)/(Finite.scale : ℝ)^3 := by
    convert realW6_homogeneous (t : ℝ) (24*A) (24*B) (24*C) (24*D)
      (Finite.scale : ℝ) scale_real_pos using 1
    rw [w6_integer_cast]
    push_cast
    rfl
  dsimp only [denominatorZeroIntegrand]
  rw [hw, hd, hh]
  have hi := integerInner_integral p q (12*(A+B-C-D))
    ((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2)
  simp only [neg_div] at hi
  change _ = denominatorRealInner (fun k => (coef p k.val : ℝ))
    (fun k => (coef q k.val : ℝ))
    (((12*(A+B-C-D) : Int) : ℝ)/(Finite.scale : ℝ))
    ((((Finite.scale-24*A-24*B-24*C-24*D+2*t)/2 : Int) : ℝ)/(Finite.scale : ℝ)) at hi
  rw [← hi]
  push_cast
  field_simp

end Sechstmoment

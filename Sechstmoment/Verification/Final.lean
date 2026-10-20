import Sechstmoment.Theorem

set_option warningAsError true

open MeasureTheory

example : DivisorProof.Watt41 → Sechstmoment.FullGoal :=
  Sechstmoment.fullProof

example : DivisorProof.Watt41 →
    (Multipliable (fun p : {n : ℕ // Nat.Prime n} =>
      Sechstmoment.eulerFactor (p.val : ℝ)) ∧ 0 < Sechstmoment.arithmeticFactor) ∧
    (((1077094746 / 26265625 : ℚ) : ℝ) : EReal) ≤
      Filter.liminf (fun T : ℝ =>
        (((∫ t in (0 : ℝ)..T, ‖riemannZeta ((1/2 : ℂ) + (t : ℂ)*Complex.I)‖^6) /
          ((Sechstmoment.arithmeticFactor / (Nat.factorial 9 : ℝ))*T*(Real.log T)^9) :
            ℝ) : EReal)) Filter.atTop :=
  Sechstmoment.fullProof

example : (41007 : ℚ) / 1000 < Sechstmoment.declaredBound :=
  Sechstmoment.declaredBound_gt_41007

#guard_msgs in
#print axioms Sechstmoment.fullProof

#print axioms Sechstmoment.fullProof

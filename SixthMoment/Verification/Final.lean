import SixthMoment.Theorem

set_option warningAsError true

open MeasureTheory

example : DivisorProof.Watt41 → SixthMoment.FullGoal :=
  SixthMoment.fullProof

example : DivisorProof.Watt41 →
    (Multipliable (fun p : {n : ℕ // Nat.Prime n} =>
      SixthMoment.eulerFactor (p.val : ℝ)) ∧ 0 < SixthMoment.arithmeticFactor) ∧
    (((1077094746 / 26265625 : ℚ) : ℝ) : EReal) ≤
      Filter.liminf (fun T : ℝ =>
        (((∫ t in (0 : ℝ)..T, ‖riemannZeta ((1/2 : ℂ) + (t : ℂ)*Complex.I)‖^6) /
          ((SixthMoment.arithmeticFactor / (Nat.factorial 9 : ℝ))*T*(Real.log T)^9) :
            ℝ) : EReal)) Filter.atTop :=
  SixthMoment.fullProof

example : (41007 : ℚ) / 1000 < SixthMoment.declaredBound :=
  SixthMoment.declaredBound_gt_41007

/--
info: 'SixthMoment.fullProof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SixthMoment.fullProof

#print axioms SixthMoment.fullProof

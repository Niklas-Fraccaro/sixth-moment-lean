import Sechstmoment.Numerator.U.Reconstruction.RectangularNearUnitExclusion
import Sechstmoment.Numerator.U.Separation.Frequency.LogFrequency

namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_global_log_one_add_lower {x : ℝ} (hx : -1<x) :
    min |x| 1/4≤|Real.log (1+x)| := by
  have hp : 0<1+x := by linarith
  by_cases hs : |x|≤1/2
  · have h := (phase_log_one_add_comparable hs).1
    have hm := min_le_left |x| 1
    nlinarith [abs_nonneg x]
  · have hlarge : 1/2< |x| := lt_of_not_ge hs
    have hm := min_le_right |x| 1
    by_cases h0 : 0≤x
    · rw [abs_of_nonneg h0] at hlarge
      have hl : (1/3:ℝ)≤Real.log (3/2) := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3/2)
        norm_num at h
        exact h
      have hc := Real.log_le_log (by norm_num : (0:ℝ)<3/2) (by linarith : (3/2:ℝ)≤1+x)
      have ha := le_abs_self (Real.log (1+x))
      linarith
    · have h0' : x≤0 := (lt_of_not_ge h0).le
      rw [abs_of_nonpos h0'] at hlarge
      have hl := Real.log_le_sub_one_of_pos hp
      have ha := neg_le_abs (Real.log (1+x))
      linarith

theorem phase_far_relative_gap_min_lower {P Q η : ℝ} (hP : 0<P) (hQ : 0<Q)
    (hη : 0≤η) (hη1 : η≤1)
    (hfar : η*Real.sqrt (P*Q)≤|P-Q|) :
    η/2≤min |P/Q-1| 1 := by
  have hne : Q≠0 := hQ.ne'
  have he : |P-Q|=|P/Q-1| *Q := by
    have hrat : P-Q=(P/Q-1)*Q := by field_simp
    rw [hrat,abs_mul,abs_of_pos hQ]
  apply le_min
  · by_cases hx : 1/2≤|P/Q-1|
    · linarith
    · have hx' : |P/Q-1|≤1/2 := (lt_of_not_ge hx).le
      have hratio : (1/2:ℝ)≤P/Q := by
        have hl := (abs_le.mp hx').1
        linarith
      have hPQ : Q/2≤P := by
        have h := (le_div_iff₀ hQ).mp hratio
        linarith
      have hroot : Q/2≤Real.sqrt (P*Q) := by
        have hsq := Real.sq_sqrt (mul_nonneg hP.le hQ.le)
        have hpq := mul_le_mul_of_nonneg_right hPQ hQ.le
        have hr := Real.sqrt_nonneg (P*Q)
        nlinarith
      have h := (mul_le_mul_of_nonneg_left hroot hη).trans hfar
      rw [he] at h
      exact (mul_le_mul_iff_right₀ hQ).mp (by nlinarith)
  · linarith

theorem phase_far_relative_gap_log_lower {P Q η : ℝ} (hP : 0<P) (hQ : 0<Q)
    (hη : 0≤η) (hη1 : η≤1)
    (hfar : η*Real.sqrt (P*Q)≤|P-Q|) :
    η/8≤|Real.log (P/Q)| := by
  have hx : -1<P/Q-1 := by have h := div_pos hP hQ; linarith
  have hlog := phase_global_log_one_add_lower hx
  rw [show 1+(P/Q-1)=P/Q by ring] at hlog
  have hg := phase_far_relative_gap_min_lower hP hQ hη hη1 hfar
  linarith

theorem phase_actual_source_far_log_lower (positive : Bool) (n : Fin 7 → ℕ)
    (hpos : ∀ j : Fin 6, 0<n j.castSucc)
    (hrel : signedQuadraticRelation positive n) {η : ℝ}
    (hη : 0≤η) (hη1 : η≤1)
    (hfar : η*Real.sqrt ((n 0:ℝ)*n 1*n 2*n 3*n 4*n 5)≤(n 6:ℝ)) :
    η/8≤|Real.log (rectangularNearLeftProduct n/rectangularNearRightProduct n)| := by
  have hP : 0<rectangularNearLeftProduct n := by
    unfold rectangularNearLeftProduct
    have h₀ := hpos 0
    have h₂ := hpos 2
    have h₃ := hpos 3
    exact mul_pos (mul_pos (by exact_mod_cast h₀) (by exact_mod_cast h₂)) (by exact_mod_cast h₃)
  have hQ : 0<rectangularNearRightProduct n := by
    unfold rectangularNearRightProduct
    have h₁ := hpos 1
    have h₄ := hpos 4
    have h₅ := hpos 5
    exact mul_pos (mul_pos (by exact_mod_cast h₁) (by exact_mod_cast h₄)) (by exact_mod_cast h₅)
  apply phase_far_relative_gap_log_lower hP hQ hη hη1
  rwa [rectangular_signed_relation_abs_gap positive n hrel,← rectangular_near_tuple_mass]

end
end Sechstmoment

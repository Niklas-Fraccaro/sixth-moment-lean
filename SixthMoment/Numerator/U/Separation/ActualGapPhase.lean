import SixthMoment.Numerator.U.Reconstruction.RectangularQuadraticReindex
import SixthMoment.Numerator.U.Separation.LogarithmicPhaseTruncation

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def rectangularTwistedQuadPhase (t : ℝ) (a b : ℕ) (n : Fin 4 → ℕ) : ℂ :=
  (((a*(n 0+1)*(n 1+1):ℕ):ℂ)/((b*(n 2+1)*(n 3+1):ℕ):ℂ))^(-(t:ℂ)*I)

def rectangularGapSign (positive : Bool) : ℝ := if positive then 1 else -1

def rectangularGapRatio (positive : Bool) (b h : ℕ) (n : Fin 4 → ℕ) : ℝ :=
  rectangularGapSign positive*(h:ℝ)/((b*(n 2+1)*(n 3+1):ℕ):ℝ)

theorem rectangular_amplifier_pair_exact_phase {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (t : ℝ) :
    ((a:ℂ)^criticalLinePoint t)⁻¹*((b:ℂ)^(1-criticalLinePoint t))⁻¹=
      (a:ℂ)^(-(1/2:ℂ))*(b:ℂ)^(-(1/2:ℂ))*((a:ℂ)/(b:ℂ))^(-(t:ℂ)*I) := by
  have ha0 : (a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb0 : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  unfold criticalLinePoint
  rw [← Complex.cpow_neg,← Complex.cpow_neg]
  have h₁ : -((1/2:ℂ)+(t:ℂ)*I)=-(1/2:ℂ)+(-(t:ℂ)*I) := by ring
  have h₂ : -(1-((1/2:ℂ)+(t:ℂ)*I))=-(1/2:ℂ)+(t:ℂ)*I := by ring
  rw [h₁,h₂,Complex.cpow_add _ _ ha0,Complex.cpow_add _ _ hb0,
    Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  have hh : (b:ℂ)^((t:ℂ)*I)=((b:ℂ)^(-(t:ℂ)*I))⁻¹ := by
    rw [← Complex.cpow_neg]
    congr 1
    ring
  rw [hh]
  ring

theorem rectangular_actual_pair_weight_oscillation (T : ℝ) (f g Φ : ℝ → ℝ)
    (u v : ℕ) (t : ℝ) (n : Fin 4 → ℕ) :
    rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n=
      (Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
        (g (Real.log (v+1:ℝ)/Real.log T):ℂ)*
        (u+1:ℂ)^(-(1/2:ℂ))*(v+1:ℂ)^(-(1/2:ℂ))*
        rectangularTwistedQuadPhase t (u+1) (v+1) n := by
  have h := rectangular_amplifier_pair_exact_phase
    (by positivity : 0<(u+1:ℝ)) (by positivity : 0<(v+1:ℝ)) t
  push_cast at h
  have hc : (((u+1:ℂ)/(v+1:ℂ))*
      ((((n 0+1)*(n 1+1):ℕ):ℂ)/(((n 2+1)*(n 3+1):ℕ):ℂ)))^(-(t:ℂ)*I)=
      ((u+1:ℂ)/(v+1:ℂ))^(-(t:ℂ)*I)*rectangularAFEOscillation t n := by
    have hd := Complex.mul_cpow_ofReal_nonneg
      (by positivity : 0≤(u+1:ℝ)/(v+1:ℝ))
      (by positivity : 0≤(((n 0+1)*(n 1+1):ℕ):ℝ)/(((n 2+1)*(n 3+1):ℕ):ℝ)) (-(t:ℂ)*I)
    simpa only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_natCast,
      Complex.ofReal_one,rectangularAFEOscillation] using hd
  have hr : (((u+1:ℂ)/(v+1:ℂ))*
      ((((n 0+1)*(n 1+1):ℕ):ℂ)/(((n 2+1)*(n 3+1):ℕ):ℂ)))^(-(t:ℂ)*I)=
      rectangularTwistedQuadPhase t (u+1) (v+1) n := by
    unfold rectangularTwistedQuadPhase
    push_cast
    congr 1
    have hv0 : (v+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero v
    have hn2 : (n 2+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero (n 2)
    have hn3 : (n 3+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero (n 3)
    field_simp [hv0,hn2,hn3]
  unfold rectangularMomentPairWeight
  simp only [div_eq_mul_inv]
  calc
    _ = ((Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
      (g (Real.log (v+1:ℝ)/Real.log T):ℂ))*
        (((u+1:ℂ)^criticalLinePoint t)⁻¹*((v+1:ℂ)^(1-criticalLinePoint t))⁻¹)*
          rectangularAFEOscillation t n := by ring
    _ = ((Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
      (g (Real.log (v+1:ℝ)/Real.log T):ℂ)*(u+1:ℂ)^(-(1/2:ℂ))*(v+1:ℂ)^(-(1/2:ℂ)))*
        (((u+1:ℂ)/(v+1:ℂ))^(-(t:ℂ)*I)*rectangularAFEOscillation t n) := by rw [h]; ring
    _ = _ := by rw [← hc,hr]; simp only [div_eq_mul_inv]

theorem rectangular_actual_signed_gap_phase (positive : Bool) (a b : ℕ)
    (hb : 0<b) (t : ℝ) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n else rectangularNegativeQuadGap a b n) :
    rectangularTwistedQuadPhase t a b n=
      (1+(rectangularGapRatio positive b (rectangularAFEGap positive a b n) n:ℂ))^(-(t:ℂ)*I) := by
  have hs := rectangular_AFE_gap_source_relation positive a b n hn
  have hden : ((b*(n 2+1)*(n 3+1):ℕ):ℂ)≠0 := by
    exact_mod_cast Nat.ne_of_gt (by positivity : 0<b*(n 2+1)*(n 3+1))
  unfold rectangularTwistedQuadPhase
  congr 1
  have hr : (a:ℂ)*(n 0+1)*(n 1+1)-(b:ℂ)*(n 2+1)*(n 3+1)=
      (rectangularGapSign positive:ℂ)*(rectangularAFEGap positive a b n:ℂ) := by
    cases positive <;> simp [signedQuadraticRelation,rectangularAFESourceTuple,rectangularGapSign] at hs ⊢
    all_goals exact_mod_cast hs
  unfold rectangularGapRatio
  push_cast
  push_cast at hden
  rw [show (a:ℂ)*(n 0+1)*(n 1+1)=(b:ℂ)*(n 2+1)*(n 3+1)+
    (rectangularGapSign positive:ℂ)*(rectangularAFEGap positive a b n:ℂ) by linear_combination hr,
    add_div,div_self hden]

end
end SixthMoment

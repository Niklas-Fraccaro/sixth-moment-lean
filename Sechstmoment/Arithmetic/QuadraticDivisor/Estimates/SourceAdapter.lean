import Mathlib.Tactic
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.Errors
import Sechstmoment.Arithmetic.QuadraticDivisor.Input


namespace Sechstmoment

open Source

theorem rectangular_source_majorant_le (q : Source.QuadraticScales) {X : ℝ}
    (hA : 0 ≤ q.A) (hB : 0 ≤ q.B) (_hX : 0 ≤ X) (hH : 0 ≤ q.H)
    (hmass : q.mass = q.A*q.B*X^2) :
    Source.orientedQuadraticMajorant q ≤ 2*rectangularQuadraticMajorant q.A q.B X q.H := by
  have hlarge := rectangular_oriented_coefficient_le hA hB
  have hsmall := rectangular_small_d_coefficient_le hA hB
  have hc := add_le_add hlarge hsmall
  have hp : 0 ≤ q.H^(1/4:ℝ)*(q.A*q.B*X^2)^(1/8:ℝ) := by positivity
  have hpref : 0 ≤ (q.A*q.B*X^2*q.H^2)^(1/4:ℝ) := by positivity
  dsimp [Source.orientedQuadraticMajorant, rectangularQuadraticMajorant]
  rw [hmass]
  calc
    _ = (q.A*q.B*X^2*q.H^2)^(1/4:ℝ)*
      (2*(q.A*q.B)+(q.H^(1/4:ℝ)*(q.A*q.B*X^2)^(1/8:ℝ))*
        (q.A^(3/8:ℝ)*q.B^(1/8:ℝ)+(q.A*q.B)^(1/4:ℝ))) := by ring
    _ ≤ (q.A*q.B*X^2*q.H^2)^(1/4:ℝ)*
      (2*(q.A*q.B)+(q.H^(1/4:ℝ)*(q.A*q.B*X^2)^(1/8:ℝ))*
        ((q.A*q.B)^(1/8:ℝ)*max q.A q.B^(1/4:ℝ)+
          (q.A*q.B)^(1/8:ℝ)*max q.A q.B^(1/4:ℝ))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hc hp) _) hpref
    _ = _ := by ring

theorem rectangular_source_mass_power_le {mass D T r ε : ℝ}
    (hmass : 0 ≤ mass) (hD : 0 ≤ D) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hgrowth : mass ≤ D*T^r) : mass^ε ≤ D^ε*T^(r*ε) := by
  have hp := Real.rpow_le_rpow hmass hgrowth hε
  rw [Real.mul_rpow hD (Real.rpow_nonneg hT r), ← Real.rpow_mul hT] at hp
  exact hp

theorem rectangular_signed_source_discrepancy_bound
    (positive : Bool) (q : Source.QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) {X C D T r ε : ℝ}
    (hA : 0 ≤ q.A) (hB : 0 ≤ q.B) (hX : 0 ≤ X) (hH : 0 ≤ q.H)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hmass : q.mass = q.A*q.B*X^2)
    (hgrowth : q.mass ≤ D*T^r) (hgrowthH : q.mass*q.H^2 ≤ D*T^r)
    (hsource : ‖Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
      C*((q.mass*q.H^2)^ε*Source.orientedQuadraticMajorant q+q.mass^ε*q.H^2)) :
    ‖Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
      C*(D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2) := by
  have hm : 0 ≤ q.mass := by rw [hmass]; positivity
  have hp₁ := rectangular_source_mass_power_le (mul_nonneg hm (sq_nonneg _)) hD hT hε hgrowthH
  have hp₂ := rectangular_source_mass_power_le hm hD hT hε hgrowth
  have hmaj := rectangular_source_majorant_le q hA hB hX hH hmass
  calc
    _ ≤ C*((D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H)+
        (D^ε*T^(r*ε))*q.H^2) := hsource.trans (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul hp₁ hmaj (by dsimp [Source.orientedQuadraticMajorant]; positivity) (by positivity))
            (mul_le_mul_of_nonneg_right hp₂ (sq_nonneg _))) hC)
    _ = _ := by ring

theorem rectangular_BBLRv1_source_adapter (hinput : Source.SeparatedQuadraticInput)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Source.QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), Source.QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β W →
      ∀ positive : Bool, ∀ X D T r : ℝ,
      0 ≤ X → 0 ≤ D → 0 ≤ T → q.mass = q.A*q.B*X^2 →
      q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      ‖Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
        C*(D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2) := by
  obtain ⟨C, hC, hc⟩ := hinput ε hε δ hδ K hK bounds hbounds
  refine ⟨C, hC, ?_⟩
  intro q α β W hq positive X D T r hX hD hT hmass hgrowth hgrowthH
  have hA : 0 ≤ q.A := le_trans (by norm_num) (hq.1 0)
  have hB : 0 ≤ q.B := le_trans (by norm_num) (hq.1 1)
  have hH : 0 ≤ q.H := le_trans (by norm_num) (hq.1 6)
  exact rectangular_signed_source_discrepancy_bound positive q α β W hA hB hX hH hC hD hT
    hε.le hmass hgrowth hgrowthH (hc q α β W hq positive)

theorem rectangular_actual_signed_transfer
    (positive : Bool) (q : Source.QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) {X C D T r ε K : ℝ}
    (hA : 0 < q.A) (hB : 0 < q.B) (hX : 0 < X) (hH : 0 < q.H)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 < T) (hε : 0 ≤ ε) (hK : 0 < K)
    (hmass : q.mass = q.A*q.B*X^2)
    (hgrowth : q.mass ≤ D*T^r) (hgrowthH : q.mass*q.H^2 ≤ D*T^r)
    (hH0 : q.H ≤ K*(q.A*q.B)^(1/2:ℝ)*X/T)
    (hsource : ‖Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
      C*((q.mass*q.H^2)^ε*Source.orientedQuadraticMajorant q+q.mass^ε*q.H^2)) :
    ‖((T/((q.A*q.B)^(1/2:ℝ)*X) : ℝ) : ℂ)*
      Source.signedQuadraticDiscrepancy positive q α β W‖ ≤
      C*(D^ε*T^(r*ε))*
        (2*(K^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)+
          K^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*max q.A q.B^(1/4:ℝ)*X^(1/2:ℝ))+
          K^2*(q.A*q.B)^(1/2:ℝ)*X/T) := by
  have he := rectangular_signed_source_discrepancy_bound positive q α β W hA.le hB.le
    hX.le hH.le hC hD hT.le hε hmass hgrowth hgrowthH hsource
  have hw : 0 ≤ T/((q.A*q.B)^(1/2:ℝ)*X) := by positivity
  have hz : 0 ≤ C*(D^ε*T^(r*ε)) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ T/((q.A*q.B)^(1/2:ℝ)*X)*
      (C*(D^ε*T^(r*ε))*(2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2)) :=
      mul_le_mul_of_nonneg_left he hw
    _ = (C*(D^ε*T^(r*ε)))*
      (2*(T/((q.A*q.B)^(1/2:ℝ)*X)*rectangularQuadraticMajorant q.A q.B X q.H)+
        T/((q.A*q.B)^(1/2:ℝ)*X)*q.H^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (rectangular_H0_back_transfer hT hA hB hX hH hK hH0) (by norm_num))
      (rectangular_poisson_back_transfer hT (mul_pos hA hB) hX hH.le hK hH0)) hz

end Sechstmoment

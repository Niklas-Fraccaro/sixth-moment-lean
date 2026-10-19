import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ResidualVertical

/-! Genuine full x/s/time and original finite amplifier aggregation of
the literal three ratio-contour remainders. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioActualAmplifierCoefficient (T : ℝ) (f : ℝ→ℝ) (n : ℕ) : ℂ :=
  (f (Real.log n/Real.log T):ℂ)

theorem a03ZeroModeRatioPrimitiveResidualPower_eq_three (g a b : ℕ) (η : ℝ) :
    a03ZeroModeRatioPrimitiveResidualPower g a b η=
      (g:ℝ)^(-1:ℝ)*(a:ℝ)^((1/2+η)-1)*(b:ℝ)^((1/2+η)-1)+
      (g:ℝ)^(-1:ℝ)*(a:ℝ)^((1/4+η)-1)*(b:ℝ)^((3/4+η)-1)+
      (g:ℝ)^(-1:ℝ)*(a:ℝ)^((3/4+η)-1)*(b:ℝ)^((1/4+η)-1) := by
  norm_num [a03ZeroModeRatioPrimitiveResidualPower,a03ZeroModeRatioResidualAmplifierLeftExponent,
    a03ZeroModeRatioResidualAmplifierRightExponent,Fin.sum_univ_succ]
  ring

theorem a03ZeroModeRatioPrimitiveResidualProfileMass_eq_original
    (T a b η : ℝ) (f g : ℝ→ℝ) :
    (∑ d∈Finset.Icc 1 (min ⌊T^a⌋₊ ⌊T^b⌋₊),∑ m∈Finset.Icc 1 (⌊T^a⌋₊/d),∑ n∈Finset.Icc 1 (⌊T^b⌋₊/d),
      if m.Coprime n then
        ‖a03ZeroModeRatioActualAmplifierCoefficient T f (d*m)‖*
          ‖a03ZeroModeRatioActualAmplifierCoefficient T g (d*n)‖*
            a03ZeroModeRatioPrimitiveResidualPower d m n η else 0)=
      a03ZeroModeRatioResidualAmplifierMass T a b f g η := by
  have hp (d m n : ℕ) :
      ‖a03ZeroModeRatioActualAmplifierCoefficient T f (d*m)‖*
        ‖a03ZeroModeRatioActualAmplifierCoefficient T g (d*n)‖*
          a03ZeroModeRatioPrimitiveResidualPower d m n η=
      ‖f (Real.log (d*m:ℕ)/Real.log T)‖*‖g (Real.log (d*n:ℕ)/Real.log T)‖*
        (d:ℝ)^(-1:ℝ)*(m:ℝ)^((1/2+η)-1)*(n:ℝ)^((1/2+η)-1)+
      ‖f (Real.log (d*m:ℕ)/Real.log T)‖*‖g (Real.log (d*n:ℕ)/Real.log T)‖*
        (d:ℝ)^(-1:ℝ)*(m:ℝ)^((1/4+η)-1)*(n:ℝ)^((3/4+η)-1)+
      ‖f (Real.log (d*m:ℕ)/Real.log T)‖*‖g (Real.log (d*n:ℕ)/Real.log T)‖*
        (d:ℝ)^(-1:ℝ)*(m:ℝ)^((3/4+η)-1)*(n:ℝ)^((1/4+η)-1) := by
    rw [a03ZeroModeRatioPrimitiveResidualPower_eq_three]
    simp only [a03ZeroModeRatioActualAmplifierCoefficient,Complex.norm_real]
    ring
  have hite (p : Prop) [Decidable p] (X Y Z : ℝ) :
      (if p then X+Y+Z else 0)=(if p then X else 0)+(if p then Y else 0)+(if p then Z else 0) := by
    split_ifs <;> ring
  simp_rw [hp,hite,Finset.sum_add_distrib]
  unfold a03ZeroModeRatioResidualAmplifierMass
  rw [←a03ZeroModeRatioPrimitiveProfilePowerMass_eq_original T a b f g (1/2+η) (1/2+η),
    ←a03ZeroModeRatioPrimitiveProfilePowerMass_eq_original T a b f g (1/4+η) (3/4+η),
    ←a03ZeroModeRatioPrimitiveProfilePowerMass_eq_original T a b f g (3/4+η) (1/4+η)]
  rfl

theorem a03ZeroModeGCDEtaResidual_chambers_uniform_full_amplifier_bound
    (K : Set MomentShifts) (hK : IsCompact K) {κ η a b : ℝ}
    (hκ : 0<κ) (hη : 0<η) (hη1 : η≤1/16)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g : ℝ→ℝ) {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,
      ‖a03ZeroModeGCDEtaResidual Φ T σ (η/4)
        (rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
          (a03ZeroModeRatioActualAmplifierCoefficient T g)‖≤
        C*(Real.log T)^56*T^(1/2+η)*a03ZeroModeRatioResidualAmplifierMass T a b f g η := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeGCDEtaResidual_chambers_uniform_vertical_bound K hK hκ hη hη1 hroot hΦ hSupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with T hbnd hT
  intro σ hσ dual m n
  let α := rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ)
  let A := a03ZeroModeRatioActualAmplifierCoefficient T f
  let B := a03ZeroModeRatioActualAmplifierCoefficient T g
  let Q : ℝ := C*(Real.log T)^56*T^(1/2+η)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  unfold a03ZeroModeGCDEtaResidual
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  calc
    _≤∑ d∈Finset.Icc 1 (min ⌊T^a⌋₊ ⌊T^b⌋₊),
      ∑ u∈Finset.Icc 1 (⌊T^a⌋₊/d),∑ v∈Finset.Icc 1 (⌊T^b⌋₊/d),
      ‖if u.Coprime v then (T:ℂ)*verticalIntegral (1+η/4)
        (a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α d u v A B) else 0‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro d _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro u _
        exact norm_sum_le _ _
    _≤∑ d∈Finset.Icc 1 (min ⌊T^a⌋₊ ⌊T^b⌋₊),
      ∑ u∈Finset.Icc 1 (⌊T^a⌋₊/d),∑ v∈Finset.Icc 1 (⌊T^b⌋₊/d),
      Q*(if u.Coprime v then ‖A (d*u)‖*‖B (d*v)‖*
        a03ZeroModeRatioPrimitiveResidualPower d u v η else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        by_cases hcop : u.Coprime v
        · rw [ite_eq_left hcop,ite_eq_left hcop]
          have hd0 : 0<d := by have hh := (Finset.mem_Icc.mp hd).1; omega
          have hu0 : 0<u := by have hh := (Finset.mem_Icc.mp hu).1; omega
          have hv0 : 0<v := by have hh := (Finset.mem_Icc.mp hv).1; omega
          exact (hbnd σ hσ dual m n d u v hd0 hu0 hv0 A B).2.trans_eq (by dsimp [Q]; ring)
        · simp [hcop]
    _=Q*a03ZeroModeRatioResidualAmplifierMass T a b f g η := by
      simp only [←Finset.mul_sum]
      rw [a03ZeroModeRatioPrimitiveResidualProfileMass_eq_original]

theorem a03ZeroModeGCDEtaResidual_chambers_uniform_oT
    (K : Set MomentShifts) (hK : IsCompact K) {κ a b : ℝ}
    (hκ : 0<κ) (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∀ d : ℝ,0<d → ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,
      ‖a03ZeroModeGCDEtaResidual Φ T σ (rectangularSlack a b/4)
        (rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
          (a03ZeroModeRatioActualAmplifierCoefficient T g)‖≤d*T := by
  obtain ⟨hη,hη1,_hexp⟩ := a03ZeroModeRatioResidualAmplifier_exponent_lt_one ha hab hlen
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeGCDEtaResidual_chambers_uniform_full_amplifier_bound K hK hκ hη hη1 hroot f g hΦ hSupp
  have hsmall := (a03ZeroModeRatioResidualAmplifierMass_isLittleO ha hab hlen f g hf hg 56).const_mul_left C
  intro d hd
  filter_upwards [hbound,isLittleO_iff.mp hsmall hd,eventually_ge_atTop (1:ℝ)] with T hbnd hsmall hT
  intro σ hσ dual m n
  apply (hbnd σ hσ dual m n).trans
  have hmajor : 0≤C*(Real.log T)^56*T^(1/2+rectangularSlack a b)*
      a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b) := by
    exact mul_nonneg (by positivity) (a03ZeroModeRatioResidualAmplifierMass_nonneg _ _ _ _ _ _)
  have hnorm : ‖C*((Real.log T)^56*T^(1/2+rectangularSlack a b)*
      a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b))‖=
      C*(Real.log T)^56*T^(1/2+rectangularSlack a b)*
        a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b) := by
    rw [show C*((Real.log T)^56*T^(1/2+rectangularSlack a b)*
      a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b))=
      C*(Real.log T)^56*T^(1/2+rectangularSlack a b)*
        a03ZeroModeRatioResidualAmplifierMass T a b f g (rectangularSlack a b) by ring,
      Real.norm_of_nonneg hmajor]
  simpa only [hnorm,Real.norm_of_nonneg (zero_le_one.trans hT)] using hsmall

end
end Sechstmoment.Source

import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.AbsoluteConvergence
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.CountableReindex
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.InitialEtaJoin
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.InitialProductFront
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.PhysicalInverse

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03UnrestrictedRatioGCDVStarIntegrand_eq_physicalSignDensity
    (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (u v m n h : ℕ) (x : ℝ)
    (hWeight : ∀ z : ℂ,a03ZeroModeRatioWeight α z=a03ZeroModeRatioWeight (rawMomentShifts T σ) z) :
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h x=
      a03ZeroModeGCDPhysicalSignDensity positive (a03RatioLeadingBranchProfile dual Φ T σ) T σ α
        (u+1) (v+1) (m+1) (n+1) (h+1)
        (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g) x := by
  have hfun : a03ZeroModeRatioWeight (rawMomentShifts T σ)=a03ZeroModeRatioWeight α :=
    funext (fun z => (hWeight z).symm)
  unfold a03UnrestrictedRatioGCDVStarIntegrand a03ZeroModeGCDPhysicalSignDensity
    a03ZeroModeGCDPhysicalCoefficient a03ZeroModeRatioActualAmplifierCoefficient
  simp only [hfun]
  ring

theorem a03UnrestrictedRatioGCDVStarTerm_signsum_eq_initial_product
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8) (f g : ℝ→ℝ)
    (dual : Bool) (u v m n h : ℕ)
    (hWeight : ∀ z : ℂ,a03ZeroModeRatioWeight α z=a03ZeroModeRatioWeight (rawMomentShifts T σ) z)
    (hNative : ∀ positive : Bool,IntegrableOn
      (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h) (Ioi 0)) :
    (∑positive : Bool,a03UnrestrictedRatioGCDVStarTerm dual positive Φ T σ α f g u v m n h)=
      2*(1/(2*Real.pi):ℂ)^3*∫p : A03GCDMellinCoordinates,
        a03ZeroModeGCDInitialMNHKernel (a03RatioLeadingBranchProfile dual Φ T σ) T σ α (u+1) (v+1)
          (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
          p.1 (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ((m+1,n+1),h+1)
        ∂a03GCDMellinMeasure := by
  have hΨ := a03RatioLeadingBranchProfile_contDiff hΦ hSupp hT σ dual
  have hΨs := (a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp
  have hJoint := a03ZeroModeGCDInitialMNHKernel_joint_integrable hΨ hΨs hT hε hε1 σ α hα
    (Nat.succ_pos u) (Nat.succ_pos v)
    (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
    ((m+1,n+1),h+1)
  unfold a03UnrestrictedRatioGCDVStarTerm
  rw [←integral_finsetSum _ (fun positive _ => hNative positive)]
  have hPoint (x : ℝ) (hx : 0<x) :
      (∑positive : Bool,a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h x)=
      2*(1/(2*Real.pi):ℂ)^3*∫q : ℝ×(ℝ×ℝ),
        a03ZeroModeGCDInitialMNHKernel (a03RatioLeadingBranchProfile dual Φ T σ) T σ α (u+1) (v+1)
          (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
          x ((ε:ℂ)+(q.1:ℂ)*I) ((ε:ℂ)+(q.2.1:ℂ)*I) (((1+ε:ℝ):ℂ)+(q.2.2:ℂ)*I) ((m+1,n+1),h+1)
        ∂(volume.prod (volume.prod volume)) := by
    simp_rw [a03UnrestrictedRatioGCDVStarIntegrand_eq_physicalSignDensity dual _ Φ T σ α f g u v m n h x hWeight]
    rw [a03ZeroModeGCDPhysicalSigns_eq_cosineDensity]
    exact a03ZeroModeGCDPhysicalCosineDensity_eq_initial_product hΨ hΨs hT hε σ α
      (Nat.succ_pos u) (Nat.succ_pos v) (Nat.succ_pos m) (Nat.succ_pos n) (Nat.succ_pos h)
      (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g) hx
  rw [setIntegral_congr_fun measurableSet_Ioi hPoint,integral_const_mul]
  congr 1
  exact (integral_prod _ hJoint).symm

private theorem nativeTriple_tsum {F : ((ℕ×ℕ)×ℕ)→ℂ} (hF : Summable F) :
    (∑'p : (ℕ×ℕ)×ℕ,F p)=∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,F ((m,n),h) := by
  rw [hF.tsum_prod,hF.prod.tsum_prod]

theorem a03UnrestrictedRatioGCDVStarTerm_signsum_tsum_eq_initialBlock
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8) (f g : ℝ→ℝ)
    (dual : Bool) (u v : ℕ)
    (hWeight : ∀ z : ℂ,a03ZeroModeRatioWeight α z=a03ZeroModeRatioWeight (rawMomentShifts T σ) z)
    (hNative : ∀ positive : Bool,
      (∀ p : (ℕ×ℕ)×ℕ,IntegrableOn
        (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2) (Ioi 0)) ∧
      Summable (fun p : (ℕ×ℕ)×ℕ => a03UnrestrictedRatioGCDVStarTerm dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2)) :
    (∑positive : Bool,∑'m : ℕ,∑'n : ℕ,∑'h : ℕ,
      a03UnrestrictedRatioGCDVStarTerm dual positive Φ T σ α f g u v m n h)=
      2*verticalIntegral (1+ε) (fun s => a03ZeroModeRatioDoubleIntegral ε ε (fun U V =>
        ∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialKernel (a03RatioLeadingBranchProfile dual Φ T σ) T σ α (u+1) (v+1)
          (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g) x U V s)) := by
  have hΨ := a03RatioLeadingBranchProfile_contDiff hΦ hSupp hT σ dual
  have hΨs := (a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp
  have htr (positive : Bool) := nativeTriple_tsum (hNative positive).2
  simp_rw [←htr]
  rw [Fintype.sum_bool,←(hNative true).2.tsum_add (hNative false).2]
  have hPair (p : (ℕ×ℕ)×ℕ) :
      a03UnrestrictedRatioGCDVStarTerm dual true Φ T σ α f g u v p.1.1 p.1.2 p.2+
        a03UnrestrictedRatioGCDVStarTerm dual false Φ T σ α f g u v p.1.1 p.1.2 p.2=
      2*(1/(2*Real.pi):ℂ)^3*∫q : A03GCDMellinCoordinates,
        a03ZeroModeGCDInitialMNHKernel (a03RatioLeadingBranchProfile dual Φ T σ) T σ α (u+1) (v+1)
          (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
          q.1 (a03GCDMellinU ε q) (a03GCDMellinV ε q) (a03GCDMellinS ε q) ((p.1.1+1,p.1.2+1),p.2+1)
        ∂a03GCDMellinMeasure := by
    simpa only [Fintype.sum_bool] using a03UnrestrictedRatioGCDVStarTerm_signsum_eq_initial_product
      hΦ hSupp hT hε hε1 σ α hα f g dual u v p.1.1 p.1.2 p.2 hWeight
      (fun positive => (hNative positive).1 p)
  simp_rw [hPair]
  rw [tsum_mul_left,a03ZeroModeGCDInitialMNHKernel_shifted_integral_tsum hΨ hΨs hT hε hε1
    σ α hα (Nat.succ_pos u) (Nat.succ_pos v)]
  rw [mul_assoc,a03ZeroModeGCDInitialKernel_product_eq_initialBlock hΨ hΨs hT hε hε1
    σ α hα (Nat.succ_pos u) (Nat.succ_pos v)]

private theorem nativeAmplifierRange_eq_Icc (N : ℕ) (F : ℕ→ℂ) :
    (∑u∈Finset.range N,F (u+1))=∑a∈Finset.Icc 1 N,F a := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

theorem a03ActualUnrestrictedRatioGCDVStar_chambers_eventually_eq_etaFront
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ ε : ℝ} (hκ : 0<κ)
    (hε : 0<ε) (hε1 : ε<1/8) (f g : ℝ→ℝ) (a b : ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ dual m n : Bool,
      let α := rawMomentShifts T (a03SourceNormalizedChamber dual m n σ)
      a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ α f g=
        2*(T:ℂ)*a03ZeroModeGCDEtaFront (a03RatioLeadingBranchProfile dual Φ T σ) T σ α
          ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
          (a03ZeroModeRatioActualAmplifierCoefficient T g) ε ε (1+ε) := by
  let W := a03SourceNormalizedChambersCompactSet K
  have hW := a03SourceNormalizedChambersCompactSet_isCompact K hK
  filter_upwards [a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g,
    compactNormalizedShifts_eventually_norm_small W hW (ε/8) (by positivity),
    eventually_gt_atTop (1:ℝ)] with T hNative hsmall hT
  intro σ hσ hroot dual m n
  dsimp only []
  let α := rawMomentShifts T (a03SourceNormalizedChamber dual m n σ)
  have hmem : a03SourceNormalizedChamber dual m n σ∈W :=
    mem_iUnion.mpr ⟨(dual,(m,n)),⟨σ,hσ,rfl⟩⟩
  have hα : ∀ j : Fin 4,‖α j‖≤ε/8 := hsmall _ hmem
  have hα1 : ∀ j : Fin 4,‖α j‖≤1/4 := fun j => (hα j).trans (by linarith)
  have hWeight (z : ℂ) : a03ZeroModeRatioWeight α z=a03ZeroModeRatioWeight (rawMomentShifts T σ) z := by
    dsimp only [α]
    rw [a03SourceNormalizedChamber_raw,a03ZeroModeRatioWeight_chamber]
    cases dual
    · rfl
    · exact a03ZeroModeRatioWeight_dual _ _
  have hrootτ := a03NormalizedPureRoot_gap_chambers σ hroot dual m n
  have hpure (k : PurePolarIndex) : purePolarRoot T (a03SourceNormalizedChamber dual m n σ) k≠0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hrootτ k)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  have hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0 := by
    intro j
    dsimp only [α]
    fin_cases j
    · change a03ZeroModeRatioRoot (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ)) 0≠0
      rw [a03ZeroModeRatioRoot_zero_eq_pure]
      exact neg_ne_zero.mpr (hpure _)
    · change a03ZeroModeRatioRoot (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ)) 1≠0
      rw [a03ZeroModeRatioRoot_one_eq_pure]
      exact neg_ne_zero.mpr (hpure _)
  have hRow (u v : ℕ) := a03UnrestrictedRatioGCDVStarTerm_signsum_tsum_eq_initialBlock hΦ hSupp
    (zero_lt_one.trans hT) hε hε1 σ α hα f g dual u v hWeight (fun positive =>
      ⟨(hNative σ hσ hroot α hα1 dual positive u v).1,
        (hNative σ hσ hroot α hα1 dual positive u v).2.2.1⟩)
  have hInitial : a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ α f g=
      2*(T:ℂ)*a03ZeroModeGCDInitialFront (a03RatioLeadingBranchProfile dual Φ T σ) T σ α
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g) ε ε (1+ε) := by
    let F : ℕ→ℕ→ℂ := fun u v => verticalIntegral (1+ε) (fun s => a03ZeroModeRatioDoubleIntegral ε ε (fun U V =>
      ∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialKernel (a03RatioLeadingBranchProfile dual Φ T σ) T σ α u v
        (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g) x U V s))
    have hRange : (∑u∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,F (u+1) (v+1))=
        ∑u∈Finset.Icc 1 ⌊T^a⌋₊,∑v∈Finset.Icc 1 ⌊T^b⌋₊,F u v := by
      rw [nativeAmplifierRange_eq_Icc ⌊T^a⌋₊ (fun u => ∑v∈Finset.range ⌊T^b⌋₊,F u (v+1))]
      apply Finset.sum_congr rfl
      intro u _
      exact nativeAmplifierRange_eq_Icc _ _
    unfold a03ActualUnrestrictedRatioGCDVStar a03ZeroModeGCDInitialFront
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range ⌊T^b⌋₊)]
    simp_rw [hRow]
    change (T:ℂ)*(∑u∈Finset.range ⌊T^a⌋₊,∑v∈Finset.range ⌊T^b⌋₊,2*F (u+1) (v+1))=
      2*(T:ℂ)*(∑u∈Finset.Icc 1 ⌊T^a⌋₊,∑v∈Finset.Icc 1 ⌊T^b⌋₊,F u v)
    have hInner (u : ℕ) := (Finset.mul_sum (Finset.range ⌊T^b⌋₊) (fun v => F (u+1) (v+1)) (2:ℂ)).symm
    simp_rw [hInner]
    rw [←Finset.mul_sum (Finset.range ⌊T^a⌋₊) (fun u => ∑v∈Finset.range ⌊T^b⌋₊,F (u+1) (v+1)) (2:ℂ),hRange]
    clear_value F
    ring
  rw [hInitial,a03ZeroModeGCDInitialFront_eq_etaFront _ _ _ _ _ _ _ _ hε hα hρ]

theorem a03ActualEightUnrestrictedRatioGCDVStar_eventually_eq_etaFront
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ ε : ℝ} (hκ : 0<κ)
    (hε : 0<ε) (hε1 : ε<1/8) (f g : ℝ→ℝ) (a b : ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,(∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      (∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual Φ T a b σ f g)=
        2*(T:ℂ)*∑dual : Bool,∑m : Bool,∑n : Bool,
          a03ZeroModeGCDEtaFront (a03RatioLeadingBranchProfile dual Φ T σ) T σ
            (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ))
            ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
            (a03ZeroModeRatioActualAmplifierCoefficient T g) ε ε (1+ε) := by
  filter_upwards [a03ActualUnrestrictedRatioGCDVStar_chambers_eventually_eq_etaFront
    hΦ hSupp K hK hκ hε hε1 f g a b] with T hT
  intro σ hσ hroot
  have hOne (dual m n : Bool) :
      a03ActualUnrestrictedRatioGCDVStar dual Φ T a b σ
        (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g=
      2*(T:ℂ)*a03ZeroModeGCDEtaFront (a03RatioLeadingBranchProfile dual Φ T σ) T σ
        (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) ⌊T^a⌋₊ ⌊T^b⌋₊
        (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
        ε ε (1+ε) := by
    simpa only [a03SourceNormalizedChamber_raw,a03SourceShifts] using hT σ hσ hroot dual m n
  unfold a03ActualFourUnrestrictedRatioGCDVStar
  simp_rw [hOne]
  simp only [Finset.mul_sum]

end
end Sechstmoment

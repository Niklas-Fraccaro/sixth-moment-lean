import SixthMoment.Numerator.U.ZeroModes.GCDMellin.ActualBranchResidualVertical
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.EtaFrontConvergence
import SixthMoment.Numerator.U.ZeroModes.MainXMellinJoin

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 1000000

private theorem etaVerticalIntegral_finsetSum {ι : Type*} [DecidableEq ι]
    (c : ℝ) (S : Finset ι) (F : ι→ℂ→ℂ)
    (hF : ∀ i∈S,Integrable (fun y : ℝ => F i ((c:ℂ)+(y:ℂ)*I))) :
    verticalIntegral c (fun s => ∑i∈S,F i s)=∑i∈S,verticalIntegral c (F i) := by
  unfold verticalIntegral
  rw [integral_finsetSum _ hF,Finset.mul_sum]

private theorem etaMainAtS_vertical_eq_sum
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (N₁ N₂ : ℕ) (A B : ℕ→ℂ) (c : ℝ)
    (hMain : ∀ g∈Finset.Icc 1 (min N₁ N₂),∀ a∈Finset.Icc 1 (N₁/g),∀ b∈Finset.Icc 1 (N₂/g),
      a.Coprime b → Integrable (fun y : ℝ => a03ZeroModeGCDEtaMainX Φ T σ α g a b A B ((c:ℂ)+(y:ℂ)*I))) :
    verticalIntegral c (a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B)=
      ∑g∈Finset.Icc 1 (min N₁ N₂),∑a∈Finset.Icc 1 (N₁/g),∑b∈Finset.Icc 1 (N₂/g),
        if a.Coprime b then verticalIntegral c (a03ZeroModeGCDEtaMainX Φ T σ α g a b A B) else 0 := by
  have hTerm (g : ℕ) (hg : g∈Finset.Icc 1 (min N₁ N₂)) (a : ℕ) (ha : a∈Finset.Icc 1 (N₁/g))
      (b : ℕ) (hb : b∈Finset.Icc 1 (N₂/g)) :
      Integrable (fun y : ℝ => if a.Coprime b then a03ZeroModeGCDEtaMainX Φ T σ α g a b A B ((c:ℂ)+(y:ℂ)*I) else 0) := by
    by_cases hab : a.Coprime b
    · simpa only [ite_eq_left hab] using hMain g hg a ha b hb hab
    · simp only [ite_eq_right hab]
      exact integrable_zero _ _ _
  have hA (g : ℕ) (hg : g∈Finset.Icc 1 (min N₁ N₂)) (a : ℕ) (ha : a∈Finset.Icc 1 (N₁/g)) :=
    integrable_finsetSum (Finset.Icc 1 (N₂/g)) (hTerm g hg a ha)
  have hG (g : ℕ) (hg : g∈Finset.Icc 1 (min N₁ N₂)) :=
    integrable_finsetSum (Finset.Icc 1 (N₁/g)) (hA g hg)
  unfold a03ZeroModeGCDEtaMainAtS
  rw [etaVerticalIntegral_finsetSum _ _ _ hG]
  apply Finset.sum_congr rfl
  intro g hg
  rw [etaVerticalIntegral_finsetSum _ _ _ (hA g hg)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [etaVerticalIntegral_finsetSum _ _ _ (hTerm g hg a ha)]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a.Coprime b
  · simp only [ite_eq_left hab]
  · simp [hab,verticalIntegral]

theorem a03ZeroModeGCDEtaFront_full_reconstruction
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T η : ℝ} (hT : 0<T) (hη : 0<η) (hη1 : η≤1/16)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ)
    (hResidual : ∀ g a b : ℕ,0<g → 0<a → 0<b → a.Coprime b →
      Integrable (fun y : ℝ => a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B
        (((1+η/4:ℝ):ℂ)+(y:ℂ)*I))) :
    (T:ℂ)*a03ZeroModeGCDEtaFront Φ T σ α N₁ N₂ A B (η/4) (η/4) (1+η/4)=
      (T:ℂ)*verticalIntegral (1+η/4) (a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B)+
        a03ZeroModeGCDEtaResidual Φ T σ (η/4) α N₁ N₂ A B := by
  have hε : 0<η/4 := by positivity
  have hε1 : η/4<1/8 := by linarith
  have hα' : ∀ j : Fin 4,‖α j‖≤(η/4)/8 := by
    simpa only [div_div,show (4:ℝ)*8=32 by norm_num] using hα
  have hBlock (g a b : ℕ) (hg : 0<g) (ha : 0<a) (hb : 0<b) (hab : a.Coprime b) :=
    a03ZeroModeGCDEtaFrontBlock_outer_reconstruction hΦ hSupp hT hη hη1 σ α hα hρ hg ha hb A B
      (a03ZeroModeGCDEtaFrontBlock_height_integrable hΦ hSupp hT hε hε1 σ α hα' hρ hg ha hb hab A B)
      (hResidual g a b hg ha hb hab)
  have hMain : ∀ g∈Finset.Icc 1 (min N₁ N₂),∀ a∈Finset.Icc 1 (N₁/g),∀ b∈Finset.Icc 1 (N₂/g),
      a.Coprime b → Integrable (fun y : ℝ => a03ZeroModeGCDEtaMainX Φ T σ α g a b A B
        (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) := by
    intro g hg a ha b hb hab
    exact (hBlock g a b
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1)
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
      (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) hab).1
  have hSum : a03ZeroModeGCDEtaFront Φ T σ α N₁ N₂ A B (η/4) (η/4) (1+η/4)=
      (∑g∈Finset.Icc 1 (min N₁ N₂),∑a∈Finset.Icc 1 (N₁/g),∑b∈Finset.Icc 1 (N₂/g),
        ((if a.Coprime b then verticalIntegral (1+η/4) (a03ZeroModeGCDEtaMainX Φ T σ α g a b A B) else 0)+
        (if a.Coprime b then verticalIntegral (1+η/4) (a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B) else 0))) := by
    unfold a03ZeroModeGCDEtaFront
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a.Coprime b
    · simpa only [ite_eq_left hab] using (hBlock g a b
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) hab).2
    · simp only [ite_eq_right hab,zero_add]
  rw [hSum,etaMainAtS_vertical_eq_sum Φ T σ α N₁ N₂ A B (1+η/4) hMain]
  simp only [Finset.sum_add_distrib,a03ZeroModeGCDEtaResidual]
  ring

private theorem etaChamberRatioRoot_ne_zero {T κ : ℝ} (hT : 1<T) (hκ : 0<κ)
    (σ : MomentShifts) (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (dual m n : Bool) :
    ∀ j : Fin 2,a03ZeroModeRatioRoot (rawMomentShifts T (SixthMoment.a03SourceNormalizedChamber dual m n σ)) j≠0 := by
  have hrootτ := SixthMoment.a03NormalizedPureRoot_gap_chambers σ hroot dual m n
  have hpure (k : PurePolarIndex) : purePolarRoot T (SixthMoment.a03SourceNormalizedChamber dual m n σ) k≠0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hrootτ k)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  intro j
  fin_cases j
  · change a03ZeroModeRatioRoot (rawMomentShifts T (SixthMoment.a03SourceNormalizedChamber dual m n σ)) 0≠0
    rw [a03ZeroModeRatioRoot_zero_eq_pure]
    exact neg_ne_zero.mpr (hpure _)
  · change a03ZeroModeRatioRoot (rawMomentShifts T (SixthMoment.a03SourceNormalizedChamber dual m n σ)) 1≠0
    rw [a03ZeroModeRatioRoot_one_eq_pure]
    exact neg_ne_zero.mpr (hpure _)

theorem a03ZeroModeGCDEtaFront_actual_branch_chambers_eventually_reconstruction
    (K : Set MomentShifts) (hK : IsCompact K) {κ η : ℝ}
    (hκ : 0<κ) (hη : 0<η) (hη1 : η≤1/16)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,∀ N₁ N₂ : ℕ,∀ A B : ℕ→ℂ,
      let α := rawMomentShifts T (SixthMoment.a03SourceNormalizedChamber dual m n σ)
      let Ψ := SixthMoment.a03RatioLeadingBranchProfile dual Φ T σ
      (T:ℂ)*a03ZeroModeGCDEtaFront Ψ T σ α N₁ N₂ A B (η/4) (η/4) (1+η/4)=
        (T:ℂ)*verticalIntegral (1+η/4) (a03ZeroModeGCDEtaMainAtS Ψ T σ α N₁ N₂ A B)+
          a03ZeroModeGCDEtaResidual Ψ T σ (η/4) α N₁ N₂ A B := by
  obtain ⟨C,hC,hRes⟩ := a03ZeroModeGCDEtaResidual_actual_branch_chambers_uniform_vertical_bound K hK hκ hη hη1 hroot hΦ hSupp
  let W := a03SourceNormalizedChambersCompactSet K
  have hW := a03SourceNormalizedChambersCompactSet_isCompact K hK
  filter_upwards [hRes,compactNormalizedShifts_eventually_norm_small W hW (η/32) (by positivity),
    eventually_gt_atTop (1:ℝ)] with T hRes hsmall hT
  intro σ hσ dual m n N₁ N₂ A B
  have hmem : SixthMoment.a03SourceNormalizedChamber dual m n σ∈W :=
    mem_iUnion.mpr ⟨(dual,(m,n)),⟨σ,hσ,rfl⟩⟩
  apply a03ZeroModeGCDEtaFront_full_reconstruction
    (SixthMoment.a03RatioLeadingBranchProfile_contDiff hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((SixthMoment.a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp)
    (zero_lt_one.trans hT) hη hη1 σ _ (hsmall _ hmem)
    (etaChamberRatioRoot_ne_zero hT hκ σ (hroot σ hσ) dual m n) N₁ N₂ A B
  intro g a b hg ha hb _
  exact (hRes σ hσ dual m n g a b hg ha hb A B).1

end
end SixthMoment.Source

import SixthMoment.Numerator.U.ZeroModes.Arithmetic.ChamberVariableMainStart
import SixthMoment.Numerator.U.ZeroModes.MainXMellinJoin
import SixthMoment.Numerator.U.ZeroModes.RatioLeadingBranchSmooth

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03ZeroModeTimeMoment_dual_partner {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) (m n : Bool) :
    a03ZeroModeTimeMoment (a03RatioLeadingBranchProfile true Φ T σ) T
      (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1))=
    a03ZeroModeTimeMoment Φ T (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) := by
  rw [a03ZeroModeTimeMoment_eq_integral _
    ((a03RatioLeadingBranchProfile_support true Φ T σ).trans hSupp) hT,
    a03ZeroModeTimeMoment_eq_integral _ hSupp hT]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [a03RatioLeadingBranchProfile,a03ProfileProduct,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    have hscale : 0<T*t/(2*Real.pi) := by positivity
    unfold a03RatioLeadingBranchProfile a03ProfileProduct bblrDualLeadingMultiplier
    simp only [ite_true]
    have he : (-∑j : Fin 4,rawMomentShifts T σ j)+
        (-(a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1) 1)-
          (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1) 3))=
        -(a03ZeroModeChamberShifts m n (rawMomentShifts T σ) 1)-
          (a03ZeroModeChamberShifts m n (rawMomentShifts T σ) 3) := by
      cases m <;> cases n <;>
        norm_num [a03ZeroModeChamberShifts,a03ZeroModePairPermutation,bblrSixShifts,Fin.sum_univ_succ] <;> ring
    have hp := Complex.cpow_add (-∑j : Fin 4,rawMomentShifts T σ j)
      (-(a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1) 1)-
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1) 3))
      (Complex.ofReal_ne_zero.mpr hscale.ne')
    push_cast at hp
    push_cast
    rw [mul_assoc,←hp,he]


theorem a03ZeroModeTimeMoment_scaled_eq_physical (Φ : ℝ→ℂ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (α : MomentShifts) (C : ℂ) :
    (T:ℂ)*a03ZeroModeTimeMoment Φ T α*C=
      ∫t : ℝ,Φ (t/T)*(t/(2*Real.pi):ℂ)^(-α 1-α 3)*C := by
  rw [a03ZeroModeTimeMoment_eq_integral Φ hSupp hT]
  let f : ℝ→ℂ := fun t => Φ t*((T*t/(2*Real.pi):ℝ):ℂ)^(-α 1-α 3)*C
  have he : (∫t : ℝ,f (t/T))=(T:ℂ)*(∫t : ℝ,f t) := by
    rw [Measure.integral_comp_div,abs_of_pos hT,Complex.real_smul]
  have hp (t : ℝ) : f (t/T)=Φ (t/T)*(t/(2*Real.pi):ℂ)^(-α 1-α 3)*C := by
    dsimp only [f]
    have ht : T*(t/T)=t := by field_simp
    rw [ht]
    push_cast
    rfl
  rw [show (T:ℂ)*(∫t : ℝ,Φ t*((T*t/(2*Real.pi):ℝ):ℂ)^(-α 1-α 3))*C=
    (T:ℂ)*(∫t : ℝ,f t) by dsimp only [f]; rw [integral_mul_const]; ring,←he]
  apply integral_congr_ae
  exact ae_of_all _ hp

private theorem physicalChamberRatioRoot_ne_zero {T κ : ℝ} (hT : 1<T) (hκ : 0<κ)
    (σ : MomentShifts)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (dual m n : Bool) :
    ∀ j : Fin 2,a03ZeroModeRatioRoot
      (a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1
        else rawMomentShifts T σ)) j≠0 := by
  let τ := a03SourceNormalizedChamber dual m n σ
  have hrootτ := a03NormalizedPureRoot_gap_chambers σ hroot dual m n
  have hpure (k : PurePolarIndex) : purePolarRoot T τ k≠0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hrootτ k)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  rw [←a03SourceNormalizedChamber_raw]
  intro j
  fin_cases j
  · change a03ZeroModeRatioRoot (rawMomentShifts T τ) 0≠0
    rw [a03ZeroModeRatioRoot_zero_eq_pure]
    exact neg_ne_zero.mpr (hpure _)
  · change a03ZeroModeRatioRoot (rawMomentShifts T τ) 1≠0
    rw [a03ZeroModeRatioRoot_one_eq_pure]
    exact neg_ne_zero.mpr (hpure _)

theorem a03PhysicalChamberIntegratedMain_pair_eq_crossed {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T δ κ cs : ℝ} (hT : 1<T) (hδ : 0<δ) (hδ1 : δ<1/4) (hκ : 0<κ)
    (hcs : 1<cs) (hcs2 : cs≤3/2) (σ : MomentShifts)
    (hα : ∀ j,‖rawMomentShifts T σ j‖≤δ/4)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (m n : Bool) (N₁ N₂ : ℕ) (A B : ℕ→ℂ) :
    2*(T:ℂ)*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS Φ T σ
      (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) N₁ N₂ A B)+
    2*(T:ℂ)*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS
      (a03RatioLeadingBranchProfile true Φ T σ) T σ
      (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1)) N₁ N₂ A B)=
      (T:ℂ)*a03ZeroModeTimeMoment Φ T (a03ZeroModeChamberShifts m n (rawMomentShifts T σ))*
        a03CrossedArithmeticSum N₁ N₂ A B (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) := by
  let α₀ := a03ZeroModeChamberShifts m n (rawMomentShifts T σ)
  let α₁ := a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1)
  have hα₀ : ∀ j,‖α₀ j‖≤δ/4 := a03ZeroMode_chamber_norm_le m n hα
  have hα₁ : ∀ j,‖α₁ j‖≤δ/4 :=
    a03ZeroMode_chamber_norm_le (!n) (!m) (bblrSixShifts_norm_le _ hα 1)
  let c₀ : ℝ := (cs-(α₀ 1+α₀ 3).re)/2
  let c₁ : ℝ := (cs-(α₁ 1+α₁ 3).re)/2
  have hc (α : MomentShifts) (hαb : ∀ j,‖α j‖≤δ/4) :
      (cs-(α 1+α 3).re)/2∈Icc δ 1 := by
    have h₁ := abs_le.mp ((Complex.abs_re_le_norm _).trans (hαb 1))
    have h₃ := abs_le.mp ((Complex.abs_re_le_norm _).trans (hαb 3))
    simp only [Complex.add_re]
    constructor <;> linarith
  have he₀ := a03ZeroModeGCDEtaMainAtS_vertical_eq_M hΦ hSupp (zero_lt_one.trans hT) σ α₀
    (fun j => (hα₀ j).trans (by linarith))
    (physicalChamberRatioRoot_ne_zero hT hκ σ hroot false m n) N₁ N₂ A B hcs
  have he₁ := a03ZeroModeGCDEtaMainAtS_vertical_eq_M
    (a03RatioLeadingBranchProfile_contDiff hΦ hSupp (zero_lt_one.trans hT) σ true)
    ((a03RatioLeadingBranchProfile_support true Φ T σ).trans hSupp) (zero_lt_one.trans hT) σ α₁
    (fun j => (hα₁ j).trans (by linarith))
    (physicalChamberRatioRoot_ne_zero hT hκ σ hroot true (!n) (!m)) N₁ N₂ A B hcs
  have htm := a03ZeroModeTimeMoment_dual_partner hSupp (zero_lt_one.trans hT) σ m n
  have hp : a03ZeroModeContourPrefactor α₁=a03ZeroModeContourPrefactor α₀ := by
    rw [show α₁=a03ZeroModeReverseNegative α₀ from
      (a03ZeroMode_chamber_dual_partner m n _).symm,a03ZeroModeContourPrefactor_reverseNegative]
  have hpair := a03PhysicalChamberMainContour_start_pair_eq_crossed hT hδ hδ1 hκ
    (hc α₀ hα₀) (hc α₁ hα₁) σ hα hroot m n N₁ N₂ A B
  change a03ZeroModeContourPrefactor α₀*(verticalIntegral c₀
    (fun w => polarPoleKiller T σ w/w*a03EtaMainFunction N₁ N₂ A B α₀ w)+
    verticalIntegral c₁ (fun w => polarPoleKiller T σ w/w*a03EtaMainFunction N₁ N₂ A B α₁ w))=
      a03CrossedArithmeticSum N₁ N₂ A B α₀ at hpair
  change a03ZeroModeTimeMoment (a03RatioLeadingBranchProfile true Φ T σ) T α₁=
    a03ZeroModeTimeMoment Φ T α₀ at htm
  rw [htm,hp] at he₁
  change _=(T:ℂ)*a03ZeroModeTimeMoment Φ T α₀*a03CrossedArithmeticSum N₁ N₂ A B α₀
  calc
    _=(T:ℂ)*(2*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS Φ T σ α₀ N₁ N₂ A B)+
      2*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS (a03RatioLeadingBranchProfile true Φ T σ) T σ α₁ N₁ N₂ A B)) := by ring
    _=(T:ℂ)*a03ZeroModeTimeMoment Φ T α₀*
      (a03ZeroModeContourPrefactor α₀*(verticalIntegral c₀
        (fun w => polarPoleKiller T σ w/w*a03EtaMainFunction N₁ N₂ A B α₀ w)+
        verticalIntegral c₁ (fun w => polarPoleKiller T σ w/w*a03EtaMainFunction N₁ N₂ A B α₁ w))) := by
          rw [he₀,he₁]
          dsimp only [c₀,c₁]
          ring
    _=_ := by rw [hpair]


theorem a03PhysicalChamberIntegratedMain_pair_eventually_eq_indexed
    (K : Set MomentShifts) (hK : IsCompact K) {κ cs : ℝ} (hκ : 0<κ)
    (hcs : 1<cs) (hcs2 : cs≤3/2)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ m n : Bool,
      2*(T:ℂ)*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS (fun t => (Φ t:ℂ)) T σ
        (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) ⌊T^a⌋₊ ⌊T^b⌋₊
        (fun k => (f (Real.log k/Real.log T):ℂ)) (fun k => (g (Real.log k/Real.log T):ℂ)))+
      2*(T:ℂ)*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS
        (a03RatioLeadingBranchProfile true (fun t => (Φ t:ℂ)) T σ) T σ
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1)) ⌊T^a⌋₊ ⌊T^b⌋₊
        (fun k => (f (Real.log k/Real.log T):ℂ)) (fun k => (g (Real.log k/Real.log T):ℂ)))=
      a03DiagonalArithmeticIndexedMainTerm (a03CrossedChamberLabel m n)
        T a b (rawMomentShifts T σ) f g Φ := by
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  filter_upwards [compactNormalizedShifts_eventually_norm_small K hK (1/32) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with T hsmall hT
  intro σ hσ m n
  rw [a03PhysicalChamberIntegratedMain_pair_eq_crossed hΦc hΦs hT (δ:=1/8)
    (by norm_num) (by norm_num) hκ hcs hcs2 σ
    (by simpa only [show (1/8:ℝ)/4=1/32 by norm_num] using hsmall σ hσ)
    (hroot σ hσ) m n ⌊T^a⌋₊ ⌊T^b⌋₊
    (fun k => (f (Real.log k/Real.log T):ℂ)) (fun k => (g (Real.log k/Real.log T):ℂ))]
  rw [a03ZeroModeTimeMoment_scaled_eq_physical _ hΦs (zero_lt_one.trans hT)]
  exact a03CrossedChamberArithmeticMoment_eq_indexed m n T a b (rawMomentShifts T σ) f g Φ


theorem a03PhysicalEightIntegratedMain_eventually_eq_crossedArithmetic
    (K : Set MomentShifts) (hK : IsCompact K) {κ cs : ℝ} (hκ : 0<κ)
    (hcs : 1<cs) (hcs2 : cs≤3/2)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∑dual : Bool,∑m : Bool,∑n : Bool,
        2*(T:ℂ)*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS
          (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
          (a03ZeroModeChamberShifts m n
            (if dual then bblrSixShifts (rawMomentShifts T σ) 1 else rawMomentShifts T σ))
          ⌊T^a⌋₊ ⌊T^b⌋₊ (fun k => (f (Real.log k/Real.log T):ℂ))
          (fun k => (g (Real.log k/Real.log T):ℂ))))=
      ∑j : Fin 4,a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩
        T a b (rawMomentShifts T σ) f g Φ := by
  filter_upwards [a03PhysicalChamberIntegratedMain_pair_eventually_eq_indexed K hK
    hκ hcs hcs2 hroot a b f g Φ hΦ] with T he
  intro σ hσ
  have h₀₀ := he σ hσ false false
  have h₀₁ := he σ hσ false true
  have h₁₀ := he σ hσ true false
  have h₁₁ := he σ hσ true true
  simp only [Fintype.sum_bool,a03RatioLeadingBranchProfile,Bool.false_eq_true,ite_false,ite_true,
    Bool.not_false,Bool.not_true,a03CrossedChamberLabel] at h₀₀ h₀₁ h₁₀ h₁₁ ⊢
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  norm_num at h₀₀ h₀₁ h₁₀ h₁₁ ⊢
  linear_combination h₀₀+h₀₁+h₁₀+h₁₁

end
end SixthMoment

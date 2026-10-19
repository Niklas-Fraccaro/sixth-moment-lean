import Sechstmoment.Numerator.U.ZeroModes.FourChamberLiteralMainTail
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ActualBranchResidualBudget
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.EtaFullReconstruction
import Sechstmoment.Numerator.U.ZeroModes.PhysicalMainPair

/-! The full eight actual eta fronts give exactly the four crossed source
main terms up to the proved three-contour and literal-main tail budgets. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def a03EightActualEtaFront (T a b : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑dual : Bool,∑m : Bool,∑n : Bool,2*(T:ℂ)*a03ZeroModeGCDEtaFront
    (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
    (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
    ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
    (a03ZeroModeRatioActualAmplifierCoefficient T g)
    (rectangularSlack a b/4) (rectangularSlack a b/4) (1+rectangularSlack a b/4)

def a03EightActualEtaResidual (T a b : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑dual : Bool,∑m : Bool,∑n : Bool,2*a03ZeroModeGCDEtaResidual
    (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (rectangularSlack a b/4)
    (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
    ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
    (a03ZeroModeRatioActualAmplifierCoefficient T g)

theorem a03EightActualEtaFront_eventually_eq_mainPairs_add_residual
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      a03EightActualEtaFront T a b σ f g Φ=
        (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)+
          a03EightActualEtaResidual T a b σ f g Φ := by
  obtain ⟨hη,hη1,_⟩ := a03ZeroModeRatioResidualAmplifier_exponent_lt_one ha hab hlen
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  have hcs : 1<1+rectangularSlack a b/4 := by linarith
  have hcs2 : 1+rectangularSlack a b/4≤(3/2:ℝ) := by linarith
  filter_upwards [a03ZeroModeGCDEtaFront_actual_branch_chambers_eventually_reconstruction K hK
    hκ hη hη1 hroot hΦc hΦs,
    a03PhysicalEightIntegratedMain_eventually_eq_crossedArithmetic K hK hκ hcs hcs2 hroot a b f g Φ hΦ,
    a03ChamberMainPairMoment_eventually_eq_indexed K hK hκ hroot a b f g Φ]
    with T hRec hMain hPair
  intro σ hσ
  have hpoint (dual m n : Bool) :
      2*(T:ℂ)*a03ZeroModeGCDEtaFront
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g)
        (rectangularSlack a b/4) (rectangularSlack a b/4) (1+rectangularSlack a b/4)=
      2*(T:ℂ)*verticalIntegral (1+rectangularSlack a b/4)
        (a03ZeroModeGCDEtaMainAtS (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
          (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
          ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
          (a03ZeroModeRatioActualAmplifierCoefficient T g))+
      2*a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (rectangularSlack a b/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g) := by
    have hr := hRec σ hσ dual m n ⌊T^a⌋₊ ⌊T^b⌋₊
      (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
    dsimp only at hr
    linear_combination 2*hr
  have hm := hMain σ hσ
  simp_rw [←a03SourceNormalizedChamber_raw] at hm
  change (∑dual : Bool,∑m : Bool,∑n : Bool,2*(T:ℂ)*verticalIntegral (1+rectangularSlack a b/4)
    (a03ZeroModeGCDEtaMainAtS (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
      (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
      ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
      (a03ZeroModeRatioActualAmplifierCoefficient T g)))=_ at hm
  have hp : (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)=
      ∑j : Fin 4,a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩
        T a b (rawMomentShifts T σ) f g Φ := by
    simp_rw [hPair σ hσ]
    simp only [Fintype.sum_bool,a03CrossedChamberLabel,Bool.false_eq_true,ite_false,ite_true,
      Fin.sum_univ_succ]
    norm_num
    ring
  unfold a03EightActualEtaFront a03EightActualEtaResidual
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  rw [hm,hp]

theorem a03EightActualEtaFront_minus_literal_crossed_uniform_oT
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ,0<ε → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖a03EightActualEtaFront T a b σ f g Φ-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤ε*T := by
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  intro ε hε
  filter_upwards [a03EightActualEtaFront_eventually_eq_mainPairs_add_residual ha hab hlen K hK hκ hroot f g Φ hΦ,
    a03FourChamberMainPairs_minus_literal_crossed_uniform_oT ha hab hlen K hK hκ hroot f g Φ hf hg hΦ
      (ε/2) (by positivity),
    a03ZeroModeGCDEtaResidual_actual_branch_chambers_uniform_oT K hK hκ ha hab hlen hroot f g hf hg hΦc hΦs
      (ε/32) (by positivity)] with T hId hTail hResidual
  intro σ hσ
  have hTerm (dual m n : Bool) :
      ‖2*a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (rectangularSlack a b/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g)‖≤(ε/16)*T := by
    rw [norm_mul,Complex.norm_ofNat]
    calc
      _≤2*((ε/32)*T) := mul_le_mul_of_nonneg_left (hResidual σ hσ dual m n) (by norm_num)
      _=_ := by ring
  have hR : ‖a03EightActualEtaResidual T a b σ f g Φ‖≤(ε/2)*T := by
    unfold a03EightActualEtaResidual
    calc
      _≤∑dual : Bool,∑m : Bool,∑n : Bool,‖2*a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (rectangularSlack a b/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro dual _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro m _
        exact norm_sum_le _ _
      _≤∑_dual : Bool,∑_m : Bool,∑_n : Bool,(ε/16)*T := by
        apply Finset.sum_le_sum
        intro dual _
        apply Finset.sum_le_sum
        intro m _
        apply Finset.sum_le_sum
        intro n _
        exact hTerm dual m n
      _=_ := by simp; ring
  rw [hId σ hσ]
  have he : (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)+
      a03EightActualEtaResidual T a b σ f g Φ-
      (∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)=
    ((∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)-
      ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)+
      a03EightActualEtaResidual T a b σ f g Φ := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hTail σ hσ) hR).trans_eq (by ring))

end
end Sechstmoment

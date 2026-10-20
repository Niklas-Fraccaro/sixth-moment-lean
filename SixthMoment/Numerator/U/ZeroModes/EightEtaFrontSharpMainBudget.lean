import SixthMoment.Numerator.U.Sources.ActualUnrestrictedGCDInitialJoin
import SixthMoment.Numerator.U.ZeroModes.EightEtaFrontMainBudget

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def a03EightActualEtaFrontAtEta (T a b η : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑dual : Bool,∑m : Bool,∑n : Bool,2*(T:ℂ)*a03ZeroModeGCDEtaFront
    (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
    (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
    ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
    (a03ZeroModeRatioActualAmplifierCoefficient T g)
    (η/4) (η/4) (1+η/4)

def a03EightActualEtaResidualAtEta (T a b η : ℝ) (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑dual : Bool,∑m : Bool,∑n : Bool,2*a03ZeroModeGCDEtaResidual
    (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (η/4)
    (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
    ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
    (a03ZeroModeRatioActualAmplifierCoefficient T g)

theorem a03EightActualEtaFrontAtEta_eventually_eq_mainPairs_add_residual
    {a b η : ℝ} (hη : 0<η) (hη1 : η≤1/16)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      a03EightActualEtaFrontAtEta T a b η σ f g Φ=
        (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)+
          a03EightActualEtaResidualAtEta T a b η σ f g Φ := by
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  have hcs : 1<1+η/4 := by linarith
  have hcs2 : 1+η/4≤(3/2:ℝ) := by linarith
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
        (η/4) (η/4) (1+η/4)=
      2*(T:ℂ)*verticalIntegral (1+η/4)
        (a03ZeroModeGCDEtaMainAtS (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ
          (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
          ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
          (a03ZeroModeRatioActualAmplifierCoefficient T g))+
      2*a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (η/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g) := by
    have hr := hRec σ hσ dual m n ⌊T^a⌋₊ ⌊T^b⌋₊
      (a03ZeroModeRatioActualAmplifierCoefficient T f) (a03ZeroModeRatioActualAmplifierCoefficient T g)
    dsimp only at hr
    linear_combination 2*hr
  have hm := hMain σ hσ
  simp_rw [←a03SourceNormalizedChamber_raw] at hm
  change (∑dual : Bool,∑m : Bool,∑n : Bool,2*(T:ℂ)*verticalIntegral (1+η/4)
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
  unfold a03EightActualEtaFrontAtEta a03EightActualEtaResidualAtEta
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  rw [hm,hp]



theorem a03FourChamberMainPairs_minus_literal_crossed_uniform_power_bound
    {a b ε : ℝ} (hab : a≤b) (hε : 0<ε)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤
        C*T^(rectangularSecondExponent a b ε) := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  obtain ⟨C,hC,hbound⟩ := a03DiagonalIndexedMainTerm_uniform_power_bound hR hκ hab hε f g Φ hf hg hΦ
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [a03ChamberMainPairMoment_eventually_eq_indexed K hK hκ hroot a b f g Φ,hbound] with T hp hb
  intro σ hσ
  have hσR (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have hpair : (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)=
      ∑j : Fin 4,a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) f g Φ := by
    simp_rw [hp σ hσ]
    simp only [Fintype.sum_bool,a03CrossedChamberLabel,Bool.false_eq_true,ite_false,ite_true,Fin.sum_univ_succ]
    norm_num
    ring
  rw [hpair,←Finset.sum_sub_distrib]
  calc
    _≤∑j : Fin 4,‖a03DiagonalArithmeticIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
      (rawMomentShifts T σ) f g Φ-bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖ := norm_sum_le _ _
    _≤∑_j : Fin 4,C*T^(rectangularSecondExponent a b ε) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_sub_rev]
      exact hb σ hσR (hroot σ hσ) _
    _=_ := by simp; ring

theorem a03ActualEtaResidual_chambers_uniform_first_power_bound
    {a b η ε : ℝ} (ha : 0≤a) (hab : a≤b) (hε : 0<ε)
    (hη : 0<η) (hη1 : η≤1/16) (hηcost : η*(1+a+b)≤ε/2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,
      ‖a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (η/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g)‖≤C*T^(rectangularFirstExponent a b ε) := by
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨C,hC,hRes⟩ := a03ZeroModeGCDEtaResidual_actual_branch_chambers_uniform_full_amplifier_bound
    K hK hκ hη hη1 hroot f g hΦc hΦs
  obtain ⟨D,hD,hMass⟩ := a03ZeroModeRatioResidualAmplifierMass_uniform_bound hab hη (by linarith) f g hf hg
  have hlog := (log_pow_isLittleO_rpow 56 (δ:=ε/2) (by positivity)).bound zero_lt_one
  have hexp : 1/2+η+a*(1/4+η)+b*(3/4+η)+ε/2≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    have hb : 0≤b := ha.trans hab
    nlinarith only [hηcost,ha,hb]
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [hRes,hlog,eventually_ge_atTop (1:ℝ)] with T hr hl hT
  intro σ hσ dual m n
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hl' : (Real.log T)^56≤T^(ε/2) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.log_nonneg hT) 56),
      abs_of_nonneg (Real.rpow_nonneg hTp.le (ε/2)),one_mul] using hl
  apply (hr σ hσ dual m n).trans
  calc
    _≤C*T^(ε/2)*T^(1/2+η)*(D*T^(a*(1/4+η)+b*(3/4+η))) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hTp.le _)
        exact mul_le_mul_of_nonneg_left hl' hC
      · exact hMass T hT
      · exact a03ZeroModeRatioResidualAmplifierMass_nonneg _ _ _ _ _ _
      · positivity
    _=(C*D)*T^(1/2+η+a*(1/4+η)+b*(3/4+η)+ε/2) := by
      have hp : T^(1/2+η+a*(1/4+η)+b*(3/4+η)+ε/2)=
          T^(1/2+η)*T^(a*(1/4+η)+b*(3/4+η))*T^(ε/2) := by
        rw [show 1/2+η+a*(1/4+η)+b*(3/4+η)+ε/2=
          ((1/2+η)+(a*(1/4+η)+b*(3/4+η)))+ε/2 by ring,
          Real.rpow_add hTp,Real.rpow_add hTp]
      rw [hp]
      ring
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) (mul_nonneg hC hD)


theorem a03EightActualEtaResidualAtEta_uniform_first_power_bound
    {a b η ε : ℝ} (ha : 0≤a) (hab : a≤b) (hε : 0<ε)
    (hη : 0<η) (hη1 : η≤1/16) (hηcost : η*(1+a+b)≤ε/2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖a03EightActualEtaResidualAtEta T a b η σ f g Φ‖≤C*T^(rectangularFirstExponent a b ε) := by
  obtain ⟨C,hC,hRes⟩ := a03ActualEtaResidual_chambers_uniform_first_power_bound
    ha hab hε hη hη1 hηcost K hK hκ hroot f g Φ hf hg hΦ
  refine ⟨16*C,by positivity,?_⟩
  filter_upwards [hRes] with T hr
  intro σ hσ
  have hterm (dual m n : Bool) :
      ‖2*a03ZeroModeGCDEtaResidual
        (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (η/4)
        (rawMomentShifts T (a03SourceNormalizedChamber dual m n σ))
        ⌊T^a⌋₊ ⌊T^b⌋₊ (a03ZeroModeRatioActualAmplifierCoefficient T f)
        (a03ZeroModeRatioActualAmplifierCoefficient T g)‖≤2*C*T^(rectangularFirstExponent a b ε) := by
    rw [norm_mul,Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hr σ hσ dual m n) (by norm_num)).trans_eq (by ring)
  unfold a03EightActualEtaResidualAtEta
  calc
    _≤∑dual : Bool,∑m : Bool,∑n : Bool,‖2*a03ZeroModeGCDEtaResidual
      (a03RatioLeadingBranchProfile dual (fun t => (Φ t:ℂ)) T σ) T σ (η/4)
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
    _≤∑_dual : Bool,∑_m : Bool,∑_n : Bool,2*C*T^(rectangularFirstExponent a b ε) := by
      apply Finset.sum_le_sum
      intro dual _
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro n _
      exact hterm dual m n
    _=_ := by simp; ring

theorem a03EightActualEtaFrontAtEta_minus_literal_crossed_uniform_sharp
    {a b η ε : ℝ} (ha : 0≤a) (hab : a≤b) (hε : 0<ε)
    (hη : 0<η) (hη1 : η≤1/16) (hηcost : η*(1+a+b)≤ε/2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖a03EightActualEtaFrontAtEta T a b η σ f g Φ-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤
        C*(T^(rectangularFirstExponent a b ε)+T^(rectangularSecondExponent a b ε)) := by
  obtain ⟨R,hR,hRes⟩ := a03EightActualEtaResidualAtEta_uniform_first_power_bound
    ha hab hε hη hη1 hηcost K hK hκ hroot f g Φ hf hg hΦ
  obtain ⟨M,hM,hMain⟩ := a03FourChamberMainPairs_minus_literal_crossed_uniform_power_bound
    hab hε K hK hκ hroot f g Φ hf hg hΦ
  refine ⟨R+M,add_nonneg hR hM,?_⟩
  filter_upwards [hRes,hMain,eventually_gt_atTop (0:ℝ),
    a03EightActualEtaFrontAtEta_eventually_eq_mainPairs_add_residual hη hη1 K hK hκ hroot f g Φ hΦ]
    with T hr hm hT hid
  intro σ hσ
  rw [hid σ hσ]
  have he : (∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)+
      a03EightActualEtaResidualAtEta T a b η σ f g Φ-
      (∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)=
    a03EightActualEtaResidualAtEta T a b η σ f g Φ+
      ((∑m : Bool,∑n : Bool,a03ChamberMainPairMoment m n T a b σ f g Φ)-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  calc
    _≤R*T^(rectangularFirstExponent a b ε)+M*T^(rectangularSecondExponent a b ε) :=
      add_le_add (hr σ hσ) (hm σ hσ)
    _≤(R+M)*T^(rectangularFirstExponent a b ε)+(R+M)*T^(rectangularSecondExponent a b ε) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (Real.rpow_nonneg hT.le _))
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hR) (Real.rpow_nonneg hT.le _))
    _=_ := by ring

theorem a03ActualEightUnrestrictedRatioGCDVStar_minus_literal_crossed_uniform_sharp
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ,0<ε → ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun t => (Φ t:ℂ)) T a b σ f g)-
        ∑j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
          (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ‖≤
        C*(T^(1/2+a+b+ε)+T^(3/4+3*a/8+5*b/8+ε)) := by
  intro ε hε
  let η := min (1/16:ℝ) (ε/4)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1/16 := min_le_left _ _
  have hηε : η≤ε/4 := min_le_right _ _
  have hab1 : a+b≤1 := by linarith
  have hηcost : η*(1+a+b)≤ε/2 := by
    exact (mul_le_mul_of_nonneg_left (by linarith : 1+a+b≤2) hη.le).trans (by linarith)
  obtain ⟨C,hC,hBudget⟩ := a03EightActualEtaFrontAtEta_minus_literal_crossed_uniform_sharp
    ha hab hε hη hη1 hηcost K hK hκ hroot f g Φ hf hg hΦ
  have hΦc : ContDiff ℝ ∞ (fun t => (Φ t:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun t => (Φ t:ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  refine ⟨C,hC,?_⟩
  filter_upwards [hBudget,a03ActualEightUnrestrictedRatioGCDVStar_eventually_eq_etaFront
    hΦc hΦs K hK hκ (show 0<η/4 by positivity) (show η/4<1/8 by linarith) f g a b]
    with T hb hn
  intro σ hσ
  have he : (∑dual : Bool,a03ActualFourUnrestrictedRatioGCDVStar dual (fun t => (Φ t:ℂ)) T a b σ f g)=
      a03EightActualEtaFrontAtEta T a b η σ f g Φ := by
    rw [hn σ hσ (hroot σ hσ)]
    unfold a03EightActualEtaFrontAtEta
    simp only [Finset.mul_sum,a03SourceNormalizedChamber_raw,a03SourceShifts]
  rw [he]
  exact hb σ hσ

end
end SixthMoment

import Sechstmoment.Numerator.U.ZeroModes.Ratio.BadSourceFiniteBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.InactiveFarKernel
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceMomentJoin

/-! Selected inactive discrete source blocks consist entirely of genuine
far tuples after their literal amplifier and dyadic supports are imposed. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_inactive_supported_source_tuple_is_far
    (T s : ℝ) (f g : ℝ→ℝ) (j : Fin 3→ℕ) (k n : Fin 4→ℕ) (p q : ℕ) (positive : Bool)
    (hinactive : ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
      (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k)
    (hselected : if positive then rectangularPositiveQuadGap (p+1) (q+1) n
      else rectangularNegativeQuadGap (p+1) (q+1) n)
    (hf : f (Real.log (p+1:ℝ)/Real.log T)≠0) (hg : g (Real.log (q+1:ℝ)/Real.log T)≠0)
    (hw : rectangularAFESmoothWeight k n≠0)
    (hW : a03SourceAmplifierGapWeight (p+1) (q+1) (rectangularAFEGap positive (p+1) (q+1) n) j≠0) :
    a03ActualFarSelection T s positive p q n := by
  let gap := rectangularAFEGap positive (p+1) (q+1) n
  have hweights := Finset.prod_ne_zero_iff.mp hW
  have hWp : rectangularSmoothBlockWeight ((p+1:ℝ)/rectangularAFESmoothScale (j 0))≠0 := by
    simpa [a03SourceAmplifierGapWeight] using hweights 0 (Finset.mem_univ _)
  have hWq : rectangularSmoothBlockWeight ((q+1:ℝ)/rectangularAFESmoothScale (j 1))≠0 := by
    simpa [a03SourceAmplifierGapWeight] using hweights 1 (Finset.mem_univ _)
  have hWh : rectangularSmoothBlockWeight ((gap:ℝ)/rectangularAFESmoothScale (j 2))≠0 := by
    simpa [a03SourceAmplifierGapWeight,gap] using hweights 2 (Finset.mem_univ _)
  have hnear : ¬rectangularNearRelation (T^(s-1)) (rectangularAFESourceTuple (p+1) (q+1) n gap) := by
    intro hn
    apply hinactive
    exact ⟨p+1,q+1,gap,n,positive,
      phaseActualAmplifierCoefficient_ne_zero_of_factors T _ f (by omega)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hWp)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hf),
      phaseActualAmplifierCoefficient_ne_zero_of_factors T _ g (by omega)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hWq)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hg),
      hw,hWh,rectangular_AFE_gap_source_relation positive _ _ n hselected,hn⟩
  refine ⟨hselected,?_⟩
  apply le_of_lt
  simpa [rectangularNearRelation,rectangularAFESourceTuple,gap] using not_le.mp hnear

def a03RatioLocalizedRawTimeTerm (dual positive : Bool) (c T _s v : ℝ) (σ α : MomentShifts)
    (f g Φ : ℝ→ℝ) (j : Fin 3→ℕ) (k : Fin 4→ℕ) (z : (ℕ×ℕ)×(Fin 4→ℕ)) : ℂ :=
  if (if positive then rectangularPositiveQuadGap (z.1.1+1) (z.1.2+1) z.2
    else rectangularNegativeQuadGap (z.1.1+1) (z.1.2+1) z.2) then
    (a03SourceAmplifierGapWeight (z.1.1+1) (z.1.2+1)
      (rectangularAFEGap positive (z.1.1+1) (z.1.2+1) z.2) j:ℂ)*
      (rectangularAFESmoothWeight k z.2:ℂ)*
      a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
        (z.2 0+1) (z.2 1+1) (z.2 2+1) (z.2 3+1)*
        ∫t : ℝ,rectangularMomentPairWeight T f g Φ z.1.1 z.1.2 t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
            rectangularAFEMellinKernel (polarPoleKiller T σ) α t z.2 ((c:ℂ)+(v:ℂ)*I)
  else 0

theorem a03RatioLocalizedRawTimeTerm_inactive_norm_le
    {T s c v B L : ℝ} (hB : 0≤B) (hL : 0≤L) (σ α : MomentShifts)
    (f g Φ : ℝ→ℝ) (dual positive : Bool) (j : Fin 3→ℕ) (k : Fin 4→ℕ)
    (hinactive : ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (j 0))
      (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) (T^(s-1)) f g k)
    (hratio : ∀ n : Fin 4→ℕ,‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
      (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤B)
    (hkernel : ∀ p q : ℕ,∀ n : Fin 4→ℕ,a03ActualFarSelection T s positive p q n →
      ‖∫t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L)
    (z : (ℕ×ℕ)×(Fin 4→ℕ)) :
    ‖a03RatioLocalizedRawTimeTerm dual positive c T s v σ α f g Φ j k z‖≤B*L := by
  unfold a03RatioLocalizedRawTimeTerm
  by_cases hselected : if positive then rectangularPositiveQuadGap (z.1.1+1) (z.1.2+1) z.2
    else rectangularNegativeQuadGap (z.1.1+1) (z.1.2+1) z.2
  · simp only [hselected,ite_true]
    by_cases hw : rectangularAFESmoothWeight k z.2=0
    · simp [hw]; positivity
    by_cases hW : a03SourceAmplifierGapWeight (z.1.1+1) (z.1.2+1)
        (rectangularAFEGap positive (z.1.1+1) (z.1.2+1) z.2) j=0
    · simp [hW]; positivity
    by_cases hf : f (Real.log (z.1.1+1:ℝ)/Real.log T)=0
    · simp [rectangularMomentPairWeight,hf]; positivity
    by_cases hg : g (Real.log (z.1.2+1:ℝ)/Real.log T)=0
    · simp [rectangularMomentPairWeight,hg]; positivity
    have hfar := a03_inactive_supported_source_tuple_is_far T s f g j k z.2 z.1.1 z.1.2 positive
      hinactive hselected hf hg hw hW
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (a03SourceAmplifierGapWeight_nonneg_le_one _ _ _ _).1,
      Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg _ _)]
    have hweight : a03SourceAmplifierGapWeight (z.1.1+1) (z.1.2+1)
        (rectangularAFEGap positive (z.1.1+1) (z.1.2+1) z.2) j*rectangularAFESmoothWeight k z.2≤1 :=
      (mul_le_mul (a03SourceAmplifierGapWeight_nonneg_le_one _ _ _ _).2
      (rectangular_small_contour_smooth_weight_le_one k z.2) (rectangular_AFE_smooth_weight_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
    exact (mul_le_mul (mul_le_mul hweight (hratio z.2) (norm_nonneg _) zero_le_one)
      (hkernel z.1.1 z.1.2 z.2 hfar) (norm_nonneg _) (by simpa using hB)).trans_eq (by ring)
  · simp only [hselected,ite_false,norm_zero]
    exact mul_nonneg hB hL

theorem a03_actual_ratio_raw_physical_source_eq_localized_terms {a b T : ℝ}
    (hT : 1<T) (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ α : MomentShifts) (c s v : ℝ) (j : Fin 3→ℕ) (k : Fin 4→ℕ) (dual positive : Bool) :
    (T:ℂ)*a03SourceMellinScaleFactor c v α k*
      a03EndpointPhysicalTensorSum (a03RatioSourceRawFamilyKernel dual (fun x => (Φ x:ℂ)) c
        (Real.log (rectangularAFESmoothScale (k 0)/rectangularAFESmoothScale (k 1)))
        (Real.log (rectangularAFESmoothScale (k 2)/rectangularAFESmoothScale (k 3))))
        positive T (rectangularAFESmoothScale (j 0)) (rectangularAFESmoothScale (j 1)) (rectangularAFESmoothScale (j 2)) σ α v f g k=
      ∑z∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        a03RatioLocalizedRawTimeTerm dual positive c T s v σ α f g Φ j k z := by
  rw [a03_actual_ratio_raw_physical_source_finite_reindex hT (boundaryActual_scale_pos _)
    (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) f g Φ hf hg σ α c v k dual positive]
  apply Finset.sum_congr rfl
  intro z _
  unfold a03RatioLocalizedRawTimeTerm
  by_cases hselected : if positive then rectangularPositiveQuadGap (z.1.1+1) (z.1.2+1) z.2
    else rectangularNegativeQuadGap (z.1.1+1) (z.1.2+1) z.2
  · simp only [hselected,ite_true]
    rw [a03_actual_localized_time_integral_eq_amp_gap_weight]
    ring
  · simp only [hselected,ite_false]

theorem a03ActualPassiveRatioInactiveSourceBlock_norm_le_card
    {a b T s εsource c v B L : ℝ} (hT : 1<T) (hB : 0≤B) (hL : 0≤L)
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (σ α : MomentShifts)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (dual positive : Bool) (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hinactive : select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2)
    (hratio : ∀ n : Fin 4→ℕ,‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
      (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤B)
    (hkernel : ∀ p q : ℕ,∀ n : Fin 4→ℕ,a03ActualFarSelection T s positive p q n →
      ‖∫t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L) :
    ‖a03ActualPassiveRatioSourceBlockValue select false dual positive (fun x => (Φ x:ℂ))
      c T s εsource v σ α f g i‖≤
      (B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*((rectangularAFESmoothBox i.2).card:ℝ) := by
  unfold a03ActualPassiveRatioSourceBlockValue
  dsimp only [phaseActualScales]
  by_cases hgood : select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,Bool.false_eq_true,ite_false]
    rw [a03_actual_ratio_raw_physical_source_eq_localized_terms hT f g Φ hf hg σ α c s v i.1 i.2 dual positive]
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _z∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox i.2),B*L := by
        apply Finset.sum_le_sum
        intro z _
        exact a03RatioLocalizedRawTimeTerm_inactive_norm_le hB hL σ α f g Φ dual positive i.1 i.2
          (hinactive hgood.1) hratio hkernel z
      _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.product_eq_sprod,Finset.card_product,Finset.card_range,Nat.cast_mul]; ring
  · simp only [hgood,ite_false,norm_zero]
    positivity

theorem a03ActualPassiveRatioInactiveSourceFinite_norm_le_card
    {a b T s u εsource c v B L : ℝ} (hT : 1<T) (hB : 0≤B) (hL : 0≤L)
    (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (σ α : MomentShifts)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (dual : Bool)
    (hinactive : ∀ i,select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2)
    (hratio : ∀ n : Fin 4→ℕ,‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
      (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤B)
    (hkernel : ∀ positive : Bool,∀ p q : ℕ,∀ n : Fin 4→ℕ,a03ActualFarSelection T s positive p q n →
      ‖∫t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L) :
    ‖a03ActualPassiveRatioSourceFiniteValue select false dual (fun x => (Φ x:ℂ))
      c T a b s u εsource v σ α f g‖≤
      2*((a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))).card:ℝ)*
        (B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u)) := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hb (positive : Bool) : ‖∑ i∈grid,a03ActualPassiveRatioSourceBlockValue select false dual positive
      (fun x => (Φ x:ℂ)) c T s εsource v σ α f g i‖≤
      (grid.card:ℝ)*((B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u))) := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _i∈grid,(B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (a03ActualPassiveRatioInactiveSourceBlock_norm_le_card hT hB hL select σ α f g Φ hf hg
          dual positive i (hinactive i) hratio (hkernel positive)).trans
        apply mul_le_mul_of_nonneg_left
        · exact (rectangular_small_contour_box_card_le i.2).trans
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp (Finset.mem_product.mp hi).2).2 (by norm_num))
        · positivity
      _=_ := by simp
  unfold a03ActualPassiveRatioSourceFiniteValue
  apply (norm_sum_le _ _).trans
  calc
    _≤∑ _positive : Bool,(grid.card:ℝ)*((B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u))) :=
      Finset.sum_le_sum (fun positive _ => hb positive)
    _=_ := by simp only [Fintype.sum_bool]; dsimp [grid]; ring

theorem a03_actual_ratio_inactive_physical_finite_uniform_rapid
    {a b s u εsource c κ θ R : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g Φ : ℝ→ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : 0<s) (hs1 : s≤1) (hu : 0<u) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T →
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      (∀ i,select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2) →
      ∀ dual : Bool,
      ‖a03ActualPassiveRatioSourceFiniteValue select false dual (fun x => (Φ x:ℂ))
        c T a b s u εsource v σ α f g‖≤C*T^(-M) := by
  let Q : ℝ := M+a+b+5+u
  obtain ⟨Cr,hCr,hratio⟩ := a03_actual_ratio_partition_uniform_linear_bound hκ
  obtain ⟨Cp,hCp,hkernel⟩ := a03_actual_ratio_inactive_far_time_kernel_uniform_rapid
    hf hg hΦ hc hc1 hκ hθ hR hs hs1 Q
  obtain ⟨D,hD,hcard⟩ := a03_actual_source_block_grid_uniform_log_card ha hb
    (by positivity : 0≤(a+b)/2+s+u/2) hu
  let L := (Nat.factorial 7:ℝ)*Real.exp 1
  let C := 32*D*L*(Cr*Cr)*Cp
  refine ⟨C,by dsimp [C,L]; positivity,?_⟩
  filter_upwards [hratio,hkernel,hcard,eventually_gt_atTop (1:ℝ)] with T hr hk hcard hT
  intro σ α hσ hα hroot v hv select hinactive dual
  have hTp : 0<T := zero_lt_one.trans hT
  have hL : 0≤L := by dsimp [L]; positivity
  have hlog : (1+Real.log T)^7≤L*T := by
    simpa only [Real.rpow_one,one_pow,div_one] using logarithmic_power_le_rpow (by norm_num : (0:ℝ)<1) hT.le 7
  have hratio4 (n : Fin 4→ℕ) : ‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
      (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤(Cr*Cr)*T^(2:ℝ) := by
    simp only [a03ZeroModeRatioFourWeight,Bool.false_eq_true,ite_false,norm_mul]
    calc
      _≤(Cr*T)*(Cr*T) := mul_le_mul
        (hr σ hroot _ (by positivity)) (hr σ hroot _ (by positivity)) (norm_nonneg _) (by positivity)
      _=(Cr*Cr)*T^(2:ℝ) := by rw [Real.rpow_two]; ring
  have hbox := a03ActualPassiveRatioInactiveSourceFinite_norm_le_card
    (a:=a) (b:=b) (u:=u) (εsource:=εsource) hT
    (mul_nonneg (mul_nonneg hCr hCr) (Real.rpow_nonneg hTp.le _))
    (mul_nonneg hCp (Real.rpow_nonneg hTp.le _)) select σ α f g Φ hf hg dual hinactive hratio4
    (fun positive p q n hfar => hk σ α hσ hα hroot v hv dual positive p q n hfar)
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hcbd : 2*(grid.card:ℝ)≤2*(D*(L*T)) :=
    mul_le_mul_of_nonneg_left (hcard.trans (mul_le_mul_of_nonneg_left hlog hD)) (by norm_num)
  have hβ : 0≤((Cr*Cr)*T^(2:ℝ))*(Cp*T^(-Q)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hcbd hβ
  have h2 := mul_le_mul h1 (Nat.floor_le (Real.rpow_nonneg hTp.le a))
    (Nat.cast_nonneg ⌊T^a⌋₊) (mul_nonneg (by positivity : 0≤2*(D*(L*T))) hβ)
  have h3 := mul_le_mul h2 (Nat.floor_le (Real.rpow_nonneg hTp.le b))
    (Nat.cast_nonneg ⌊T^b⌋₊) (by positivity : 0≤2*(D*(L*T))*(((Cr*Cr)*T^(2:ℝ))*(Cp*T^(-Q)))*T^a)
  have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : 0≤16*T^(2+u))
  have hpow : T*(T^(2:ℝ)*T^(-Q))*T^a*T^b*T^(2+u)=T^(-M) := by
    calc
      _=T^(1:ℝ)*(T^(2:ℝ)*T^(-Q))*T^a*T^b*T^(2+u) := by rw [Real.rpow_one]
      _=T^(1+2-Q+a+b+(2+u)) := by
        rw [←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp,←Real.rpow_add hTp]
        congr 1
        ring
      _=T^(-M) := by congr 1; dsimp [Q]; ring
  calc
    _≤2*(D*(L*T))*(((Cr*Cr)*T^(2:ℝ))*(Cp*T^(-Q)))*T^a*T^b*(16*T^(2+u)) := hbox.trans h4
    _=C*(T*(T^(2:ℝ)*T^(-Q))*T^a*T^b*T^(2+u)) := by dsimp [C]; ring
    _=C*T^(-M) := by rw [hpow]

theorem a03_actual_ratio_inactive_physical_moment_uniform_rapid
    {a b s u c κ θ R : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g Φ : ℝ→ℝ} (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : 0<s) (hs1 : s≤1) (hu : 0<u) (M εsource : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop,
      (∀ i,select i → ¬phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2) →
      ∀ dual : Bool,
      ‖a03ActualPassiveRatioSourceValueMoment select false dual (fun x => (Φ x:ℂ))
        c T a b s u εsource θ σ α f g‖≤C*T^(-M) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_ratio_inactive_physical_finite_uniform_rapid
    ha hb hf hg hΦ hc hc1 hκ hθ hR hs hs1 hu (εsource:=εsource) (M+1)
  refine ⟨2*θ*C,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hb hT
  intro σ α hσ hα hroot select hinactive dual
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hint := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (fun v hv => hb σ α hσ hα hroot v
      (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)) select hinactive dual)
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])] at hint
  unfold a03ActualPassiveRatioSourceValueMoment
  calc
    _≤C*T^(-(M+1))*(θ*Real.log T-(-θ*Real.log T)) := hint
    _≤C*T^(-(M+1))*(2*θ*T) := mul_le_mul_of_nonneg_left
      (by nlinarith [Real.log_le_self hTp.le]) (by positivity)
    _=(2*θ*C)*T^(-M) := by
      have hp : T^(-(M+1))*T=T^(-M) := by
        calc
          _=T^(-(M+1))*T^(1:ℝ) := by rw [Real.rpow_one]
          _=T^(-(M+1)+1) := (Real.rpow_add hTp _ _).symm
          _=T^(-M) := by congr 1; ring
      rw [show C*T^(-(M+1))*(2*θ*T)=(2*θ*C)*(T^(-(M+1))*T) by ring,hp]

end
end Sechstmoment

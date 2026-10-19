import Sechstmoment.Numerator.U.ZeroModes.Ratio.BadSourceKernel
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceTimeBridge

/-! Actual finite counting for the complement of the soft source mask. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualRatioBadSourceTimeBlock (dual positive : Bool) (c T a b s εsource v : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  if a03ActualRatioSourceGoodBlock T s εsource f g i then 0 else
    a03ActualRatioTimeBlock false false dual positive (a03ZeroModeRatioWeight (rawMomentShifts T σ))
      c T a b s v σ α f g Φ i.1 i.2

def a03ActualRatioBadSourceTimeFinite (dual : Bool) (c T a b s u εsource v : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualRatioBadSourceTimeBlock dual positive c T a b s εsource v σ α f g Φ i

def a03ActualRatioBadSourceTimeMoment (dual : Bool) (c T a b s u εsource θ : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ

theorem a03SourceAmplifierGapWeight_nonneg_le_one (u w h : ℕ) (j : Fin 3→ℕ) :
    0≤a03SourceAmplifierGapWeight u w h j ∧ a03SourceAmplifierGapWeight u w h j≤1 := by
  refine ⟨Finset.prod_nonneg (fun _ _ => rectangularSmoothBlockWeight_nonneg _),?_⟩
  change (∏ r : Fin 3,rectangularSmoothBlockWeight
    (((![u,w,h] r : ℕ):ℝ)/rectangularAFESmoothScale (j r)))≤1
  calc
    _≤∏ _r : Fin 3,(1:ℝ) := Finset.prod_le_prod₀
      (fun _ _ => rectangularSmoothBlockWeight_nonneg _) (fun _ _ => rectangularSmoothBlockWeight_le_one _)
    _=1 := by simp

theorem a03ActualRatioBadSourceTimeBlock_norm_le_card
    {T a b s εsource c v B L : ℝ} (hB : 0≤B) (hL : 0≤L)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (dual positive : Bool)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hratio : phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      ¬a03ActualRatioSourceGoodBlock T s εsource f g i →
      ∀ n : Fin 4→ℕ,rectangularAFESmoothWeight i.2 n≠0 →
      ‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
        (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤B)
    (hkernel : ∀ u w : ℕ,∀ n : Fin 4→ℕ,
      ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L) :
    ‖a03ActualRatioBadSourceTimeBlock dual positive c T a b s εsource v σ α f g Φ i‖≤
      (B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*((rectangularAFESmoothBox i.2).card:ℝ) := by
  unfold a03ActualRatioBadSourceTimeBlock
  by_cases hgood : a03ActualRatioSourceGoodBlock T s εsource f g i
  · simp only [hgood,ite_true,norm_zero]
    positivity
  · simp only [hgood,ite_false]
    unfold a03ActualRatioTimeBlock
    by_cases hactive : phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2
    · simp only [hactive,ite_true]
      apply (norm_sum_le _ _).trans
      calc
        _≤∑ _z∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox i.2),B*L := by
          apply Finset.sum_le_sum
          intro z _
          by_cases hselected : if positive then rectangularPositiveQuadGap (z.1.1+1) (z.1.2+1) z.2
            else rectangularNegativeQuadGap (z.1.1+1) (z.1.2+1) z.2
          · simp only [hselected,ite_true]
            by_cases hw : rectangularAFESmoothWeight i.2 z.2=0
            · simp only [hw,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero]
              exact mul_nonneg hB hL
            · rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
                Real.norm_of_nonneg (a03SourceAmplifierGapWeight_nonneg_le_one _ _ _ _).1,
                Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg _ _)]
              have hwbd : a03SourceAmplifierGapWeight (z.1.1+1) (z.1.2+1)
                  (rectangularAFEGap positive (z.1.1+1) (z.1.2+1) z.2) i.1*rectangularAFESmoothWeight i.2 z.2≤1 :=
                (mul_le_mul (a03SourceAmplifierGapWeight_nonneg_le_one _ _ _ _).2
                  (rectangular_small_contour_smooth_weight_le_one _ _) (rectangular_AFE_smooth_weight_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
              exact (mul_le_mul (mul_le_mul hwbd (hratio hactive hgood z.2 hw) (norm_nonneg _) zero_le_one)
                (hkernel z.1.1 z.1.2 z.2) (norm_nonneg _) (by simpa only [one_mul] using hB)).trans_eq
                (by ring)
          · simp only [hselected,ite_false,norm_zero]
            exact mul_nonneg hB hL
        _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.product_eq_sprod,Finset.card_product,Finset.card_range,Nat.cast_mul]; ring
    · simp only [hactive,ite_false,norm_zero]
      positivity

theorem a03ActualRatioBadSourceTimeFinite_norm_le_card
    {T a b s u εsource c v B L : ℝ} (_hT : 0≤T) (hB : 0≤B) (hL : 0≤L)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (dual : Bool)
    (hratio : ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      ¬a03ActualRatioSourceGoodBlock T s εsource f g i →
      ∀ n : Fin 4→ℕ,rectangularAFESmoothWeight i.2 n≠0 →
      ‖a03ZeroModeRatioFourWeight (a03ZeroModeRatioWeight (rawMomentShifts T σ)) false false
        (n 0+1) (n 1+1) (n 2+1) (n 3+1)‖≤B)
    (hkernel : ∀ _positive : Bool,∀ u w : ℕ,∀ n : Fin 4→ℕ,
      ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L) :
    ‖a03ActualRatioBadSourceTimeFinite dual c T a b s u εsource v σ α f g Φ‖≤
      2*((a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))).card:ℝ)*
        (B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u)) := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hb (positive : Bool) : ‖∑ i∈grid,a03ActualRatioBadSourceTimeBlock dual positive c T a b s εsource v σ α f g Φ i‖≤
      (grid.card:ℝ)*((B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u))) := by
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _i∈grid,(B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (a03ActualRatioBadSourceTimeBlock_norm_le_card hB hL σ α f g Φ dual positive i
          (hratio i hi) (hkernel positive)).trans
        apply mul_le_mul_of_nonneg_left
        · exact (rectangular_small_contour_box_card_le i.2).trans
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp (Finset.mem_product.mp hi).2).2 (by norm_num))
        · positivity
      _=_ := by simp
  unfold a03ActualRatioBadSourceTimeFinite
  apply (norm_sum_le _ _).trans
  calc
    _≤∑ _positive : Bool,(grid.card:ℝ)*((B*L)*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*(16*T^(2+u))) :=
      Finset.sum_le_sum (fun positive _ => hb positive)
    _=_ := by simp only [Fintype.sum_bool]; dsimp [grid]; ring

end
end Sechstmoment

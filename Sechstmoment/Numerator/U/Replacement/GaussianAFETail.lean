import Mathlib.Analysis.Normed.Group.InfiniteSum
import Sechstmoment.Numerator.U.Replacement.GaussianTailUniform

/-! Summability and uniform power decay of the genuine fourfold AFE tail.
The cutoff acts on the actual vertical V integral, not on an abstract error.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def bblrGaussianAFETailSummand (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (n : Fin 4 → ℕ) : ℂ :=
  ((((n 0+1)*(n 1+1) : ℕ) : ℂ)/(((n 2+1)*(n 3+1) : ℕ) : ℂ))^(-(t : ℂ)*I)*
    bblrGaussianVTail T σ α (positiveQuadProduct n) t R /
      ∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j)

def bblrGaussianAFETail (T : ℝ) (σ α : MomentShifts) (t R : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, bblrGaussianAFETailSummand T σ α t R n

def bblrGaussianAFEQuadMajorant (n : Fin 4 → ℕ) : ℝ :=
  ∏ j : Fin 4, 1/(n j+1 : ℝ)^(5/4 : ℝ)

theorem bblrGaussianAFEQuadMajorant_nonneg (n : Fin 4 → ℕ) :
    0 ≤ bblrGaussianAFEQuadMajorant n := by unfold bblrGaussianAFEQuadMajorant; positivity

theorem bblrGaussianAFEQuadMajorant_summable : Summable bblrGaussianAFEQuadMajorant := by
  have hs : ∀ j : Fin 4, Summable (fun k : ℕ => 1/(k+1 : ℝ)^(5/4 : ℝ)) := by
    intro j
    have h := (Real.summable_one_div_nat_add_rpow 1 (5/4 : ℝ)).mpr (by norm_num)
    have ha (k : ℕ) : |(k : ℝ)+1| = (k : ℝ)+1 := abs_of_pos (by positivity)
    simpa only [ha] using h
  exact summable_finitePi_prod_nonneg 4 (fun _j k => 1/(k+1 : ℝ)^(5/4 : ℝ))
    (fun _j k => by positivity) hs

theorem bblrGaussianAFETailSummand_norm_le (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) {B : ℝ} (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, 0 < x → ‖bblrGaussianVTail T σ α x t R‖ ≤ B/x)
    (n : Fin 4 → ℕ) :
    ‖bblrGaussianAFETailSummand T σ α t R n‖ ≤ B*bblrGaussianAFEQuadMajorant n := by
  have hn (j : Fin 4) : 0 < (n j+1 : ℝ) := by positivity
  have hx : 0 < (positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  have hden : 0 < ∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hn j) _)
  have he : ∏ j : Fin 4, (n j+1 : ℝ)^(3/2+(α j).re) =
      (positiveQuadProduct n : ℝ)*∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re) := by
    have he' (j : Fin 4) : (n j+1 : ℝ)^(3/2+(α j).re) =
        (n j+1 : ℝ)*(n j+1 : ℝ)^(1/2+(α j).re) := by
      rw [show (3/2 : ℝ)+(α j).re = 1+(1/2+(α j).re) by ring,
        Real.rpow_add (hn j),Real.rpow_one]
    simp_rw [he']
    rw [Finset.prod_mul_distrib,positiveQuadProduct_eq_prod]
    push_cast
    rfl
  have hcp (j : Fin 4) : ‖(n j+1 : ℂ)^(1/2+α j)‖ =
      (n j+1 : ℝ)^(1/2+(α j).re) := by
    rw [show (n j+1 : ℂ) = ((n j+1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (hn j)]
    congr 1
    simp
  have hp (j : Fin 4) : 1/(n j+1 : ℝ)^(3/2+(α j).re) ≤
      1/(n j+1 : ℝ)^(5/4 : ℝ) := by
    have har := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hn j) _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega)
      (by linarith)
  unfold bblrGaussianAFETailSummand
  rw [norm_div,norm_mul,bblrAFE_oscillation_norm_one,one_mul,norm_prod]
  simp_rw [hcp]
  calc
    _ ≤ (B/(positiveQuadProduct n : ℝ))/
        (∏ j : Fin 4, (n j+1 : ℝ)^(1/2+(α j).re)) :=
      div_le_div_of_nonneg_right (hV _ hx) hden.le
    _ = B*∏ j : Fin 4, 1/(n j+1 : ℝ)^(3/2+(α j).re) := by
      rw [Finset.prod_div_distrib,Finset.prod_const_one,he]
      ring
    _ ≤ B*bblrGaussianAFEQuadMajorant n := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hp j)

theorem bblrGaussianAFETail_norm_summable (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) {B : ℝ} (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, 0 < x → ‖bblrGaussianVTail T σ α x t R‖ ≤ B/x) :
    Summable (fun n => ‖bblrGaussianAFETailSummand T σ α t R n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => bblrGaussianAFETailSummand_norm_le T σ α t R hα hB hV n)
    (bblrGaussianAFEQuadMajorant_summable.mul_left B)

theorem bblrGaussianAFETail_norm_le (T : ℝ) (σ α : MomentShifts) (t R : ℝ)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) {B : ℝ} (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, 0 < x → ‖bblrGaussianVTail T σ α x t R‖ ≤ B/x) :
    ‖bblrGaussianAFETail T σ α t R‖ ≤ B*(∑' n, bblrGaussianAFEQuadMajorant n) := by
  have hs := bblrGaussianAFETail_norm_summable T σ α t R hα hB hV
  unfold bblrGaussianAFETail
  calc
    _ ≤ ∑' n, ‖bblrGaussianAFETailSummand T σ α t R n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, B*bblrGaussianAFEQuadMajorant n :=
      hs.tsum_le_tsum (fun n => bblrGaussianAFETailSummand_norm_le T σ α t R hα hB hV n)
        (bblrGaussianAFEQuadMajorant_summable.mul_left B)
    _ = _ := tsum_mul_left

theorem bblrGaussianAFETailSummand_summable (T : ℝ) (σ α : MomentShifts)
    (t R : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R) (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Summable (bblrGaussianAFETailSummand T σ α t R) := by
  obtain ⟨D,hD,hbound⟩ := bblrGaussianVTail_norm_le
  have hCG := polarGaussianConstant_nonneg T σ 1
  apply Summable.of_norm
  apply bblrGaussianAFETail_norm_summable T σ α t R hα
    (B := D*polarGaussianConstant T σ 1*(2+t)^8*Real.exp (-(1/2)*R^2))
    (by positivity)
  intro x hx
  convert hbound T σ α hα t x R ht hx hR using 1
  ring

theorem bblrGaussianAFETail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T),
      ‖bblrGaussianAFETail T σ α t (T^ε)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ := bblrGaussianVTail_uniform_power_bound K δ hδ hρ hε A
  let S : ℝ := ∑' n, bblrGaussianAFEQuadMajorant n
  have hS : 0 ≤ S := tsum_nonneg bblrGaussianAFEQuadMajorant_nonneg
  refine ⟨D*S,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with T hb hT
  intro σ hσ α hα t ht
  calc
    _ ≤ (D*T^(-(A : ℝ)))*S :=
      bblrGaussianAFETail_norm_le T σ α t (T^ε) hα (by positivity)
        (fun x hx => hb σ hσ α hα t ht x hx)
    _ = _ := by ring

theorem bblrGaussianAFETail_uniform_raw_power_bound (K : Set MomentShifts)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrGaussianAFETail T σ (rawMomentShifts T σ) t (T^ε)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianAFETail_uniform_power_bound K δ hδ hρ hε A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hs
  intro σ hσ t ht
  exact hb σ hσ (rawMomentShifts T σ) (hs σ hσ) t ht

theorem bblrGaussianAFETail_uniform_six_shifts_power_bound (K : Set MomentShifts)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ k : Fin 6,
      ∀ t ∈ Icc T (2*T),
      ‖bblrGaussianAFETail T σ (bblrSixShifts (rawMomentShifts T σ) k) t (T^ε)‖ ≤
        C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianAFETail_uniform_power_bound K δ hδ hρ hε A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hs
  intro σ hσ k t ht
  apply hb σ hσ _ _ t ht
  intro j
  have h := hs σ hσ
  fin_cases k <;> fin_cases j <;> simp [bblrSixShifts] <;>
    first | simpa using h 0 | simpa using h 1 | simpa using h 2 | simpa using h 3

end
end Sechstmoment.Source

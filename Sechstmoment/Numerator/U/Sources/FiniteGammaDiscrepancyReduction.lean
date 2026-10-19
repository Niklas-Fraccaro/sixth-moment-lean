import Sechstmoment.Numerator.U.DiscrepancyIdentity
import Sechstmoment.Numerator.U.ZeroModes.DiagonalGammaMainTerms

/-! Uniform reduction of the literal A03 discrepancy to the two actual
finite Gamma offdiagonal moments and the four literal crossed terms.
Every known error is closed; the remaining discrepancy is explicitly named. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03FiniteGammaCrossedDiscrepancy (c T a b u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  a03ActualFiniteOffdiagonalGammaMoment false c T a b u θ σ f g Φ+
    a03ActualFiniteOffdiagonalGammaMoment true c T a b u θ σ f g Φ-
      ∑ j : Fin 4,bblrIndexedMainTerm ⟨j.val+2,by omega⟩ T a b
        (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ

theorem a03FinalDiscrepancy_minus_finiteGammaCrossed_uniform_oT_of_source
    (hAFE : BBLRv1FixedApproximateFEInput) {a b u θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2) (hu : 0<u) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ,0<ε → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03FiniteGammaCrossedDiscrepancy (rectangularSlack a b/512) T a b u θ σ f g Φ‖≤ε*T := by
  have hslack := (rectangular_slack_bounds hab hrect).1
  have hc : 0<rectangularSlack a b/512 := by positivity
  have hc1 : rectangularSlack a b/512≤1 := by dsimp [rectangularSlack]; linarith
  obtain ⟨C,_hC,htrunc⟩ := rectangularFullAFEMoment_uniform_finite_small_error hc hc1 hu hθ
    K hK κ hκ hroot a b f g Φ hf hg hΦ 0
  have hdiag := a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_oT_of_source
    (u:=u) ha hab hrect hκ hθ hu K hK hroot f g Φ hf hg hΦ
  intro ε hε
  filter_upwards [rectangular_concrete_AFE_integrated_uniform_negligible hAFE K hK κ hκ hroot
    a b f g Φ hf hg hΦ (ε/3) (by positivity),hdiag (ε/3) (by positivity),htrunc,
    compactNormalizedShifts_eventually_norm_small K hK (1/8) (by norm_num),
    eventually_gt_atTop (1:ℝ),eventually_ge_atTop (3*C/ε)] with T hE hD hF hraw hT hlarge
  intro σ hσ
  have hfull := rectangularFullAFEMoment_actual_identity hT σ
    (fun j => (hraw σ hσ j).trans_lt (by norm_num)) a b f g Φ hf hg hΦ
  have hsplit := rectangularFiniteSmallGaussianGridMoment_eq_diagonal_and_offdiagonal hc hT
    a b u θ σ (fun j => (hraw σ hσ j).trans (by norm_num)) f g Φ hf hg hΦ
  have he : bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
      a03FiniteGammaCrossedDiscrepancy (rectangularSlack a b/512) T a b u θ σ f g Φ=
    rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      (rectangularFullAFEMoment T σ f g Φ-
        rectangularFiniteSmallGaussianGridMoment (rectangularSlack a b/512) T σ f g Φ
          (T^(2+u)) (θ*Real.log T))+
      (a03ActualFiniteDiagonalGammaMoment false (rectangularSlack a b/512) T a b u θ σ f g Φ+
        a03ActualFiniteDiagonalGammaMoment true (rectangularSlack a b/512) T a b u θ σ f g Φ-
          (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
            bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)) := by
    unfold bblrMomentDiscrepancy a03FiniteGammaCrossedDiscrepancy
    rw [a03SixMainTerms_split,hfull.2,hsplit]
    ring
  have ht : ‖rectangularFullAFEMoment T σ f g Φ-
      rectangularFiniteSmallGaussianGridMoment (rectangularSlack a b/512) T σ f g Φ
        (T^(2+u)) (θ*Real.log T)‖≤(ε/3)*T := by
    have hb := (hF σ hσ).2.2
    simp only [neg_zero,Real.rpow_zero,mul_one] at hb
    have hx := (div_le_iff₀ hε).mp hlarge
    exact hb.trans (by nlinarith)
  have hpair : (∑ dual : Bool,a03ActualFiniteDiagonalGammaMoment dual (rectangularSlack a b/512)
      T a b u θ σ f g Φ)=
      a03ActualFiniteDiagonalGammaMoment false (rectangularSlack a b/512) T a b u θ σ f g Φ+
        a03ActualFiniteDiagonalGammaMoment true (rectangularSlack a b/512) T a b u θ σ f g Φ := by
    rw [Fintype.sum_bool]
    ring
  have hd := hD σ hσ
  rw [hpair] at hd
  rw [he]
  calc
    _≤‖rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
        (rectangularFullAFEMoment T σ f g Φ-
          rectangularFiniteSmallGaussianGridMoment (rectangularSlack a b/512) T σ f g Φ
            (T^(2+u)) (θ*Real.log T))‖+
        ‖a03ActualFiniteDiagonalGammaMoment false (rectangularSlack a b/512) T a b u θ σ f g Φ+
          a03ActualFiniteDiagonalGammaMoment true (rectangularSlack a b/512) T a b u θ σ f g Φ-
            (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
              bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖ := norm_add_le _ _
    _≤((ε/3)*T+(ε/3)*T)+(ε/3)*T :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (hE σ hσ) ht)) hd
    _=ε*T := by ring

end
end Sechstmoment

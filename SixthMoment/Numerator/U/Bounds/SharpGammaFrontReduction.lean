import SixthMoment.Numerator.U.Sources.FiniteGammaDiscrepancyReduction

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_sharp_bound
    {a b c ε κ θ u : ℝ} (ha : 0≤a) (hab : a≤b)
    (hc : 0<c) (hc1 : c≤1) (hcε : 2*c<ε/4) (hε : 0<ε)
    (hκ : 0<κ) (hθ : 0<θ) (hu : 0<u)
    (K : Set MomentShifts) (hK : IsCompact K)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤
        C*T^(rectangularFirstExponent a b ε) := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left B 0)
  obtain ⟨C,hC,hΓ⟩ := a03DiagonalGammaMoment_sub_Star_uniform_polylog_bound
    (u:=u) hc hc1 hcε hκ hθ.le hR f g Φ hf hg hΦ
  obtain ⟨D,hD,hStar⟩ := rectangularVStarSelectedMoment_uniform_finite_small_error
    hc hc1 hu hθ K hK κ hκ hroot a b f g Φ hf hg hΦ 0
  have hlog := (log_pow_isLittleO_rpow 1 (δ:=ε/4) (by positivity)).bound zero_lt_one
  have hq : 0≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith
  have hbudget : ε/4+(ε/4+(a+b)/2)≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith
  refine ⟨2*C+D,by positivity,?_⟩
  filter_upwards [hΓ,hStar,hlog,eventually_gt_atTop (1:ℝ),
    compactNormalizedShifts_eventually_norm_small K hK (1/4) (by norm_num)]
    with T hΓ hStar hl hT hraw
  intro σ hσ
  have hTp : 0<T := zero_lt_one.trans hT
  have hl' : Real.log T≤T^(ε/4) := by
    simpa only [pow_one,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hT.le),
      abs_of_nonneg (Real.rpow_nonneg hTp.le (ε/4)),one_mul] using hl
  have hΓpow (dual : Bool) :
      ‖a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ‖≤
        C*T^(rectangularFirstExponent a b ε) := by
    apply (hΓ σ (hσR σ hσ) (hroot σ hσ) dual).trans
    calc
      _≤C*T^(ε/4)*T^(ε/4+(a+b)/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl' hC)
          (Real.rpow_nonneg hTp.le _)
      _=C*T^(ε/4+(ε/4+(a+b)/2)) := by
        rw [Real.rpow_add hTp (ε/4) (ε/4+(a+b)/2)]
        ring
      _≤_ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT.le hbudget) hC
  have hleft : ‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
      (∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)‖≤
      (2*C)*T^(rectangularFirstExponent a b ε) := by
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑dual:Bool,‖a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ‖ := norm_sum_le _ _
      _≤∑_dual:Bool,C*T^(rectangularFirstExponent a b ε) :=
        Finset.sum_le_sum (fun dual _ => hΓpow dual)
      _=_ := by simp; ring
  have hright : ‖(∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)-
      (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
        bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤
      D*T^(rectangularFirstExponent a b ε) := by
    rw [a03DiagonalStarMoments_eq_selectedFiniteMoment hc hTp a b u θ σ (hraw σ hσ) f g Φ hΦ,
      ←rectangularVStarSelectedMoment_diagonal_eq_main_terms hTp a b σ (hraw σ hσ) f g Φ hΦ,
      norm_sub_rev]
    have hb := (hStar σ hσ true).2.2.2
    simp only [neg_zero,Real.rpow_zero,mul_one] at hb
    exact hb.trans (le_mul_of_one_le_right hD (Real.one_le_rpow hT.le hq))
  calc
    _≤‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
        (∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)‖+
      ‖(∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(2*C)*T^(rectangularFirstExponent a b ε)+D*T^(rectangularFirstExponent a b ε) :=
      add_le_add hleft hright
    _=(2*C+D)*T^(rectangularFirstExponent a b ε) := by ring

theorem a03FinalDiscrepancy_minus_finiteGammaCrossed_uniform_sharp_bound
    (hAFE : BBLRv1FixedApproximateFEInput) {a b c ε u θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hc : 0<c) (hc1 : c≤1) (hcε : 2*c<ε/4)
    (hε : 0<ε) (hu : 0<u) (hθ : 0<θ)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03FiniteGammaCrossedDiscrepancy c T a b u θ σ f g Φ‖≤
        C*T^(rectangularFirstExponent a b ε) := by
  obtain ⟨A,hA,hAFEerr⟩ := rectangular_concrete_AFE_integrated_uniform_bound
    hAFE K hK κ hκ hroot a b f g Φ hf hg hΦ 1
  obtain ⟨B,hB,htrunc⟩ := rectangularFullAFEMoment_uniform_finite_small_error hc hc1 hu hθ
    K hK κ hκ hroot a b f g Φ hf hg hΦ 0
  obtain ⟨D,hD,hdiag⟩ := a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_sharp_bound
    ha hab hc hc1 hcε hε hκ hθ hu K hK hroot f g Φ hf hg hΦ
  have hq : 0≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith
  have heq : 1+a+b-(1:ℝ)≤rectangularFirstExponent a b ε := by
    dsimp [rectangularFirstExponent]
    linarith
  refine ⟨A+B+D,by positivity,?_⟩
  filter_upwards [hAFEerr,htrunc,hdiag,
    compactNormalizedShifts_eventually_norm_small K hK (1/8) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with T hE hF hDg hraw hT
  intro σ hσ
  have hfull := rectangularFullAFEMoment_actual_identity hT σ
    (fun j => (hraw σ hσ j).trans_lt (by norm_num)) a b f g Φ hf hg hΦ
  have hsplit := rectangularFiniteSmallGaussianGridMoment_eq_diagonal_and_offdiagonal hc hT
    a b u θ σ (fun j => (hraw σ hσ j).trans (by norm_num)) f g Φ hf hg hΦ
  have he : bblrMomentDiscrepancy T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
      a03FiniteGammaCrossedDiscrepancy c T a b u θ σ f g Φ=
    rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
      (rectangularFullAFEMoment T σ f g Φ-
        rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+u)) (θ*Real.log T))+
      (a03ActualFiniteDiagonalGammaMoment false c T a b u θ σ f g Φ+
        a03ActualFiniteDiagonalGammaMoment true c T a b u θ σ f g Φ-
          (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
            bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)) := by
    unfold bblrMomentDiscrepancy a03FiniteGammaCrossedDiscrepancy
    rw [a03SixMainTerms_split,hfull.2,hsplit]
    ring
  have hEp : ‖rectangularAFEIntegratedError T (rawMomentShifts T σ)
      (polarPoleKiller T σ) f g Φ‖≤A*T^(rectangularFirstExponent a b ε) := by
    simp only [Nat.cast_one] at hE
    apply (hE σ hσ).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT.le heq) hA
  have ht : ‖rectangularFullAFEMoment T σ f g Φ-
      rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+u)) (θ*Real.log T)‖≤
      B*T^(rectangularFirstExponent a b ε) := by
    have hb := (hF σ hσ).2.2
    simp only [neg_zero,Real.rpow_zero,mul_one] at hb
    exact hb.trans (le_mul_of_one_le_right hB (Real.one_le_rpow hT.le hq))
  have hpair : (∑ dual : Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)=
      a03ActualFiniteDiagonalGammaMoment false c T a b u θ σ f g Φ+
        a03ActualFiniteDiagonalGammaMoment true c T a b u θ σ f g Φ := by
    rw [Fintype.sum_bool]
    ring
  have hd := hDg σ hσ
  rw [hpair] at hd
  rw [he]
  calc
    _≤‖rectangularAFEIntegratedError T (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
        (rectangularFullAFEMoment T σ f g Φ-
          rectangularFiniteSmallGaussianGridMoment c T σ f g Φ (T^(2+u)) (θ*Real.log T))‖+
        ‖a03ActualFiniteDiagonalGammaMoment false c T a b u θ σ f g Φ+
          a03ActualFiniteDiagonalGammaMoment true c T a b u θ σ f g Φ-
            (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
              bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖ :=
      norm_add_le _ _
    _≤(A*T^(rectangularFirstExponent a b ε)+B*T^(rectangularFirstExponent a b ε))+
        D*T^(rectangularFirstExponent a b ε) :=
      add_le_add ((norm_add_le _ _).trans (add_le_add hEp ht)) hd
    _=(A+B+D)*T^(rectangularFirstExponent a b ε) := by ring

end
end SixthMoment

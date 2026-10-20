import Sechstmoment.Numerator.U.Replacement.VStar.DiagonalFiniteMoment
import Sechstmoment.Numerator.U.ZeroModes.DiagonalGammaReplacement

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03DiagonalStarPairGrid (dual : Bool) (c T a b u θ : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    rectangularMomentPairWeight T f g Φ p q t*
      (if dual then bblrDualLeadingMultiplier T σ (t/T) else 1)*
      bblrVStarSelectedFiniteCore true c T σ (a03SourceShifts dual T σ) p q t
        (T^(2+u)) (θ*Real.log T)

theorem a03DiagonalStarWeightedKernel_continuousOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun w : ℝ×ℝ => (if dual then bblrDualLeadingMultiplier T σ (w.2/T) else 1)*
      rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α w.2 n ((c:ℂ)+(w.1:ℂ)*I))
        (Icc (-R) R ×ˢ Icc T (2*T)) := by
  apply ((a03FiniteGammaWeightedKernel_continuous hc dual σ α hσ hα n).continuousOn.sub
    (a03DiagonalReplacementKernel_continuousOn hc hT dual σ α hσ hα n R)).congr
  intro w hw
  have ht := hT.trans_le hw.2.1
  dsimp only [Pi.sub_apply]
  cases dual
  · simp only [a03DiagonalReplacementKernel,Bool.false_eq_true,ite_false,one_mul]
    rw [rectangularWeightReplacementMellinKernel_eq_actual_sub_star _ _ ht]
    ring
  · simp only [a03DiagonalReplacementKernel,ite_true]
    rw [rectangularDualReplacementMellinKernel_eq_actual_sub_leading_star _ _ _ _ ht,
      bblrDualLeadingMultiplier_time_eq hT.ne']
    ring

theorem a03DiagonalStarMoment_eq_pair_grid {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (a03DiagonalStarPairGrid dual c T a b u θ σ f g Φ) ∧
    a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ=
      ∫ t : ℝ,a03DiagonalStarPairGrid dual c T a b u θ σ f g Φ t := by
  let α := a03SourceShifts dual T σ
  let R := θ*Real.log T
  let K : (Fin 4→ℕ)→ℝ×ℝ→ℂ := fun n w =>
    (if dual then bblrDualLeadingMultiplier T σ (w.2/T) else 1)*
      rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α w.2 n ((c:ℂ)+(w.1:ℂ)*I)
  have hα : ∀ j,‖α j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  let F : ℕ→ℕ→(Fin 4→ℕ)→(Fin 4→ℕ)→ℝ×ℝ→ℂ := fun p q k n w =>
    if diagonalQuadRelation (p+1) (q+1) n then
      (rectangularAFESmoothWeight k n:ℂ)*rectangularMomentPairWeight T f g Φ p q w.2*K n w else 0
  have hF (p q : ℕ) (k n : Fin 4→ℕ) :
      Integrable (F p q k n) ((volume.restrict (Icc (-R) R)).prod volume) := by
    have hk := a03_pair_compact_time_contour_integrable hT f g Φ hΦ p q R (K n)
      (a03DiagonalStarWeightedKernel_continuousOn hc hT dual σ α hσ hα n R)
    dsimp only [F]
    by_cases hn : diagonalQuadRelation (p+1) (q+1) n
    · simp only [hn,ite_true]
      simpa only [mul_assoc] using hk.const_mul (rectangularAFESmoothWeight k n:ℂ)
    · simp only [hn,ite_false]
      exact integrable_zero _ _ _
  let H : ℝ×ℝ→ℂ := fun w => ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,F p q k n w
  have hH : Integrable H ((volume.restrict (Icc (-R) R)).prod volume) := by
    apply integrable_finsetSum
    intro p _
    apply integrable_finsetSum
    intro q _
    apply integrable_finsetSum
    intro k _
    exact integrable_finsetSum _ (fun n _ => hF p q k n)
  have hTime (p q : ℕ) (k n : Fin 4→ℕ) (v : ℝ) : Integrable (fun t : ℝ => F p q k n (v,t)) := by
    dsimp only [F]
    by_cases hn : diagonalQuadRelation (p+1) (q+1) n
    · simp only [hn,ite_true]
      have hh := a03DiagonalStarKernel_time_integrable hc hT dual σ α hσ hα f g Φ hΦ p q n v
      simpa only [K,mul_assoc] using hh.const_mul (rectangularAFESmoothWeight k n:ℂ)
    · simp only [hn,ite_false]
      exact integrable_zero _ _ _
  have hsource (v : ℝ) : a03ActualFiniteDiagonalStarMellinGrid dual c T a b u v f g Φ σ α=
      ∫t:ℝ,H (v,t) := by
    dsimp only [H]
    rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
      integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hTime p q k n v))))]
    unfold a03ActualFiniteDiagonalStarMellinGrid
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ =>
      hTime p q k n v)))]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hTime p q k n v))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum _ (fun n _ => hTime p q k n v)]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [F,K]
    by_cases hn : diagonalQuadRelation (p+1) (q+1) n
    · simp only [hn,ite_true,integral_const_mul,mul_assoc]
    · simp only [hn,ite_false,integral_zero]
  have htarget (t : ℝ) : a03DiagonalStarPairGrid dual c T a b u θ σ f g Φ t=
      (1/(2*Real.pi):ℂ)*∫v in Icc (-R) R,H (v,t) := by
    dsimp only [H]
    have hFn (p q : ℕ) (k n : Fin 4→ℕ) : IntegrableOn (fun v : ℝ => F p q k n (v,t)) (Icc (-R) R) := by
      dsimp only [F,K]
      by_cases hn : diagonalQuadRelation (p+1) (q+1) n
      · simp only [hn,ite_true]
        have hk : IntegrableOn (fun v : ℝ => rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α t n
            ((c:ℂ)+(v:ℂ)*I)) (Icc (-R) R) := by
          have hcont := (rectangular_VStar_Mellin_kernel_joint_continuous hc _
            (polarPoleKiller_differentiable T σ).continuous α n).comp
              (f:=fun v : ℝ => (t,v)) (continuous_const.prodMk continuous_id)
          exact hcont.continuousOn.integrableOn_compact isCompact_Icc
        simpa only [IntegrableOn,mul_assoc,mul_left_comm,mul_comm] using hk.const_mul
          ((rectangularAFESmoothWeight k n:ℂ)*rectangularMomentPairWeight T f g Φ p q t*
            (if dual then bblrDualLeadingMultiplier T σ (t/T) else 1))
      · simp only [hn,ite_false]
        exact integrable_zero _ _ _
    simp_rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
      integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hFn p q k n))))]
    unfold a03DiagonalStarPairGrid bblrVStarSelectedFiniteCore
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (fun k _ =>
      integrable_finsetSum _ (fun n _ => hFn p q k n)))]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun n _ => hFn p q k n))]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum _ (fun n _ => hFn p q k n)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [F,K]
    by_cases hn : diagonalQuadRelation (p+1) (q+1) n
    · simp only [hn,ite_true]
      rw [rectangular_actual_vstar_core_summand_Mellin]
      simp only [integral_const_mul]
      dsimp only [R,α]
      ring
    · simp only [hn,iff_true,ite_false,integral_zero,mul_zero]
  have hi : Integrable (a03DiagonalStarPairGrid dual c T a b u θ σ f g Φ) := by
    have hh := hH.integral_prod_right.const_mul (1/(2*Real.pi):ℂ)
    exact hh.congr (ae_of_all _ (fun t => (htarget t).symm))
  refine ⟨hi,?_⟩
  unfold a03ActualFiniteDiagonalStarMoment
  try simp only [neg_mul]
  change (1/(2*Real.pi):ℂ)*(∫v in Icc (-R) R,
    a03ActualFiniteDiagonalStarMellinGrid dual c T a b u v f g Φ σ α)=_
  simp_rw [hsource]
  rw [integral_integral_swap hH]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => (htarget t).symm)

theorem a03DiagonalStarMoments_eq_selectedFiniteMoment {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (a b u θ : ℝ) (σ : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)=
      rectangularVStarSelectedFiniteMoment true c T a b σ f g Φ (T^(2+u)) (θ*Real.log T) := by
  have h0 := a03DiagonalStarMoment_eq_pair_grid hc hT false a b u θ σ hσ f g Φ hΦ
  have h1 := a03DiagonalStarMoment_eq_pair_grid hc hT true a b u θ σ hσ f g Φ hΦ
  rw [Fintype.sum_bool,h1.2,h0.2,←integral_add h1.1 h0.1]
  unfold rectangularVStarSelectedFiniteMoment
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold a03DiagonalStarPairGrid rectangularVStarSelectedFiniteIntegrand
  simp only [a03SourceShifts,Bool.false_eq_true,ite_false,ite_true,mul_one]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_oT
    {a b c ε κ θ u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0<θ) (hu : 0<u) (hbudget : ε+(a+b)/2<1)
    (K : Set MomentShifts) (hK : IsCompact K)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ η : ℝ,0<η → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤η*T := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left B 0)
  have hΓ := a03DiagonalGammaMoment_sub_Star_uniform_oT (u:=u) hc hc1 hε hκ hθ.le hR hbudget f g Φ hf hg hΦ
  obtain ⟨C,hC,hStar⟩ := rectangularVStarSelectedMoment_uniform_finite_small_error hc hc1 hu hθ
    K hK κ hκ hroot a b f g Φ hf hg hΦ 0
  intro η hη
  have hConst := (isLittleO_const_id_atTop C).bound (show 0<η/2 by linarith)
  filter_upwards [hΓ (η/4) (by linarith),hStar,hConst,eventually_gt_atTop (1:ℝ),
    compactNormalizedShifts_eventually_norm_small K hK (1/4) (by norm_num)]
    with T hΓ hStar hConst hT hraw
  intro σ hσ
  have hTp : 0<T := zero_lt_one.trans hT
  have hleft : ‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
      (∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)‖≤(η/2)*T := by
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑dual:Bool,‖a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ‖ := norm_sum_le _ _
      _≤∑_dual:Bool,(η/4)*T := Finset.sum_le_sum (fun dual _ => hΓ σ (hσR σ hσ) (hroot σ hσ) dual)
      _=_ := by simp; ring
  have hright : ‖(∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)-
      (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
        bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤(η/2)*T := by
    rw [a03DiagonalStarMoments_eq_selectedFiniteMoment hc hTp a b u θ σ (hraw σ hσ) f g Φ hΦ,
      ←rectangularVStarSelectedMoment_diagonal_eq_main_terms hTp a b σ (hraw σ hσ) f g Φ hΦ,norm_sub_rev]
    have hb := (hStar σ hσ true).2.2.2
    simp only [neg_zero,Real.rpow_zero,mul_one] at hb
    apply hb.trans
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hC,abs_of_pos hTp] using hConst
  calc
    _≤‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ)-
        (∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)‖+
      ‖(∑dual:Bool,a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ)-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(η/2)*T+(η/2)*T := add_le_add hleft hright
    _=η*T := by ring

theorem a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_oT_of_source
    {a b κ θ u : ℝ} (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (hκ : 0<κ) (hθ : 0<θ) (hu : 0<u)
    (K : Set MomentShifts) (hK : IsCompact K)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ η : ℝ,0<η → ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      ‖(∑dual:Bool,a03ActualFiniteDiagonalGammaMoment dual (rectangularSlack a b/512) T a b u θ σ f g Φ)-
        (bblrIndexedMainTerm 0 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ+
          bblrIndexedMainTerm 1 T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ)‖≤η*T := by
  have hd := (rectangular_slack_bounds hab hrect).1
  exact a03ActualFiniteDiagonalGamma_minus_literal_main01_uniform_oT
    (ε:=rectangularSlack a b/16) (by positivity)
    (by dsimp [rectangularSlack]; linarith) (by linarith) hκ hθ hu
    (by dsimp [rectangularSlack]; linarith) K hK hroot f g Φ hf hg hΦ

end
end Sechstmoment

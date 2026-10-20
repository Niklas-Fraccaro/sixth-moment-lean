import SixthMoment.Numerator.U.ZeroModes.GCDMasks.AbsoluteConvergence
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.HighFrequencyEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.RatioTailMass

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000

theorem a03NativeGCD_mask_complement_absolute_budget {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ s δ χ c : ℝ}
    (hκ : 0<κ) (hs : 0<s) (hδ : 0<δ) (hχ : 0<χ) (hc : 0<c)
    (M : ℕ) (f g : ℝ→ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →
      ∀ dual positive : Bool,∀ u v : ℕ,∀ mask : ((ℕ×ℕ)×ℕ)→ℝ→ℝ,
      (∀ p,AEStronglyMeasurable (mask p) (volume.restrict (Ioi 0))) →
      (∀ p X,0<X → 0≤mask p X ∧ mask p X≤1) →
      (∀ p X,0<X → mask p X≠1 →
        (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))*T^δ≤X ∨
        T^s≤|-(T*rectangularGapSign positive*
          (Nat.gcd ((u+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)/X)| ∨
        c*T^χ≤(u+1:ℝ)*(p.1.1+1:ℝ)^2/X ∨
        c*T^χ≤(v+1:ℝ)*(p.1.2+1:ℝ)^2/X) →
      Summable (fun p : (ℕ×ℕ)×ℕ => ∫ X : ℝ in Ioi 0,
        ‖((1-mask p X:ℝ):ℂ)*a03UnrestrictedRatioGCDVStarIntegrand
          dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X‖) ∧
      (∑' p : (ℕ×ℕ)×ℕ,∫ X : ℝ in Ioi 0,
        ‖((1-mask p X:ℝ):ℂ)*a03UnrestrictedRatioGCDVStarIntegrand
          dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X‖)≤
        (|f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)| *
          C*T^(-(M:ℝ))*(Real.log T)^56/((u+1:ℝ)*(v+1:ℝ)*T^2))*
            ((40/91:ℝ)*(T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))^(7/2:ℝ)+
              (40/99:ℝ)*(T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))^(9/2:ℝ)) := by
  obtain ⟨C0,hC0,hFour⟩ := a03VStarActualBranchTimeFourier_uniform_degreeTen_log_envelope
    hΦ hSupp K hK hκ 2
  obtain ⟨Cs,hCs,hSpatial⟩ := a03VStarActualBranchTimeFourier_highSpatial_uniform_rapid
    hΦ hSupp K hK hκ hδ (M:ℝ) 2
  obtain ⟨Ch,hCh,hFrequency⟩ := a03VStarActualBranchTimeFourier_highFrequency_uniform_rapid
    hΦ hSupp K hK hκ hs (M:ℝ)
  obtain ⟨D0,hD0,hBroad⟩ := a03NativeGCDAbsoluteMajorant_summable_bound hκ
  obtain ⟨D1,hD1,hRatio⟩ := a03NativeGCDRatioTailMass_uniform_rapid hκ hχ hc M
  let Cf : ℝ := C0+Cs+Ch
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  refine ⟨Cf*(D0+D1),by positivity,?_⟩
  filter_upwards [hFour,hSpatial,hFrequency,hRatio,
    a03UnrestrictedRatioGCDVStar_absolute_convergence hΦ hSupp K hK hκ f g,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hFT hST hHT hRT hCT hT hlog
  intro σ hσ hroot α hα dual positive u v mask hmask hb hbad
  let F : ((ℕ×ℕ)×ℕ)→ℝ→ℂ := fun p =>
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2
  let Y : ℝ := T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))
  let ξ : ((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun p X =>
    -(T*rectangularGapSign positive*
      (Nat.gcd ((u+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)/X)
  let B : ((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun p X =>
    a03NativeGCDAbsoluteMajorant T σ (u+1) (v+1) Y X p
  let R : ((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun p X =>
    a03NativeGCDRatioTailMassTerm c χ T σ (u+1) (v+1) X p
  let S : ℝ→ℝ := fun X => (X^(-(3/2:ℝ))+X^(-(1/2:ℝ)))*a03NativeGCDSpatialEnvelope Y X
  let A : ℝ := |f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)|
  let Q : ℝ := A*Cf*(Real.log T)^48
  let E : ℝ := T^(-(M:ℝ))
  have hTp : 0<T := zero_lt_one.trans hT
  have hY : 0<Y := by dsimp [Y]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hC0f : C0≤Cf := by dsimp [Cf]; linarith only [hCs,hCh]
  have hCsf : Cs≤Cf := by dsimp [Cf]; linarith only [hC0,hCh]
  have hChf : Ch≤Cf := by dsimp [Cf]; linarith only [hC0,hCs]
  have hConv := hCT σ hσ hroot α hα dual positive u v
  have hDiffBound (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X) : |1-mask p X|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hb p X hX).2)]
    linarith only [(hb p X hX).1]
  have hMasked := a03NativeGCD_bounded_mask_absolute_convergence hConv.1 hConv.2.1
    (fun p X => 1-mask p X) (fun p => aestronglyMeasurable_const.sub (hmask p)) hDiffBound
  let Fd : ((ℕ×ℕ)×ℕ)→ℝ→ℂ := fun p X => ((1-mask p X:ℝ):ℂ)*F p X
  have hfd (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X) : ‖Fd p X‖≤‖F p X‖ := by
    dsimp [Fd]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hDiffBound p X hX)
  have hsB (X : ℝ) (hX : 0<X) : Summable (fun p => B p X) :=
    (hBroad T hT hlog σ hroot (u+1) (v+1) (by positivity) (by positivity) Y X hX).1
  have hsR (X : ℝ) (hX : 0<X) : Summable (fun p => R p X) :=
    (hRT σ hroot (u+1) (v+1) (by positivity) (by positivity) X hX).1
  have hsFd (X : ℝ) (hX : 0<X) : Summable (fun p : (ℕ×ℕ)×ℕ => ‖Fd p X‖) :=
    (hConv.2.2.2.1 X hX).of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hfd p X hX)
  have hbase (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X) : ‖F p X‖≤Q*B p X := by
    have hf := hFT σ hσ hroot dual Y X (ξ p X) hY hX
    have hf' : (1+|ξ p X|)^2*‖a03VStarActualBranchTimeFourier dual Φ T σ Y X (ξ p X)‖≤
        (Cf*(Real.log T)^48)*a03NativeGCDSpatialEnvelope Y X := by
      apply hf.trans
      gcongr
      exact a03NativeGCDSpatialEnvelope_nonneg Y X
    convert a03UnrestrictedRatioGCDVStarIntegrand_norm_le_majorant hTp hX
      (by positivity : 0≤Cf*(Real.log T)^48) σ α hα dual positive Φ f g u v p.1.1 p.1.2 p.2 hf' using 1
    dsimp [F,Q,A,B]
    ring
  have hsmall (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X)
      (hboundary : Y*T^δ≤X ∨ T^s≤|ξ p X|) : ‖F p X‖≤Q*E*B p X := by
    have hf' : (1+|ξ p X|)^2*‖a03VStarActualBranchTimeFourier dual Φ T σ Y X (ξ p X)‖≤
        (Cf*E*(Real.log T)^48)*a03NativeGCDSpatialEnvelope Y X := by
      rcases hboundary with hsp|hfr
      · have hh := hST σ hσ hroot dual Y X (ξ p X) hY hX hsp
        apply hh.trans
        change Cs*E*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y X≤_
        gcongr
        exact a03NativeGCDSpatialEnvelope_nonneg Y X
      · have hh := hHT σ hσ hroot dual Y X (ξ p X) hY hX hfr
        apply hh.trans
        change Ch*E*(Real.log T)^48*a03NativeGCDSpatialEnvelope Y X≤_
        gcongr
        exact a03NativeGCDSpatialEnvelope_nonneg Y X
    convert a03UnrestrictedRatioGCDVStarIntegrand_norm_le_majorant hTp hX
      (by positivity : 0≤Cf*E*(Real.log T)^48) σ α hα dual positive Φ f g u v p.1.1 p.1.2 p.2 hf' using 1
    dsimp [F,Q,A,B]
    ring
  have hpoint (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X) :
      ‖Fd p X‖≤Q*(E*B p X+S X*R p X) := by
    have hnB : 0≤B p X := a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX _
    have hnR : 0≤R p X := a03NativeGCDRatioTailMassTerm_nonneg _ _ _ _ _ _ _ _
    have hnS : 0≤S X := by
      dsimp [S]
      exact mul_nonneg (by positivity) (a03NativeGCDSpatialEnvelope_nonneg Y X)
    by_cases hm : mask p X=1
    · simp only [Fd,hm,sub_self,Complex.ofReal_zero,zero_mul,norm_zero]
      positivity
    · rcases hbad p X hX hm with hsp|hfr|hr₁|hr₂
      · exact (hfd p X hX).trans ((hsmall p X hX (Or.inl hsp)).trans (by nlinarith only [mul_nonneg hQ (mul_nonneg hnS hnR)]))
      · exact (hfd p X hX).trans ((hsmall p X hX (Or.inr hfr)).trans (by nlinarith only [mul_nonneg hQ (mul_nonneg hnS hnR)]))
      · have he : S X*R p X=B p X := by
          dsimp [S,R,B,a03NativeGCDRatioTailMassTerm,a03NativeGCDAbsoluteMajorant,a03NativeGCDPositiveIndex]
          push_cast
          simp only [hr₁,true_or,ite_true]
        rw [he]
        exact (hfd p X hX).trans ((hbase p X hX).trans (by nlinarith only [mul_nonneg hQ (mul_nonneg hE hnB)]))
      · have he : S X*R p X=B p X := by
          dsimp [S,R,B,a03NativeGCDRatioTailMassTerm,a03NativeGCDAbsoluteMajorant,a03NativeGCDPositiveIndex]
          push_cast
          simp only [hr₂,or_true,ite_true]
        rw [he]
        exact (hfd p X hX).trans ((hbase p X hX).trans (by nlinarith only [mul_nonneg hQ (mul_nonneg hE hnB)]))
  let P : ℝ→ℝ := fun X => (X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X
  let L : ℝ := A*Cf*(D0+D1)*E*(Real.log T)^56/((u+1:ℝ)*(v+1:ℝ)*T^2)
  have hsumBound (X : ℝ) (hX : 0<X) : (∑'p : (ℕ×ℕ)×ℕ,‖Fd p X‖)≤L*P X := by
    have hnS : 0≤S X := by
      dsimp [S]
      exact mul_nonneg (by positivity) (a03NativeGCDSpatialEnvelope_nonneg Y X)
    have hsmajor : Summable (fun p : (ℕ×ℕ)×ℕ => Q*(E*B p X+S X*R p X)) :=
      (((hsB X hX).mul_left E).add ((hsR X hX).mul_left (S X))).mul_left Q
    have hp := (hsFd X hX).tsum_le_tsum (fun p => hpoint p X hX) hsmajor
    rw [tsum_mul_left] at hp
    have hadd : (∑'p : (ℕ×ℕ)×ℕ,(E*B p X+S X*R p X))=
        E*(∑'p : (ℕ×ℕ)×ℕ,B p X)+S X*(∑'p : (ℕ×ℕ)×ℕ,R p X) := by
      simpa only [Pi.add_def,tsum_mul_left] using
        ((hsB X hX).mul_left E).tsum_add ((hsR X hX).mul_left (S X))
    rw [hadd] at hp
    have hB := (hBroad T hT hlog σ hroot (u+1) (v+1) (by positivity) (by positivity) Y X hX).2
    have hR := (hRT σ hroot (u+1) (v+1) (by positivity) (by positivity) X hX).2
    push_cast at hB hR
    have hlogs : (Real.log T)^4≤(Real.log T)^8 :=
      pow_le_pow_right₀ hlog (by norm_num : 4≤8)
    have hR' : S X*(∑'p : (ℕ×ℕ)×ℕ,R p X)≤
        (D1*E*(Real.log T)^8/((u+1:ℝ)*(v+1:ℝ)*T^2))*P X := by
      calc
        _≤S X*(D1*E*(Real.log T)^4*(X^2/((u+1:ℝ)*(v+1:ℝ)))*(X/T)^2) :=
          mul_le_mul_of_nonneg_left hR hnS
        _≤S X*(D1*E*(Real.log T)^8*(X^2/((u+1:ℝ)*(v+1:ℝ)))*(X/T)^2) := by gcongr
        _=_ := by
          have hx₁ : X^(-(3/2:ℝ))*X^2*X^2=X^(5/2:ℝ) := by
            rw [←Real.rpow_two,←Real.rpow_add hX,←Real.rpow_add hX]
            norm_num
          have hx₂ : X^(-(1/2:ℝ))*X^2*X^2=X^(7/2:ℝ) := by
            rw [←Real.rpow_two,←Real.rpow_add hX,←Real.rpow_add hX]
            norm_num
          dsimp [S,P]
          calc
            _=(D1*E*(Real.log T)^8/((u+1:ℝ)*(v+1:ℝ)*T^2))*
              ((X^(-(3/2:ℝ))*X^2*X^2+X^(-(1/2:ℝ))*X^2*X^2)*a03NativeGCDSpatialEnvelope Y X) := by
                field_simp
            _=_ := by rw [hx₁,hx₂]
    calc
      _≤Q*(E*(∑'p : (ℕ×ℕ)×ℕ,B p X)+S X*(∑'p : (ℕ×ℕ)×ℕ,R p X)) := hp
      _≤Q*(E*((D0*(Real.log T)^8/((u+1:ℝ)*(v+1:ℝ)*T^2))*P X)+
        (D1*E*(Real.log T)^8/((u+1:ℝ)*(v+1:ℝ)*T^2))*P X) := by
          apply mul_le_mul_of_nonneg_left _ hQ
          exact add_le_add (mul_le_mul_of_nonneg_left hB hE) hR'
      _=L*P X := by dsimp [Q,L]; ring
  have hFdInt : IntegrableOn (fun X : ℝ => ∑'p : (ℕ×ℕ)×ℕ,‖Fd p X‖) (Ioi 0) := by
    apply hConv.2.2.2.2.1.mono' (AEStronglyMeasurable.tsum (fun p => (hMasked.1 p).1.norm))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    exact (hsFd X hX).tsum_le_tsum (fun p => hfd p X hX) (hConv.2.2.2.1 X hX)
  have hExchange : (∑'p : (ℕ×ℕ)×ℕ,∫ X : ℝ in Ioi 0,‖Fd p X‖)=
      ∫ X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,‖Fd p X‖ := by
    apply integral_tsum_of_summable_integral_norm (fun p => (hMasked.1 p).norm)
    simpa only [norm_norm] using hMasked.2.1
  refine ⟨hMasked.2.1,?_⟩
  calc
    _=∫ X : ℝ in Ioi 0,∑'p : (ℕ×ℕ)×ℕ,‖Fd p X‖ := hExchange
    _≤L*((40/91:ℝ)*Y^(7/2:ℝ)+(40/99:ℝ)*Y^(9/2:ℝ)) := by
      have hInt := integral_mono_ae hFdInt ((a03NativeGCDSpatialBroadBudget_integrable hY).const_mul L)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
          exact hsumBound X hX)
      exact hInt.trans_eq (by rw [integral_const_mul,a03NativeGCDSpatialBroadBudget_integral hY])
    _=_ := by dsimp [L,A,Y,E]; ring

end
end SixthMoment

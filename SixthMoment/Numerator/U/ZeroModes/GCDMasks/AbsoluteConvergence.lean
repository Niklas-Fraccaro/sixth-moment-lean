import Mathlib.MeasureTheory.Integral.DominatedConvergence
import SixthMoment.Numerator.U.Replacement.VStar.ActualBranchTimeFourierEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.BroadDensityBounds
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.SpatialBroadBudget
import SixthMoment.Numerator.U.ZeroModes.GCDMasks.TripleAbsoluteMass
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.Measurability

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDPositiveIndex (p : (ℕ×ℕ)×ℕ) : (ℕ×ℕ)×ℕ :=
  ((p.1.1+1,p.1.2+1),p.2)

theorem a03NativeGCDPositiveIndex_injective :
    Function.Injective a03NativeGCDPositiveIndex := by
  intro p q h
  apply Prod.ext
  · apply Prod.ext
    · exact Nat.add_right_cancel (congrArg (fun r : (ℕ×ℕ)×ℕ => r.1.1) h)
    · exact Nat.add_right_cancel (congrArg (fun r : (ℕ×ℕ)×ℕ => r.1.2) h)
  · simpa only [a03NativeGCDPositiveIndex] using congrArg (fun r : (ℕ×ℕ)×ℕ => r.2) h

theorem a03ActualRatioPartition_measurable (T : ℝ) (σ : MomentShifts) :
    Measurable (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ))) := by
  let G := a03ZeroModeRatioWeight (rawMomentShifts T σ)
  have hG : Measurable G := (a03ZeroModeRatioWeight_differentiable _).continuous.measurable
  have hz : Measurable (fun p : ℝ×ℝ => (1:ℂ)+(p.2:ℂ)*I) := by fun_prop
  have hx : Measurable (fun p : ℝ×ℝ => (p.1:ℂ)) := by fun_prop
  have hk : Measurable (fun p : ℝ×ℝ => a03ZeroModeRatioKernel G p.1 ((1:ℂ)+(p.2:ℂ)*I)) := by
    unfold a03ZeroModeRatioKernel
    exact ((hG.comp hz).mul (a03MeasurableCPow hx hz.neg)).div hz
  unfold a03ZeroModeRatioPartition verticalIntegral
  exact measurable_const.mul hk.stronglyMeasurable.integral_prod_right'.measurable

theorem a03UnrestrictedRatioGCDVStarIntegrand_measurable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (dual positive : Bool) (u v m n h : ℕ) :
    Measurable (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h) := by
  have hR := a03ActualRatioPartition_measurable T σ
  have hV := a03VStar_measurable (polarPoleKiller T σ)
    (polarPoleKiller_differentiable T σ).continuous.measurable
  have hP := (a03RatioLeadingBranchProfile_contDiff hΦ hSupp hT σ dual).continuous.measurable
  have harg : Measurable (fun p : ℝ×ℝ => p.1^2/
      ((u+1:ℝ)*(v+1:ℝ)*(T*p.2)^2)) := by fun_prop
  have he : Measurable (fun p : ℝ×ℝ => Complex.exp
      (((-(T*rectangularGapSign positive*
        (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℝ)*(h+1)/p.1):ℝ):ℂ)*I*(p.2:ℂ))) := by
    fun_prop
  have hi := ((he.mul (hP.comp measurable_snd)).mul (hV.comp harg)).stronglyMeasurable.integral_prod_right' (ν:=volume) |>.measurable
  have hx : Measurable (fun X : ℝ => (X:ℂ)^(-1-α 1-α 3)) :=
    a03MeasurableCPow Complex.measurable_ofReal measurable_const
  have hr₁ : Measurable (fun X : ℝ => a03ZeroModeRatioPartition
      (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)) :=
    hR.comp (by fun_prop)
  have hr₂ : Measurable (fun X : ℝ => a03ZeroModeRatioPartition
      (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X)) :=
    hR.comp (by fun_prop)
  push_cast at hi
  unfold a03UnrestrictedRatioGCDVStarIntegrand
  push_cast
  exact (((measurable_const.mul hx).mul (hr₁.mul hr₂)).mul hi)

def a03NativeGCDAbsoluteMajorant (T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (Y X : ℝ) (p : (ℕ×ℕ)×ℕ) : ℝ :=
  (X^(-(3/2:ℝ))+X^(-(1/2:ℝ)))*a03NativeGCDSpatialEnvelope Y X*
    a03NativeGCDTripleAbsoluteMassTerm T σ a b X (a03NativeGCDPositiveIndex p)

theorem a03NativeGCDAbsoluteMajorant_nonneg (T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (Y X : ℝ) (hX : 0<X) (p : (ℕ×ℕ)×ℕ) :
    0≤a03NativeGCDAbsoluteMajorant T σ a b Y X p := by
  unfold a03NativeGCDAbsoluteMajorant
  exact mul_nonneg (mul_nonneg (by positivity) (a03NativeGCDSpatialEnvelope_nonneg _ _))
    (a03NativeGCDTripleAbsoluteMassTerm_nonneg _ _ _ _ _ _)

theorem a03NativeGCDAbsoluteMajorant_measurable (T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (Y : ℝ) (p : (ℕ×ℕ)×ℕ) :
    Measurable (fun X : ℝ => a03NativeGCDAbsoluteMajorant T σ a b Y X p) := by
  have hR := a03ActualRatioPartition_measurable T σ
  have hr₁ : Measurable (fun X : ℝ => ‖a03ZeroModeRatioPartition
      (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((a:ℝ)*(p.1.1+1:ℝ)^2/X)‖) :=
    (hR.comp (by fun_prop)).norm
  have hr₂ : Measurable (fun X : ℝ => ‖a03ZeroModeRatioPartition
      (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((b:ℝ)*(p.1.2+1:ℝ)^2/X)‖) :=
    (hR.comp (by fun_prop)).norm
  unfold a03NativeGCDAbsoluteMajorant a03NativeGCDTripleAbsoluteMassTerm
    a03NativeGCDPositiveIndex a03RatioBroadDirichletTerm a03NativeGCDFrequencyMassTerm
    a03NativeGCDSpatialEnvelope
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
  have hbase : Measurable (fun X : ℝ =>
      (X^(-(3/2:ℝ))+X^(-(1/2:ℝ)))*min 1 ((Y/X)^10)) := by fun_prop
  have hfreq : Measurable (fun X : ℝ =>
      (Nat.gcd (a*(p.1.1+1)) (b*(p.1.2+1)):ℝ)/
        (1+T*(Nat.gcd (a*(p.1.1+1)) (b*(p.1.2+1)):ℝ)*((p.2:ℝ)+1)/X)^2) := by fun_prop
  have hall := hbase.mul (((hr₁.const_mul ((p.1.1+1:ℝ)^(-(1/2:ℝ)))).mul
    (hr₂.const_mul ((p.1.2+1:ℝ)^(-(1/2:ℝ))))).mul hfreq)
  convert hall using 1
  funext X
  push_cast
  rfl

theorem a03NativeGCDAbsoluteMajorant_summable_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ a b : ℕ,0<a → 0<b → ∀ Y X : ℝ,0<X →
      Summable (a03NativeGCDAbsoluteMajorant T σ a b Y X) ∧
        (∑' p : (ℕ×ℕ)×ℕ,a03NativeGCDAbsoluteMajorant T σ a b Y X p)≤
          (C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))*
            ((X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X) := by
  obtain ⟨C,hC,hmass⟩ := a03NativeGCDTripleAbsoluteMass_uniform_bound hκ
  refine ⟨C,hC,?_⟩
  intro T hT hlog σ hroot a b ha hb Y X hX
  obtain ⟨hs,hm⟩ := hmass T hT hlog σ hroot a b ha hb X hX
  have hp := hs.comp_injective a03NativeGCDPositiveIndex_injective
  have hsum : (∑' p : (ℕ×ℕ)×ℕ,
      a03NativeGCDTripleAbsoluteMassTerm T σ a b X (a03NativeGCDPositiveIndex p))≤
        ∑' p : (ℕ×ℕ)×ℕ,a03NativeGCDTripleAbsoluteMassTerm T σ a b X p := by
    exact hp.tsum_le_tsum_of_inj a03NativeGCDPositiveIndex a03NativeGCDPositiveIndex_injective
      (fun p _ => a03NativeGCDTripleAbsoluteMassTerm_nonneg _ _ _ _ _ p)
      (fun _ => le_rfl) hs
  refine ⟨hp.mul_left _,?_⟩
  unfold a03NativeGCDAbsoluteMajorant
  rw [tsum_mul_left]
  have hb' := mul_le_mul_of_nonneg_left (hsum.trans hm)
    (mul_nonneg (by positivity : 0≤X^(-(3/2:ℝ))+X^(-(1/2:ℝ)))
      (a03NativeGCDSpatialEnvelope_nonneg Y X))
  apply hb'.trans_eq
  have hx₁ : X^(-(3/2:ℝ))*X^2*X^2=X^(5/2:ℝ) := by
    rw [←Real.rpow_two,←Real.rpow_add hX,←Real.rpow_add hX]
    norm_num
  have hx₂ : X^(-(1/2:ℝ))*X^2*X^2=X^(7/2:ℝ) := by
    rw [←Real.rpow_two,←Real.rpow_add hX,←Real.rpow_add hX]
    norm_num
  calc
    _=(C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))*
      ((X^(-(3/2:ℝ))*X^2*X^2+X^(-(1/2:ℝ))*X^2*X^2)*
        a03NativeGCDSpatialEnvelope Y X) := by ring
    _=_ := by rw [hx₁,hx₂]

theorem a03NativeGCDAbsoluteMajorant_sum_integrable {κ : ℝ} (hκ : 0<κ)
    {T : ℝ} (hT : 1<T) (hlog : 1≤Real.log T) (σ : MomentShifts)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,
      a03NativeGCDAbsoluteMajorant T σ a b Y X p) (Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := a03NativeGCDAbsoluteMajorant_summable_bound hκ
  have hm : AEStronglyMeasurable (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,
      a03NativeGCDAbsoluteMajorant T σ a b Y X p) (volume.restrict (Ioi 0)) :=
    (StronglyMeasurable.tsum (fun p =>
      (a03NativeGCDAbsoluteMajorant_measurable T σ a b Y p).stronglyMeasurable)).aestronglyMeasurable
  apply ((a03NativeGCDSpatialBroadBudget_integrable hY).const_mul
    (C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  rw [Real.norm_of_nonneg (tsum_nonneg (a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX))]
  exact (hbound T hT hlog σ hroot a b ha hb Y X hX).2

theorem a03NativeGCDAbsoluteMajorant_integral_uniform_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ a b : ℕ,0<a → 0<b → ∀ Y : ℝ,0<Y →
      (∫ X : ℝ in Ioi 0,∑' p : (ℕ×ℕ)×ℕ,
        a03NativeGCDAbsoluteMajorant T σ a b Y X p)≤
          (C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))*
            ((40/91:ℝ)*Y^(7/2:ℝ)+(40/99:ℝ)*Y^(9/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := a03NativeGCDAbsoluteMajorant_summable_bound hκ
  refine ⟨C,hC,?_⟩
  intro T hT hlog σ hroot a b ha hb Y hY
  have hM := a03NativeGCDAbsoluteMajorant_sum_integrable hκ hT hlog σ hroot ha hb hY
  have hB := (a03NativeGCDSpatialBroadBudget_integrable hY).const_mul
    (C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))
  calc
    _≤∫ X : ℝ in Ioi 0,(C*(Real.log T)^8/((a:ℝ)*(b:ℝ)*T^2))*
        ((X^(5/2:ℝ)+X^(7/2:ℝ))*a03NativeGCDSpatialEnvelope Y X) := by
      apply integral_mono_ae hM hB
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
      exact (hbound T hT hlog σ hroot a b ha hb Y X hX).2
    _=_ := by rw [integral_const_mul,a03NativeGCDSpatialBroadBudget_integral hY]

theorem a03UnrestrictedRatioGCDVStarIntegrand_eq_timeFourier
    (dual positive : Bool) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (f g : ℝ→ℝ) (u v m n h : ℕ) (X : ℝ) :
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h X=
      (f (Real.log (u+1:ℝ)/Real.log T):ℂ)*(g (Real.log (v+1:ℝ)/Real.log T):ℂ)*
        (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℂ)*
          a03NativeGCDBroadDensity α (u+1) (v+1) (m+1) (n+1) X*
            (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)*
              a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X))*
                a03VStarActualBranchTimeFourier dual Φ T σ
                  (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X
                  (-(T*rectangularGapSign positive*
                    (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℝ)*(h+1)/X)) := by
  rw [a03UnrestrictedRatioGCDVStarIntegrand_eq_broadDensity]
  congr 1
  unfold a03VStarActualBranchTimeFourier
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    have he : (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ)))^2*t^2=
        (u+1:ℝ)*(v+1:ℝ)*(T*t)^2 := by
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      ring
    rw [he]

theorem a03UnrestrictedRatioGCDVStarIntegrand_norm_le_majorant
    {T X C : ℝ} (hT : 0<T) (hX : 0<X) (hC : 0≤C)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤1/4)
    (dual positive : Bool) (Φ : ℝ→ℂ) (f g : ℝ→ℝ) (u v m n h : ℕ)
    (hFour : (1+|-(T*rectangularGapSign positive*
        (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℝ)*(h+1)/X)|)^2*
      ‖a03VStarActualBranchTimeFourier dual Φ T σ
        (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X
          (-(T*rectangularGapSign positive*
            (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1)):ℝ)*(h+1)/X))‖≤
        C*a03NativeGCDSpatialEnvelope (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X) :
    ‖a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v m n h X‖≤
      (|f (Real.log (u+1:ℝ)/Real.log T)| *|g (Real.log (v+1:ℝ)/Real.log T)| *C)*
        a03NativeGCDAbsoluteMajorant T σ (u+1) (v+1)
          (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X ((m,n),h) := by
  let d : ℝ := Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1))
  let Y : ℝ := T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))
  let ξ : ℝ := -(T*rectangularGapSign positive*d*(h+1)/X)
  have hd : 1≤d := by
    dsimp [d]
    exact_mod_cast Nat.gcd_pos_of_pos_left ((v+1)*(n+1)) (by positivity : 0<(u+1)*(m+1))
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hξ : |ξ|=T*d*(h+1)/X := by
    dsimp [ξ]
    rw [abs_neg,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos hT,abs_of_pos hd0,
      abs_of_pos (by positivity : 0<(h:ℝ)+1),abs_of_pos hX]
    cases positive <;> norm_num [rectangularGapSign]
  have hden : 0<(1+T*d*(h+1)/X)^2 := by positivity
  change (1+|ξ|)^2*‖a03VStarActualBranchTimeFourier dual Φ T σ Y X ξ‖≤
    C*a03NativeGCDSpatialEnvelope Y X at hFour
  rw [hξ] at hFour
  have hf : d*‖a03VStarActualBranchTimeFourier dual Φ T σ Y X ξ‖≤
      C*a03NativeGCDSpatialEnvelope Y X*a03NativeGCDFrequencyMassTerm T X d h := by
    have hh : ‖a03VStarActualBranchTimeFourier dual Φ T σ Y X ξ‖≤
        C*a03NativeGCDSpatialEnvelope Y X/(1+T*d*(h+1)/X)^2 := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_comm] using hFour
    calc
      _≤d*(C*a03NativeGCDSpatialEnvelope Y X/(1+T*d*(h+1)/X)^2) :=
        mul_le_mul_of_nonneg_left hh hd0.le
      _=_ := by unfold a03NativeGCDFrequencyMassTerm; ring
  have hD := a03NativeGCDBroadDensity_norm_bound α hα
    (by positivity : 0<u+1) (by positivity : 0<v+1)
      (by positivity : 0<m+1) (by positivity : 0<n+1) hX
  push_cast at hD
  rw [a03UnrestrictedRatioGCDVStarIntegrand_eq_timeFourier]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
  change _≤_
  let W : ℝ := |f (Real.log (u+1:ℝ)/Real.log T)| * |g (Real.log (v+1:ℝ)/Real.log T)| *
    ‖a03NativeGCDBroadDensity α (u+1) (v+1) (m+1) (n+1) X‖ *
      (‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)‖ *
        ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X)‖)
  have hW : 0≤W := by dsimp [W]; positivity
  have hcalc := mul_le_mul_of_nonneg_left hf hW

  calc
    _=(|f (Real.log (u+1:ℝ)/Real.log T)| *|g (Real.log (v+1:ℝ)/Real.log T)| *
      ‖a03NativeGCDBroadDensity α (u+1) (v+1) (m+1) (n+1) X‖*
        (‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)‖*
          ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X)‖))*
            (d*‖a03VStarActualBranchTimeFourier dual Φ T σ Y X ξ‖) := by
      dsimp [d,Y,ξ]
      ring
    _≤_ := hcalc
    _≤_ := by
      unfold a03NativeGCDAbsoluteMajorant a03NativeGCDTripleAbsoluteMassTerm
        a03NativeGCDPositiveIndex a03RatioBroadDirichletTerm
      simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]
      push_cast
      dsimp only [Prod.fst,Prod.snd,Y,d]
      let Z : ℝ := |f (Real.log (u+1:ℝ)/Real.log T)| *|g (Real.log (v+1:ℝ)/Real.log T)| *
        C*a03NativeGCDSpatialEnvelope (T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))) X*
          (‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((u+1:ℝ)*(m+1:ℝ)^2/X)‖*
            ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((v+1:ℝ)*(n+1:ℝ)^2/X)‖)*
              a03NativeGCDFrequencyMassTerm T X (Nat.gcd ((u+1)*(m+1)) ((v+1)*(n+1))) h
      have hZ : 0≤Z := by
        dsimp [Z]
        unfold a03NativeGCDFrequencyMassTerm a03NativeGCDSpatialEnvelope
        positivity
      convert mul_le_mul_of_nonneg_left hD hZ using 1 <;> dsimp [Z] <;> ring

theorem a03UnrestrictedRatioGCDVStar_absolute_convergence {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) {κ : ℝ} (hκ : 0<κ)
    (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/4) →
      ∀ dual positive : Bool,∀ u v : ℕ,
      (∀ p : (ℕ×ℕ)×ℕ,IntegrableOn
        (a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2) (Ioi 0)) ∧
      Summable (fun p : (ℕ×ℕ)×ℕ => ∫ X : ℝ in Ioi 0,
        ‖a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X‖) ∧
      Summable (fun p : (ℕ×ℕ)×ℕ => ∫ X : ℝ in Ioi 0,
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X) ∧
      (∀ X : ℝ,0<X → Summable (fun p : (ℕ×ℕ)×ℕ =>
        ‖a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X‖)) ∧
      IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,
        ‖a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X‖) (Ioi 0) ∧
      IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X) (Ioi 0) ∧
      (∑' p : (ℕ×ℕ)×ℕ,∫ X : ℝ in Ioi 0,
        a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X)=
        ∫ X : ℝ in Ioi 0,∑' p : (ℕ×ℕ)×ℕ,
          a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2 X := by
  obtain ⟨C,hC,hFour⟩ := a03VStarActualBranchTimeFourier_uniform_degreeTen_log_envelope
    hΦ hSupp K hK hκ 2
  obtain ⟨D,hD,hMajorant⟩ := a03NativeGCDAbsoluteMajorant_summable_bound hκ
  filter_upwards [hFour,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hFT hT hlog
  intro σ hσ hroot α hα dual positive u v
  let F : ((ℕ×ℕ)×ℕ)→ℝ→ℂ := fun p =>
    a03UnrestrictedRatioGCDVStarIntegrand dual positive Φ T σ α f g u v p.1.1 p.1.2 p.2
  let Y : ℝ := T*Real.sqrt ((u+1:ℝ)*(v+1:ℝ))
  let M : ((ℕ×ℕ)×ℕ)→ℝ→ℝ := fun p X =>
    a03NativeGCDAbsoluteMajorant T σ (u+1) (v+1) Y X p
  let Q : ℝ := |f (Real.log (u+1:ℝ)/Real.log T)| *|g (Real.log (v+1:ℝ)/Real.log T)| *
    (C*(Real.log T)^48)
  have hTp : 0<T := zero_lt_one.trans hT
  have hY : 0<Y := by dsimp [Y]; positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hFM (p : (ℕ×ℕ)×ℕ) : AEStronglyMeasurable (F p) (volume.restrict (Ioi 0)) :=
    (a03UnrestrictedRatioGCDVStarIntegrand_measurable hΦ hSupp hTp σ α f g
      dual positive u v p.1.1 p.1.2 p.2).aestronglyMeasurable
  have hMS (X : ℝ) (hX : 0<X) : Summable (fun p => M p X) :=
    (hMajorant T hT hlog σ hroot (u+1) (v+1) (by positivity) (by positivity) Y X hX).1
  have hMI : IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,M p X) (Ioi 0) :=
    a03NativeGCDAbsoluteMajorant_sum_integrable hκ hT hlog σ hroot
      (by positivity) (by positivity) hY
  have hbound (p : (ℕ×ℕ)×ℕ) (X : ℝ) (hX : 0<X) : ‖F p X‖≤Q*M p X := by
    apply a03UnrestrictedRatioGCDVStarIntegrand_norm_le_majorant hTp hX
      (by positivity : 0≤C*(Real.log T)^48) σ α hα dual positive Φ f g u v p.1.1 p.1.2 p.2
    exact hFT σ hσ hroot dual Y X
      (-(T*rectangularGapSign positive*
        (Nat.gcd ((u+1)*(p.1.1+1)) ((v+1)*(p.1.2+1)):ℝ)*(p.2+1)/X)) hY hX
  have hNS (X : ℝ) (hX : 0<X) : Summable (fun p : (ℕ×ℕ)×ℕ => ‖F p X‖) :=
    ((hMS X hX).mul_left Q).of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hbound p X hX)
  have hFI (p : (ℕ×ℕ)×ℕ) : IntegrableOn (F p) (Ioi 0) := by
    apply (hMI.const_mul Q).mono' (hFM p)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact (hbound p X hX).trans (mul_le_mul_of_nonneg_left
      ((hMS X hX).le_tsum p (fun q _ => a03NativeGCDAbsoluteMajorant_nonneg _ _ _ _ _ _ hX q)) hQ)
  have hNMI : IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,‖F p X‖) (Ioi 0) := by
    have hm : AEStronglyMeasurable (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,‖F p X‖)
        (volume.restrict (Ioi 0)) := by
      apply AEStronglyMeasurable.tsum
      exact fun p => (hFM p).norm
    apply (hMI.const_mul Q).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    have hh := (hNS X hX).tsum_le_tsum (fun p => hbound p X hX) ((hMS X hX).mul_left Q)
    simpa only [tsum_mul_left] using hh
  have hSI : IntegrableOn (fun X : ℝ => ∑' p : (ℕ×ℕ)×ℕ,F p X) (Ioi 0) := by
    apply hNMI.mono' (AEStronglyMeasurable.tsum hFM)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact norm_tsum_le_tsum_norm (hNS X hX)
  have hNormSum : Summable (fun p : (ℕ×ℕ)×ℕ => ∫ X : ℝ in Ioi 0,‖F p X‖) := by
    have h := hasSum_integral_of_dominated_convergence (μ:=volume.restrict (Ioi 0))
      (fun p X => Q*M p X) (fun p => (hFM p).norm)
      (fun p => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
        simpa only [norm_norm] using hbound p X hX)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
        exact (hMS X hX).mul_left Q)
      (by
        simp only [tsum_mul_left]
        exact hMI.const_mul Q)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
        exact (hNS X hX).hasSum)
    exact h.summable
  have hComplexSum := hasSum_integral_of_summable_integral_norm hFI hNormSum
  exact ⟨hFI,hNormSum,hComplexSum.summable,hNS,hNMI,hSI,hComplexSum.tsum_eq⟩

theorem a03NativeGCD_bounded_mask_absolute_convergence
    {F : ((ℕ×ℕ)×ℕ)→ℝ→ℂ}
    (hFI : ∀ p,IntegrableOn (F p) (Ioi 0))
    (hNormSum : Summable (fun p => ∫ X : ℝ in Ioi 0,‖F p X‖))
    (mask : ((ℕ×ℕ)×ℕ)→ℝ→ℝ)
    (hmask : ∀ p,AEStronglyMeasurable (mask p) (volume.restrict (Ioi 0)))
    (hbound : ∀ p X,0<X → |mask p X|≤1) :
    (∀ p,IntegrableOn (fun X => (mask p X:ℂ)*F p X) (Ioi 0)) ∧
    Summable (fun p => ∫ X : ℝ in Ioi 0,‖(mask p X:ℂ)*F p X‖) ∧
    Summable (fun p => ∫ X : ℝ in Ioi 0,(mask p X:ℂ)*F p X) ∧
    (∑' p,∫ X : ℝ in Ioi 0,(mask p X:ℂ)*F p X)=
      ∫ X : ℝ in Ioi 0,∑' p,(mask p X:ℂ)*F p X := by
  have hm (p : (ℕ×ℕ)×ℕ) : AEStronglyMeasurable
      (fun X => (mask p X:ℂ)*F p X) (volume.restrict (Ioi 0)) :=
    ((Complex.ofRealCLM.continuous.comp_aestronglyMeasurable (hmask p))).mul (hFI p).1
  have hn (p : (ℕ×ℕ)×ℕ) : ∀ᵐ X ∂volume.restrict (Ioi 0),
      ‖(mask p X:ℂ)*F p X‖≤‖F p X‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound p X hX)
  have hI (p : (ℕ×ℕ)×ℕ) : IntegrableOn
      (fun X => (mask p X:ℂ)*F p X) (Ioi 0) := (hFI p).norm.mono' (hm p) (hn p)
  have hS : Summable (fun p : (ℕ×ℕ)×ℕ =>
      ∫ X : ℝ in Ioi 0,‖(mask p X:ℂ)*F p X‖) :=
    hNormSum.of_nonneg_of_le (fun p => integral_nonneg (fun _ => norm_nonneg _))
      (fun p => integral_mono_ae (hI p).norm (hFI p).norm (hn p))
  have h := hasSum_integral_of_summable_integral_norm hI hS
  exact ⟨hI,hS,h.summable,h.tsum_eq⟩

end
end SixthMoment

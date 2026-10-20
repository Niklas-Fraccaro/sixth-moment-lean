import SixthMoment.Numerator.U.Bounds.SharpGammaSourceBudget

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SharpSourceScale (a b ε : ℝ) : ℝ :=
  min ε (min (rectangularSlack a b) (1/16))

theorem a03_actual_finite_offdiagonal_Gamma_sub_retained_GCD_uniform_sharp
    (hinput : SeparatedQuadraticInput) {a b ε c : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε)
    (hc : 0<c) (hcsmall : c≤a03SharpSourceScale a b ε/128)
    (K : Set MomentShifts) (hK : IsCompact K) {κ θ : ℝ} (hκ : 0<κ) (hθ : 0<θ)
    (hroot : ∀σ∈K,∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ S U : ℝ,0<S ∧ S≤a03SharpSourceScale a b ε/128 ∧
      0<U ∧ U≤a03SharpSourceScale a b ε/128 ∧
      ∀ s u : ℝ,0<s → s≤S → 0<u → u≤U → ∃ C : ℝ,0≤C ∧
      ∀ᶠ T : ℝ in atTop,∀σ∈K,
      ‖(∑dual : Bool,a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ)-
        ∑dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
          T a b s u (a03SharpSourceScale a b ε/1024) σ f g‖≤
        C*(T^rectangularFirstExponent a b ε+T^rectangularSecondExponent a b ε) := by
  let λ := a03SharpSourceScale a b ε
  have hλ : 0<λ := lt_min hε (lt_min (rectangular_slack_bounds hab hlen).1 (by norm_num))
  have hλε : λ≤ε := min_le_left _ _
  have hλslack : λ≤rectangularSlack a b := (min_le_right _ _).trans (min_le_left _ _)
  have hλcap : λ≤1/16 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : 0≤b := ha.trans hab
  have hc1 : c≤1 := by change c≤λ/128 at hcsmall; linarith
  have he : 12*c<λ/8 := by change c≤λ/128 at hcsmall; linarith
  have hker : 2*c<λ/16 := by change c≤λ/128 at hcsmall; linarith
  have hsrc : 0<λ/1024 := by positivity
  have hLoss : 4*(λ/1024)+λ/8<rectangularSlack a b := by linarith
  have hcap : 0<λ/128 := by positivity
  have hδ : 0<λ/8 := by positivity
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  have hσR (σ : MomentShifts) (hσ : σ∈K) (j : Fin 4) : ‖σ j‖≤R :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨Sf,Uf,hSf,_hSf2,_hSf8,hSfλ,hUf,_hUf8,hUfλ,hFalse⟩ :=
    a03_actual_ratio_native_sub_Gamma_mass_budget_smaller false hinput ha hab hlen hsrc f g hf hg
      hΦc hΦs hc hc1 he hκ hθ.le hR hLoss (λ/128) (λ/128) hcap hcap
  obtain ⟨St,Ut,hSt,_hSt2,_hSt8,hStλ,hUt,_hUt8,hUtλ,hTrue⟩ :=
    a03_actual_ratio_native_sub_Gamma_mass_budget_smaller true hinput ha hab hlen hsrc f g hf hg
      hΦc hΦs hc hc1 he hκ hθ.le hR hLoss (λ/128) (λ/128) hcap hcap
  let S := min Sf St
  let U := min Uf Ut
  have hS : 0<S := lt_min hSf hSt
  have hU : 0<U := lt_min hUf hUt
  have hScap : S≤λ/128 := (min_le_left _ _).trans hSfλ
  have hUcap : U≤λ/128 := (min_le_left _ _).trans hUfλ
  refine ⟨S,U,hS,hScap,hU,hUcap,?_⟩
  intro s u hs hsS hu huU
  have hsλ : s≤λ/128 := hsS.trans hScap
  have huλ : u≤λ/128 := huU.trans hUcap
  have hs8 : s≤1/8 := by linarith
  have hs2 : s<1/2 := by linarith
  have hs1 : s≤1 := by linarith
  have hu8 : u≤1/8 := by linarith
  obtain ⟨CF,hCF,hF⟩ := hFalse s u hs (hsS.trans (min_le_left _ _)) hu (huU.trans (min_le_left _ _))
  obtain ⟨CT,hCT,hT⟩ := hTrue s u hs (hsS.trans (min_le_right _ _)) hu (huU.trans (min_le_right _ _))
  have hP : 1/2+a+b+s/2+4*(λ/1024)+λ/8+λ/8≤rectangularFirstExponent a b ε := by
    unfold rectangularFirstExponent
    linarith
  have hQ : 3/4+3*a/8+5*b/8+3*s/4+u/4+4*(λ/1024)+λ/8+λ/8≤rectangularSecondExponent a b ε := by
    unfold rectangularSecondExponent
    linarith
  obtain ⟨CM,hCM,hMajorant⟩ := a03_actual_soft_source_restored_sharp_power
    ha hab hlen hs.le hs8 hu hu8 hsrc.le hθ.le hδ hP hQ f g hf hg
  have hGammaExp : (a+b)/2+3*s+u/2+λ/16+λ/8≤rectangularFirstExponent a b ε := by
    unfold rectangularFirstExponent
    linarith
  obtain ⟨CG,hCG,hGamma⟩ := a03_actual_ratio_Gamma_zero_sub_linear_uniform_power
    ha hb hs.le (by linarith : s<1) f g hf hg hΦc hΦs hc hc1 hker hκ hθ.le hR hu hδ hGammaExp (λ/1024)
  obtain ⟨CB,hCB,hBad⟩ := a03_actual_ratio_bad_source_moment_uniform_rapid ha hab hlen hs.le hs2.le hu hsrc
    hf hg hΦ hc hc1 hκ hθ.le hR 0
  obtain ⟨CR,hCR,hFar⟩ := a03_actual_source_far_residual_contour_uniform_rapid hf hg hΦ hc hc1 hu
    hκ hθ.le hR hs hs1 0
  obtain ⟨CL,hCL,hLinear⟩ := a03_actual_four_ratio_linear_core_sub_retained_GCD_uniform_rapid
    ha hb hs.le hu f g Φ hf hg hΦ hc hθ hκ hR (λ/1024) 0
  let CS := (CF+CT)*CM
  let CA := CS+CG+CB
  have hCS : 0≤CS := by dsimp [CS]; positivity
  have hCA : 0≤CA := by dsimp [CA]; positivity
  refine ⟨8*CA+4*CR+CL,by positivity,?_⟩
  filter_upwards [hF,hT,hMajorant,hGamma,hBad,hFar,hLinear,
    a03_actual_source_finite_values_integrableOn false hΦc hΦs hc hc1
      (e:=λ/8) (by linarith : 4*c<λ/8) hκ hθ.le hR hs2 a b u f g,
    a03_actual_source_finite_values_integrableOn true hΦc hΦs hc hc1
      (e:=λ/8) (by linarith : 4*c<λ/8) hκ hθ.le hR hs2 a b u f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_gt_atTop (1:ℝ)] with T hFT hTT hMT hGT hBT hRT hLT hIf hIt hraw hlog hT1
  intro σ hσ
  have hrootσ := hroot σ hσ
  have hσB : ∀ j,‖σ j‖≤R := hσR σ hσ
  have hrawσ := hraw σ hσB
  let E := T^rectangularFirstExponent a b ε+T^rectangularSecondExponent a b ε
  have hTp : 0<T := zero_lt_one.trans hT1
  have hEp : 0≤E := by dsimp [E]; positivity
  have hE1 : 1≤E := by
    have hp : 0≤rectangularFirstExponent a b ε := by unfold rectangularFirstExponent; linarith
    exact (Real.one_le_rpow hT1.le hp).trans (le_add_of_nonneg_right (Real.rpow_nonneg hTp.le _))
  have hPE : T^rectangularFirstExponent a b ε≤E :=
    le_add_of_nonneg_right (Real.rpow_nonneg hTp.le _)
  have hSource (dual : Bool) (α : MomentShifts) (hαscale : ∀ j,‖α j‖≤R/Real.log T) :
      ‖a03ActualRatioSourceValueMoment false dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g-
        a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g‖≤CS*E := by
    have hMass : T^(λ/8)*a03ActualSoftSourceGlobalMajorant T a b s u (λ/1024) θ f g≤CM*E := hMT
    cases dual
    · apply (hFT σ α hσB hαscale hrootσ).trans
      calc
        _=CF*(T^(λ/8)*a03ActualSoftSourceGlobalMajorant T a b s u (λ/1024) θ f g) := by ring
        _≤CF*(CM*E) := mul_le_mul_of_nonneg_left hMass hCF
        _≤CS*E := by dsimp [CS]; nlinarith only [mul_nonneg hCT (mul_nonneg hCM hEp)]
    · apply (hTT σ α hσB hαscale hrootσ).trans
      calc
        _=CT*(T^(λ/8)*a03ActualSoftSourceGlobalMajorant T a b s u (λ/1024) θ f g) := by ring
        _≤CT*(CM*E) := mul_le_mul_of_nonneg_left hMass hCT
        _≤CS*E := by dsimp [CS]; nlinarith only [mul_nonneg hCF (mul_nonneg hCM hEp)]
  have hsingle (dual m n : Bool) :
      ‖a03ActualRatioTimeMoment false false dual (a03ZeroModeRatioWeight (rawMomentShifts T σ))
          c T a b s u θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ-
        a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤CA*E := by
    let α := a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)
    have hα := a03SourceChamberShifts_norm_le_quarter dual σ hrawσ m n
    have hαscale := a03SourceChamberShifts_norm_le_raw_scale (zero_lt_one.trans_le hlog) dual σ hσB m n
    have hgood := hSource dual α hαscale
    have hgamma := hGT σ α hσB hα hαscale hrootσ dual
    have hbad := (hBT σ α hσB hα hrootσ dual).2
    simp only [neg_zero,Real.rpow_zero,mul_one] at hbad
    have heq := (a03ActualRatioTimeMoment_eq_source_add_bad hc hT1 dual f g Φ hf hg hΦ σ α hα hrawσ
      s u (λ/1024) θ).2.2
    rw [heq]
    have halg (X Y Z W : ℂ) : X+Y-W=(X-Z)+(Z-W)+Y := by ring
    rw [halg _ _ (a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g)]
    calc
      _≤(‖a03ActualRatioSourceValueMoment false dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g-
        a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g‖+
        ‖a03ActualRatioSourceValueMoment true dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g-
          a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ α f g‖)+
        ‖a03ActualRatioBadSourceTimeMoment dual c T a b s u (λ/1024) θ σ α f g Φ‖ :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _≤CS*E+CG*T^rectangularFirstExponent a b ε+CB := add_le_add (add_le_add hgood hgamma) hbad
      _≤CS*E+CG*E+CB*E := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hPE hCG))
        (le_mul_of_one_le_right hCB hE1)
      _=CA*E := by dsimp [CA]; ring
  have hconst : ‖(1/(2*Real.pi):ℂ)‖≤1 := by
    rw [norm_div,norm_one,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact (div_le_one (by positivity : (0:ℝ)<2*Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hdual (dual : Bool) :
      ‖a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u (λ/1024) θ σ f g Φ‖≤(4*CA+2*CR)*E := by
    have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
      cases dual
      · exact hrawσ
      · exact bblrSixShifts_norm_le _ hrawσ 1
    have hfarT (positive : Bool) := hRT σ (a03SourceShifts dual T σ) hσB hα hrootσ dual positive
    have hInt : IntegrableOn (fun v => a03ActualSourceFiniteValue false dual (fun x => (Φ x:ℂ))
        c T a b s u v σ f g) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
      cases dual
      · exact hIf σ hσB hrootσ false
      · exact hIt σ hσB hrootσ false
    rw [a03ActualFiniteOffdiagonalGammaMoment_eq_source_add_far hT1 dual c s u θ σ f g Φ hf hg
      hInt (fun positive => (hfarT positive).1),
      a03_actual_source_moment_four_chambers hc hT1 dual f g Φ hf hg hΦ σ hrawσ s u θ]
    unfold a03ActualFiniteFourRatioLinearZeroMoment a03ActualFourRatioLinearZeroMoment
    have halg (z X Y R : ℂ) : z*X+R-z*Y=z*(X-Y)+R := by ring
    rw [halg]
    have hfour : ‖(∑ m : Bool,∑ n : Bool,a03ActualRatioTimeMoment false false dual
        (a03ZeroModeRatioWeight (rawMomentShifts T σ)) c T a b s u θ σ
          (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ)-
        ∑ m : Bool,∑ n : Bool,a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ))
          c T a b s u (λ/1024) θ σ (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖≤4*CA*E := by
      rw [←Finset.sum_sub_distrib]
      simp_rw [←Finset.sum_sub_distrib]
      calc
        _≤∑ m : Bool,∑ n : Bool,‖a03ActualRatioTimeMoment false false dual
          (a03ZeroModeRatioWeight (rawMomentShifts T σ)) c T a b s u θ σ
            (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g Φ-
          a03ActualRatioSourceLinearZeroMoment dual (fun x => (Φ x:ℂ)) c T a b s u (λ/1024) θ σ
            (a03ZeroModeChamberShifts m n (a03SourceShifts dual T σ)) f g‖ := by
              apply (norm_sum_le _ _).trans
              exact Finset.sum_le_sum (fun m _ => norm_sum_le _ _)
        _≤∑ _m : Bool,∑ _n : Bool,CA*E :=
          Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => hsingle dual m n))
        _=_ := by simp only [Fintype.sum_bool]; ring
    have hfar : ‖∑ positive : Bool,a03ActualSourceFarResidualContour dual positive c T a b s u θ f g Φ σ
        (a03SourceShifts dual T σ)‖≤2*CR*E := by
      apply (norm_sum_le _ _).trans
      calc
        _≤∑ _positive : Bool,CR := Finset.sum_le_sum (fun positive _ => by
          simpa only [neg_zero,Real.rpow_zero,mul_one] using (hfarT positive).2)
        _=2*CR := by simp only [Fintype.sum_bool]; ring
        _≤_ := le_mul_of_one_le_right (by positivity) hE1
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact (add_le_add ((mul_le_mul hconst hfour (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) hfar).trans_eq (by ring)
  have hAll : ‖(∑dual : Bool,a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ)-
      ∑dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u (λ/1024) θ σ f g Φ‖≤
      (8*CA+4*CR)*E := by
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑dual : Bool,‖a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u (λ/1024) θ σ f g Φ‖ := norm_sum_le _ _
      _≤∑ _dual : Bool,(4*CA+2*CR)*E := Finset.sum_le_sum (fun dual _ => hdual dual)
      _=_ := by simp only [Fintype.sum_bool]; ring
  have hL := hLT σ hσB hrootσ
  simp only [neg_zero,Real.rpow_zero,mul_one] at hL
  have hL' := hL.trans (le_mul_of_one_le_right hCL hE1)
  have halg (X Y Z : ℂ) : X-Z=(X-Y)+(Y-Z) := by ring
  change ‖(∑dual : Bool,a03ActualFiniteOffdiagonalGammaMoment dual c T a b u θ σ f g Φ)-
    ∑dual : Bool,a03ActualFourRetainedRatioGCDVStarFinite dual (fun x => (Φ x:ℂ))
      T a b s u (λ/1024) σ f g‖≤(8*CA+4*CR+CL)*E
  rw [halg _ (∑dual : Bool,a03ActualFiniteFourRatioLinearZeroMoment dual c T a b s u (λ/1024) θ σ f g Φ)]
  exact (norm_add_le _ _).trans ((add_le_add hAll hL').trans_eq (by ring))

end
end SixthMoment

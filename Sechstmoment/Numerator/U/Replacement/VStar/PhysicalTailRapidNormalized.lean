import Sechstmoment.Numerator.U.Replacement.VStar.PhysicalTailRapid
import Sechstmoment.Numerator.U.ZeroModes.NormalizedDenominator

/-! The same literal rapid tail for every actual normalized chamber shift. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem normalized_tail_scalar_bound {d D g G p m M k W e c : ℝ}
    (hd0 : 0≤d) (hD : d≤D) (hk : 0≤k) (hg : 0≤g) (hG : g≤G)
    (hp0 : 0≤p) (hp : p≤1) (hW : 0≤W) (he : 0≤e) (hm0 : 0≤m) (hm : m≤M)
    (hc : 0<c) :
    d*k*g/c*p*W*e*m≤D*k*G/c*1*W*e*M := by
  have hD0 := hd0.trans hD
  have hG0 := hg.trans hG
  gcongr

/-- A literal tail in the source's real physical quad variables has
arbitrary negative powers of T, before its GCD/arithmetic sums are taken. -/
theorem a03VStarPhysicalTimeTail_normalized_uniform_rapid {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {c θ κ R η : ℝ}
    (hc : 0<c) (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R) (N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ α : MomentShifts,(∀ j,‖α j‖≤R/Real.log T) → ∀ Q : Fin 4→ℝ,(∀ j,1≤Q j) →
      (∏j : Fin 4,Q j)≤16*T^(2+η) → ∀ dual : Bool,∀ ξ : ℝ,
      ‖a03VStarPhysicalTimeTail dual Φ c T σ α
        Q ξ (θ*Real.log T)‖≤C*T^(-N)/Real.sqrt (∏j : Fin 4,Q j) := by
  let K : Set MomentShifts := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨D,hD,hdual⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  let E : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/κ^2)^24
  let H : ℝ := Real.exp (R*(Real.log 16+(2+η)))
  let F : ℝ := (1+D)*(∫t : ℝ,‖Φ t‖)
  let A : ℝ := H*(gaussianTailConstant 48/(2*Real.pi))*E/c*2^(2*c)*F
  have hGauss := gaussianTailConstant_nonneg 48
  have hE : 0≤E := by dsimp [E]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  have hF : 0≤F := by dsimp [F]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hFK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hFi : Integrable Φ volume := hΦ.integrable_of_hasCompactSupport hFK
  have hlog : ∀ᶠ T : ℝ in atTop,(Real.log T)^48≤T := by
    have hh := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with T hh hT
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT),
      abs_of_nonneg (by positivity : 0≤(Real.log T)^48),one_mul] using hh
  refine ⟨A,hA,?_⟩
  filter_upwards [hdual,hlog,polynomial_gaussian_logarithmic_eventually_le hθ (1+2*c) N,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hdual hlog hdec hT hL
  have hTp : 0<T := zero_lt_one.trans hT
  intro σ hσ hroot α hα Q hQ hcut dual ξ
  have hσK : σ∈K := by
    change dist σ 0≤R
    rw [dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR).mpr hσ
  have hQpos (j : Fin 4) : 0<Q j := zero_lt_one.trans_le (hQ j)
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQpos j)
  have hP1 : 1≤a03PhysicalQuadProduct Q := by
    have h01 : (1:ℝ)≤Q 0*Q 1 := by
      simpa only [one_mul] using mul_le_mul (hQ 0) (hQ 1) zero_le_one (hQpos 0).le
    have h23 : (1:ℝ)≤Q 2*Q 3 := by
      simpa only [one_mul] using mul_le_mul (hQ 2) (hQ 3) zero_le_one (hQpos 2).le
    have hh := mul_le_mul h01 h23 zero_le_one (mul_pos (hQpos 0) (hQpos 1)).le
    simpa only [one_mul,a03PhysicalQuadProduct,Fin.prod_univ_four,mul_assoc] using hh
  have hprod : (a03PhysicalQuadProduct Q)^(-c)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1 (by linarith)
  have hCG : polarGaussianConstant T σ c≤E*T := by
    exact (Sechstmoment.polarGaussianConstant_log_growth hT hL hκ σ c hroot).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have hden := a03ZeroModeRealQuadDenominator_normalized_inv_norm_le hTp hL (by norm_num : (1:ℝ)≤16)
    hR α hα (0:ℂ) (by norm_num) Q hQ hcut
  have hprofile := a03VStarBranchTimeProfile_continuous hΦ hSupp hTp σ dual
  have hsupport := (a03VStarBranchTimeProfile_support dual Φ T σ).trans hSupp
  have hprofileK : HasCompactSupport (a03VStarBranchTimeProfile dual Φ T σ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupport
  have hprofileI : Integrable (a03VStarBranchTimeProfile dual Φ T σ) volume :=
    hprofile.integrable_of_hasCompactSupport hprofileK
  have hm : (∫t : ℝ,‖a03VStarBranchTimeProfile dual Φ T σ t‖)≤F := by
    have hp : ∀t : ℝ,‖a03VStarBranchTimeProfile dual Φ T σ t‖≤(1+D)*‖Φ t‖ := by
      intro t
      cases dual
      · simp only [a03VStarBranchTimeProfile,Bool.false_eq_true,ite_false]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith only [hD] : (1:ℝ)≤1+D) (norm_nonneg (Φ t))
      · by_cases ht : Φ t=0
        · simp [a03VStarBranchTimeProfile,a03ProfileProduct,ht]
        · have hts := hSupp (subset_tsupport _ ht)
          have htT : T*t∈Icc T (2*T) := ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left hts.1 hTp.le,by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hts.2 hTp.le⟩
          have hb := hdual σ hσK (T*t) htT
          have hcancel : T*t/T=t := mul_div_cancel_left₀ t hTp.ne'
          rw [hcancel] at hb
          simp only [a03VStarBranchTimeProfile,ite_true,a03ProfileProduct,norm_mul]
          exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right (by linarith only [] : D≤1+D) (norm_nonneg (Φ t)))
    exact (integral_mono hprofileI.norm (hFi.norm.const_mul (1+D)) hp).trans_eq (by rw [integral_const_mul])
  have ht := a03PhysicalLeadingFourierTail_norm_le hprofile hsupport hTp hc
    (mul_nonneg hθ.le (zero_le_one.trans hL)) σ α Q hQpos ξ
  have hid := a03PhysicalLeadingFourierSet_time_eq hprofile hsupport hTp hc σ
    α Q hQpos ξ {v : ℝ | θ*Real.log T < |v|}
  change a03PhysicalLeadingFourierSet (a03VStarBranchTimeProfile dual Φ T σ) c T σ
    α Q ξ {v : ℝ | θ*Real.log T < |v|}=
      a03VStarPhysicalTimeTail dual Φ c T σ α Q ξ (θ*Real.log T) at hid
  rw [←hid]
  have htime : (2*T)^(2*c)=2^(2*c)*T^(2*c) := Real.mul_rpow (by norm_num) hTp.le
  have hden' : ‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖≤
      H/Real.sqrt (a03PhysicalQuadProduct Q) := hden
  have hAeq : A=H*(gaussianTailConstant 48/(2*Real.pi))*E/c*2^(2*c)*F := rfl
  clear_value H E F A
  calc
    _≤(H/Real.sqrt (a03PhysicalQuadProduct Q)*(gaussianTailConstant 48/(2*Real.pi))*(E*T)/c*
      1*(2*T)^(2*c)*Real.exp (-(1/2)*(θ*Real.log T)^2))*F := by
      apply ht.trans
      apply normalized_tail_scalar_bound (norm_nonneg _) hden' (by positivity) (polarGaussianConstant_nonneg _ _ _) hCG
        (Real.rpow_nonneg hP.le _) hprod (by positivity) (Real.exp_pos _).le
        (integral_nonneg (fun _ => norm_nonneg _)) hm hc
    _=A/Real.sqrt (a03PhysicalQuadProduct Q)*(T^(1+2*c)*Real.exp (-(1/2)*(θ*Real.log T)^2)) := by
      rw [htime,Real.rpow_add hTp,Real.rpow_one]
      rw [hAeq]
      ring
    _≤_ := by
      exact (mul_le_mul_of_nonneg_left hdec (div_nonneg hA (Real.sqrt_nonneg _))).trans_eq (by unfold a03PhysicalQuadProduct; ring)

end
end Sechstmoment

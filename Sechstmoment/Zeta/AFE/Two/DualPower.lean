import Sechstmoment.Zeta.AFE.Two.Dual

/-! Relative reciprocal-height error for the actual two-factor chi multiplier.
The leading term is the literal positive real power, rather than its
inverse-logarithmic normalized-shift limit. -/
namespace Sechstmoment.Source
open Complex Real Filter Set
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

def secondDualPower (t : ℝ) (α : SecondMomentShifts) : ℂ :=
  ((t/(2*Real.pi):ℝ):ℂ)^(-(α 0+α 1))

def secondSingleChiNormalized (t : ℝ) (u : ℂ) : ℂ :=
  zetaChi (criticalLinePoint t+u)/
    (criticalChi t*((t/(2*Real.pi):ℝ):ℂ)^(-u))

theorem secondDual_realPower_eq {t : ℝ} (ht : 0 < t) (u : ℂ) :
    ((t/(2*Real.pi):ℝ):ℂ)^(-u) = (Real.pi:ℂ)^u*(t/2:ℂ)^(-u) := by
  have hp : 0 < t/(2*Real.pi) := by positivity
  have hp2 : 0 < t/2 := by positivity
  have hy : t/(2*Real.pi) = (t/2)/Real.pi := by ring
  have hlog : Complex.log ((t/(2*Real.pi):ℝ):ℂ) =
      Complex.log (t/2:ℂ)-Complex.log (Real.pi:ℂ) := by
    rw [←Complex.ofReal_log hp.le, secondGammaHalf_log ht,
      ←Complex.ofReal_log Real.pi_pos.le, hy,
      Real.log_div hp2.ne' Real.pi_pos.ne']
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero (secondGammaHalf_ne_zero ht),
    ←Complex.exp_add, hlog]
  congr 1
  ring

/-- Exact reconstruction from the two independently normalized Gamma ratios. -/
theorem secondSingleChiNormalized_eq_gamma {t : ℝ} (ht : 0 < t) (u : ℂ)
    (hshift : (criticalLinePoint t+u).im ≠ 0) :
    secondSingleChiNormalized t u = secondGammaMainPhase t (fun _ => 0) (-u)*
      (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
        secondNormalizedGammaFactor t (fun _ => 0) u 0) := by
  have hp : 0 < t/(2*Real.pi) := by positivity
  have hp2 : 0 < t/2 := by positivity
  have hp0 : ((t/(2*Real.pi):ℝ):ℂ)^(-u) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hp.ne'))
  have hp20 : (t/2:ℂ)^(-u) ≠ 0 := by simp [secondGammaHalf_ne_zero ht]
  have hs : (criticalLinePoint t).im ≠ 0 := by simpa [criticalLinePoint] using ht.ne'
  have hcen := Sechstmoment.centeringFactorAt_eq_gamma_ratios
    (Real.exp 1) (criticalLinePoint t) u hs
    (by simpa only [Real.log_exp, Complex.ofReal_one, div_one] using hshift)
  have hphase : Sechstmoment.gammaChiMainPhase (criticalLinePoint t) u u =
      Complex.exp u*((t/(2*Real.pi):ℝ):ℂ)^(-u)*
        secondGammaMainPhase t (fun _ => 0) (-u) := by
    rw [secondDual_realPower_eq ht]
    unfold Sechstmoment.gammaChiMainPhase secondGammaMainPhase
    simp [secondGammaBase, secondSourceZetaPoints, Fin.prod_univ_succ]
    field_simp
  have ha : Sechstmoment.normalizedGammaRatio ((1-criticalLinePoint t)/2) (-u/2) =
      secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 := by
    simp [Sechstmoment.normalizedGammaRatio, secondNormalizedGammaFactor,
      secondGammaBase, secondSourceZetaPoints]
  have hb : Sechstmoment.normalizedGammaRatio (criticalLinePoint t/2) (u/2) =
      secondNormalizedGammaFactor t (fun _ => 0) u 0 := by
    simp [Sechstmoment.normalizedGammaRatio, secondNormalizedGammaFactor,
      secondGammaBase, secondSourceZetaPoints]
  unfold Sechstmoment.centeringFactorAt at hcen
  simp only [Real.log_exp, Complex.ofReal_one, div_one] at hcen
  rw [hphase, ha, hb] at hcen
  change Complex.exp u*zetaChi (criticalLinePoint t+u)/criticalChi t = _ at hcen
  have hchi : zetaChi (criticalLinePoint t+u)/criticalChi t =
      ((t/(2*Real.pi):ℝ):ℂ)^(-u)*secondGammaMainPhase t (fun _ => 0) (-u)*
        (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
          secondNormalizedGammaFactor t (fun _ => 0) u 0) := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero u)
    convert hcen using 1 <;> ring
  unfold secondSingleChiNormalized
  rw [div_mul_eq_div_div, hchi]
  field_simp

/-- Each actual chi ratio has a relative O(t⁻¹) error uniformly on every
bounded raw-shift disk, with all Gamma errors and phases accounted for. -/
theorem secondSingleChiNormalized_error_le {R t : ℝ} (hR : 0 ≤ R)
    (ht : 4096*(1+R+R^2) ≤ t) (u : ℂ) (hu : ‖u‖ ≤ R) :
    ‖secondSingleChiNormalized t u-1‖ ≤ (384*(R+R^2)+2*R)/t := by
  have htp : 0 < t := by nlinarith [sq_nonneg R]
  have ht8 : 8 ≤ t := by nlinarith [sq_nonneg R]
  have htR : R < t := by nlinarith [sq_nonneg R]
  have hs : (criticalLinePoint t+u).im ≠ 0 := by
    have hi := (abs_le.mp ((Complex.abs_im_le_norm u).trans hu)).1
    have he : (criticalLinePoint t+u).im = t+u.im := by simp [criticalLinePoint]
    rw [he]
    exact ne_of_gt (by linarith)
  have hu2 : ‖u‖^2 ≤ R^2 := by nlinarith [norm_nonneg u]
  have hz : 48*(‖u‖+‖u‖^2) < t := by nlinarith [sq_nonneg R]
  let δ : ℝ := 48*(R+R^2)/t
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1/2 := by dsimp [δ]; rw [div_le_iff₀ htp]; nlinarith
  have ha : ‖secondNormalizedGammaFactor t (fun _ => 0) (-u) 1-1‖ ≤ δ := by
    have hh := secondNormalizedGammaFactor_error_le (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num; exact ht8) (fun _ => 0) (by simp) (-u)
      (by simpa only [norm_neg] using hz) 1
    simp only [norm_neg] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by nlinarith) htp.le)
  have hb : ‖secondNormalizedGammaFactor t (fun _ => 0) u 0-1‖ ≤ δ := by
    exact (secondNormalizedGammaFactor_error_le (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num; exact ht8) (fun _ => 0) (by simp) u hz 0).trans
        (div_le_div_of_nonneg_right (by nlinarith) htp.le)
  have hratio := Sechstmoment.norm_div_sub_one_le_four hδ hδhalf ha hb
  have hphase : ‖secondGammaMainPhase t (fun _ => 0) (-u)-1‖ ≤ 2*R/t := by
    have hh := secondGammaMainPhase_error_le (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num; linarith : 4*(0+1) ≤ t) (fun _ => 0) (by simp) (-u)
      (by norm_num; simpa only [norm_neg] using hu.trans htR.le)
    norm_num only [zero_mul, add_zero, norm_neg] at hh
    exact hh.trans (div_le_div_of_nonneg_right (by linarith) htp.le)
  have hpn : ‖secondGammaMainPhase t (fun _ => 0) (-u)‖ ≤ 2 := by
    have hh : ‖secondGammaMainPhase t (fun _ => 0) (-u)‖ ≤
        ‖secondGammaMainPhase t (fun _ => 0) (-u)-1‖+1 := by
      convert norm_add_le (secondGammaMainPhase t (fun _ => 0) (-u)-1) (1:ℂ) using 1 <;> simp
    have h2 : 2*R/t ≤ 1 := by rw [div_le_iff₀ htp]; nlinarith [sq_nonneg R]
    linarith
  rw [secondSingleChiNormalized_eq_gamma htp u hs]
  have he : secondGammaMainPhase t (fun _ => 0) (-u)*
      (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
        secondNormalizedGammaFactor t (fun _ => 0) u 0)-1 =
      secondGammaMainPhase t (fun _ => 0) (-u)*
        (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
          secondNormalizedGammaFactor t (fun _ => 0) u 0-1)+
      (secondGammaMainPhase t (fun _ => 0) (-u)-1) := by ring
  rw [he]
  have hprod : ‖secondGammaMainPhase t (fun _ => 0) (-u)*
      (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
        secondNormalizedGammaFactor t (fun _ => 0) u 0-1)‖ ≤ 8*δ := by
    rw [norm_mul]
    calc
      _ ≤ 2*(4*δ) := mul_le_mul hpn hratio (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ ‖secondGammaMainPhase t (fun _ => 0) (-u)*
        (secondNormalizedGammaFactor t (fun _ => 0) (-u) 1 /
          secondNormalizedGammaFactor t (fun _ => 0) u 0-1)‖+
        ‖secondGammaMainPhase t (fun _ => 0) (-u)-1‖ := norm_add_le _ _
    _ ≤ 8*δ+2*R/t := add_le_add hprod hphase
    _ = (384*(R+R^2)+2*R)/t := by dsimp [δ]; ring

/-- Upper/lower critical-line phases cancel before the dual-power comparison. -/
theorem secondDualMultiplier_div_power_eq {t : ℝ} (ht : 0 < t)
    (α : SecondMomentShifts) :
    secondDualMultiplier t α/secondDualPower t α =
      secondSingleChiNormalized t (α 0)*conj (secondSingleChiNormalized t (conj (α 1))) := by
  have hp : 0 < t/(2*Real.pi) := by positivity
  let P : ℂ := ((t/(2*Real.pi):ℝ):ℂ)
  have hp0 : P ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hlow : zetaChi (1-criticalLinePoint t+α 1) =
      conj (zetaChi (criticalLinePoint t+conj (α 1))) := by
    rw [←Sechstmoment.zetaChi_conj, criticalLinePoint_one_sub]
    congr 1
    simp
  have hconj : conj (P^(-conj (α 1))) = P^(-(α 1)) := by
    dsimp [P]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ←Complex.ofReal_log hp.le]
    simp [←Complex.exp_conj]
  have hc : criticalChi t*conj (criticalChi t) = 1 := by
    simp [Complex.mul_conj', criticalChi_norm]
  have hpow : P^(-(α 0))*P^(-(α 1)) = P^(-(α 0+α 1)) := by
    rw [←Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have hd : (criticalChi t*P^(-(α 0)))*(conj (criticalChi t)*P^(-(α 1))) =
      P^(-(α 0+α 1)) := by
    calc
      _ = (criticalChi t*conj (criticalChi t))*(P^(-(α 0))*P^(-(α 1))) := by ring
      _ = _ := by rw [hc, one_mul, hpow]
  unfold secondSingleChiNormalized secondDualMultiplier secondDualPower
  simp only [secondSourceZetaPoints, Matrix.cons_val_zero, Matrix.cons_val_one]
  change _ = _*(conj (zetaChi (criticalLinePoint t+conj (α 1)) /
    (criticalChi t*P^(-conj (α 1)))))
  rw [map_div₀, map_mul, hconj, ←mul_div_mul_comm, hd, ←hlow]

/-- The actual pair chi multiplier differs relatively from its exact main
positive power by O(t⁻¹), uniformly on bounded raw complex shifts. -/
theorem secondDualMultiplier_relative_power_error_le {R t : ℝ} (hR : 0 ≤ R)
    (ht : 4096*(1+R+R^2) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ R) :
    ‖secondDualMultiplier t α/secondDualPower t α-1‖ ≤
      (1152*(R+R^2)+6*R)/t := by
  have htp : 0 < t := by nlinarith [sq_nonneg R]
  let δ : ℝ := (384*(R+R^2)+2*R)/t
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; rw [div_le_iff₀ htp]; nlinarith [sq_nonneg R]
  let r : Fin 2 → ℂ := ![secondSingleChiNormalized t (α 0),
    conj (secondSingleChiNormalized t (conj (α 1)))]
  have hr : ∀ j, ‖r j-1‖ ≤ δ := by
    intro j
    fin_cases j
    · exact secondSingleChiNormalized_error_le hR ht (α 0) (hα 0)
    · change ‖conj (secondSingleChiNormalized t (conj (α 1)))-1‖ ≤ δ
      rw [show conj (secondSingleChiNormalized t (conj (α 1)))-1 =
        conj (secondSingleChiNormalized t (conj (α 1))-1) by simp, Complex.norm_conj]
      exact secondSingleChiNormalized_error_le hR ht (conj (α 1)) (by simpa using hα 1)
  rw [secondDualMultiplier_div_power_eq htp α]
  have hp := twofold_product_error_le r hδ hδ1 hr
  simp [r, Fin.prod_univ_succ] at hp
  exact hp.trans_eq (by dsimp [δ]; ring)

/-- Absolute form retaining the unavoidable norm of the leading raw-shift power. -/
theorem secondDualMultiplier_power_error_le {R t : ℝ} (hR : 0 ≤ R)
    (ht : 4096*(1+R+R^2) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ R) :
    ‖secondDualMultiplier t α-secondDualPower t α‖ ≤
      (t/(2*Real.pi))^(-(α 0+α 1)).re*((1152*(R+R^2)+6*R)/t) := by
  have htp : 0 < t := by nlinarith [sq_nonneg R]
  have hp : 0 < t/(2*Real.pi) := by positivity
  have hp0 : secondDualPower t α ≠ 0 := by
    unfold secondDualPower
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hp.ne'))
  have he : secondDualMultiplier t α-secondDualPower t α =
      secondDualPower t α*(secondDualMultiplier t α/secondDualPower t α-1) := by field_simp
  rw [he, norm_mul]
  have hn : ‖secondDualPower t α‖ = (t/(2*Real.pi))^(-(α 0+α 1)).re := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos hp _
  rw [hn]
  exact mul_le_mul_of_nonneg_left (secondDualMultiplier_relative_power_error_le hR ht α hα)
    (by positivity)

def secondDualBoxConstant (R : ℝ) : ℝ :=
  Real.exp (2*R*(1+Sechstmoment.elementaryPhaseLogBound))

/-- The literal main t-power stays bounded on every normalized shift box. -/
theorem secondDualPower_normalized_box_norm_le {T R : ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hL : 1 ≤ Real.log T)
    {τ : ℝ} (hτ : τ ∈ Icc (1:ℝ) 2) (σ : SecondMomentShifts)
    (hσ : ∀ j, ‖σ j‖ ≤ R) :
    ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ secondDualBoxConstant R := by
  have hτp : 0 < τ := by linarith [hτ.1]
  have hLp : 0 < Real.log T := by linarith
  let z : ℂ := σ 0+σ 1
  have hz : ‖z‖ ≤ 2*R := (norm_add_le _ _).trans (by linarith [hσ 0, hσ 1])
  have he : secondDualPower (T*τ) (rawSecondMomentShifts T σ) =
      Complex.exp (-z)*Sechstmoment.elementaryCenteredPhase T τ z := by
    unfold secondDualPower rawSecondMomentShifts Sechstmoment.elementaryCenteredPhase
    have hs : -(σ 0/(Real.log T:ℂ)+σ 1/(Real.log T:ℂ)) = -z/(Real.log T:ℂ) := by dsimp [z]; ring
    rw [hs, ←mul_assoc, ←Complex.exp_add]
    simp
  have he0 : ‖Complex.exp (-z)‖ ≤ Real.exp (2*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (by simpa only [norm_neg] using hz)
  have hE : 0 ≤ Sechstmoment.elementaryPhaseLogBound :=
    Sechstmoment.elementaryPhaseLogBound_pos.le
  have harg : ‖-z*(Real.log (τ/(2*Real.pi)):ℂ)/(Real.log T:ℂ)‖ ≤
      2*R*Sechstmoment.elementaryPhaseLogBound := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLp]
    apply (div_le_self (by positivity) hL).trans
    exact mul_le_mul hz (Sechstmoment.elementaryPhase_log_bound hτ) (abs_nonneg _) (by positivity)
  have he1 : ‖Sechstmoment.elementaryCenteredPhase T τ z‖ ≤
      Real.exp (2*R*Sechstmoment.elementaryPhaseLogBound) := by
    rw [Sechstmoment.elementaryCenteredPhase_eq_exp z hT hτp hLp.ne', Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans harg)
  rw [he, norm_mul]
  exact (mul_le_mul he0 he1 (norm_nonneg _) (by positivity)).trans_eq (by
    unfold secondDualBoxConstant
    rw [←Real.exp_add]
    congr 1
    ring)

/-- The exact normalized-box exponent in elementary logarithms. -/
theorem secondDualBoxConstant_eq (R : ℝ) :
    secondDualBoxConstant R =
      Real.exp (2*R*(1+Real.log 2+|Real.log (2*Real.pi)|)) := by
  unfold secondDualBoxConstant Sechstmoment.elementaryPhaseLogBound
  congr 1
  ring

/-- Actual absolute reciprocal-height error and chi-norm bound on every
bounded normalized complex shift box, uniformly over the dyadic time window. -/
theorem secondDualMultiplier_normalized_box_error_and_norm {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ τ ∈ Icc (1:ℝ) 2,
      ∀ σ : SecondMomentShifts, (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C/T ∧
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C := by
  let D : ℝ := 1152*(R+R^2)+6*R
  let B : ℝ := secondDualBoxConstant R
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B, secondDualBoxConstant]; positivity
  refine ⟨B*(D+1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4096*(1+R+R^2)),
    eventually_ge_atTop (1:ℝ), Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1:ℝ))] with T hT hT1 hL
  intro τ hτ σ hσ
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have ht : T ≤ T*τ := by nlinarith [hτ.1]
  have htp : 0 < T*τ := hTp.trans_le ht
  have hα : ∀ j, ‖rawSecondMomentShifts T σ j‖ ≤ R := by
    intro j
    unfold rawSecondMomentShifts
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Real.log T)]
    exact (div_le_self (norm_nonneg _) hL).trans (hσ j)
  have hmain := secondDualPower_normalized_box_norm_le hTp hR hL hτ σ hσ
  have he := secondDualMultiplier_power_error_le hR (hT.trans ht)
    (rawSecondMomentShifts T σ) hα
  have hn : ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ =
      (T*τ/(2*Real.pi))^(-(rawSecondMomentShifts T σ 0+rawSecondMomentShifts T σ 1)).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
  rw [←hn] at he
  have herr : ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
      secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ B*D/T := by
    calc
      _ ≤ B*(D/(T*τ)) := he.trans (mul_le_mul_of_nonneg_right hmain (by positivity))
      _ ≤ B*(D/T) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hD hTp ht) hB.le
      _ = _ := by ring
  constructor
  · exact herr.trans (div_le_div_of_nonneg_right (by nlinarith) hTp.le)
  · have htri : ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖ ≤
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖+
        ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ := by
      convert norm_add_le
        (secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ))
        (secondDualPower (T*τ) (rawSecondMomentShifts T σ)) using 1
      rw [sub_add_cancel]
    have hdiv : B*D/T ≤ B*D := div_le_self (by positivity) hT1
    exact htri.trans ((add_le_add (herr.trans hdiv) hmain).trans_eq (by ring))

/-- Explicit exponential form of the actual normalized-box main-power bound. -/
theorem secondDualPower_normalized_box_exp_norm_le {R T τ : ℝ} (hR : 0 ≤ R)
    (hT : 0 < T) (hlog : 1 ≤ Real.log T) (hτ : τ ∈ Icc (1:ℝ) 2)
    (σ : SecondMomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) :
    ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤
      Real.exp (2*R*(1+Sechstmoment.elementaryPhaseLogBound)) := by
  simpa only [secondDualBoxConstant] using
    secondDualPower_normalized_box_norm_le hT hR hlog hτ σ hσ

/-- The absolute reciprocal-height chi error and actual dual multiplier
bound are both uniform on the real dyadic window and normalized shift box. -/
theorem secondDualMultiplier_normalized_box_power_error_and_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4096*(1+R+R^2) ≤ T → 1 ≤ Real.log T →
      ∀ τ ∈ Icc (1:ℝ) 2, ∀ σ : SecondMomentShifts, (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C/T ∧
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C := by
  let B : ℝ := Real.exp (2*R*(1+Sechstmoment.elementaryPhaseLogBound))
  let K : ℝ := 1152*(R+R^2)+6*R
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨B*(1+K), by dsimp [B]; positivity, ?_⟩
  intro T hT hlog τ hτ σ hσ
  have hTp : 0 < T := by nlinarith [sq_nonneg R]
  have hT1 : 1 ≤ T := by nlinarith [sq_nonneg R]
  have hL : 0 < Real.log T := by linarith
  have ht : T ≤ T*τ := by nlinarith [hτ.1]
  have htp : 0 < T*τ := hTp.trans_le ht
  have ha : ∀ j, ‖rawSecondMomentShifts T σ j‖ ≤ R := by
    intro j
    unfold rawSecondMomentShifts
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    exact (div_le_div_of_nonneg_right (hσ j) hL.le).trans (div_le_self hR hlog)
  have hmain := secondDualPower_normalized_box_exp_norm_le hR hTp hlog hτ σ hσ
  have herr := secondDualMultiplier_power_error_le hR (hT.trans ht)
    (rawSecondMomentShifts T σ) ha
  have hn : (T*τ/(2*Real.pi))^(-(rawSecondMomentShifts T σ 0+
      rawSecondMomentShifts T σ 1)).re =
      ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ := by
    exact (Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < T*τ/(2*Real.pi)) _).symm
  rw [hn] at herr
  have herr' : ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
      secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ B*K/T := by
    calc
      _ ≤ B*(K/(T*τ)) := herr.trans
        (mul_le_mul hmain le_rfl (by positivity) (by dsimp [B]; positivity))
      _ ≤ B*(K/T) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hK hTp ht) (by dsimp [B]; positivity)
      _ = _ := by ring
  constructor
  · exact herr'.trans (div_le_div_of_nonneg_right
      (by dsimp [B]; nlinarith [Real.exp_pos (2*R*(1+Sechstmoment.elementaryPhaseLogBound))]) hTp.le)
  · have hh : ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖ ≤
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖+
        ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ := by
      convert norm_add_le
        (secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ))
        (secondDualPower (T*τ) (rawSecondMomentShifts T σ)) using 1
      simp
    have hc : B*K/T ≤ B*K := div_le_self (by dsimp [B]; positivity) hT1
    exact hh.trans ((add_le_add (herr'.trans hc) hmain).trans_eq (by ring))

/-- The compact-box absolute chi error is genuinely O(1/T), including every
allowed dyadic height and normalized complex shift. -/
theorem secondDualMultiplier_uniform_normalized_power_error {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ τ ∈ Icc (1:ℝ) 2, ∀ σ : SecondMomentShifts, (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          secondDualPower (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C/T ∧
        ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := secondDualMultiplier_normalized_box_power_error_and_bound hR
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (4096*(1+R+R^2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hL
  exact hb T hT hL

/-- Exact time separation retains the dyadic power before oscillatory
integration. The normalized shifts use the same `log T` in both factors. -/
theorem secondDualPower_dyadic_factorization {T τ : ℝ}
    (hT : 0 < T) (hτ : 0 < τ) (σ : SecondMomentShifts) :
    secondDualPower (T*τ) (rawSecondMomentShifts T σ) =
      secondDualPower T (rawSecondMomentShifts T σ)*
        (τ:ℂ)^(-(σ 0+σ 1)/(Real.log T:ℂ)) := by
  unfold secondDualPower rawSecondMomentShifts
  simp only [← add_div, neg_div]
  rw [show T*τ/(2*Real.pi) = (T/(2*Real.pi))*τ by ring,
    Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) hτ.le _

/-- The exact exponent of the dyadic time factor is uniformly bounded on
every normalized complex shift box. -/
theorem secondDualTimeExponent_normalized_box_norm_le {T R : ℝ}
    (hL : 1 ≤ Real.log T) (σ : SecondMomentShifts)
    (hσ : ∀ j, ‖σ j‖ ≤ R) :
    ‖-(σ 0+σ 1)/(Real.log T:ℂ)‖ ≤ 2*R := by
  have hLp : 0 < Real.log T := by linarith
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLp]
  exact (div_le_self (norm_nonneg _) hL).trans
    ((norm_add_le _ _).trans (by linarith [hσ 0, hσ 1]))

/-- The separated dyadic power has a fixed norm bound on the full time
window, with no Gamma or chi remainder in this factor. -/
theorem secondDualTimePower_normalized_window_norm_le {T R τ : ℝ}
    (hR : 0 ≤ R) (hL : 1 ≤ Real.log T) (hτ : τ ∈ Icc (1:ℝ) 2)
    (σ : SecondMomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) :
    ‖(τ:ℂ)^(-(σ 0+σ 1)/(Real.log T:ℂ))‖ ≤ Real.exp (2*R*Real.log 2) := by
  have hτp : 0 < τ := zero_lt_one.trans_le hτ.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hτp, Real.rpow_def_of_pos hτp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.log τ*(2*R) := mul_le_mul_of_nonneg_left
      ((Complex.re_le_norm _).trans
        (secondDualTimeExponent_normalized_box_norm_le hL σ hσ))
      (Real.log_nonneg hτ.1)
    _ ≤ Real.log 2*(2*R) := mul_le_mul_of_nonneg_right
      (Real.log_le_log hτp hτ.2) (by positivity)
    _ = _ := by ring

/-- The literal main power converges uniformly on the entire dyadic time
window and normalized shift box, by the chi limit and reciprocal-height error. -/
theorem secondDualPower_uniform_normalized_window_tendsto {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ τ ∈ Icc (1:ℝ) 2, ∀ σ : SecondMomentShifts,
      (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)-
          Complex.exp (-(σ 0+σ 1))‖ < ε := by
  obtain ⟨C, _hC, herror⟩ := secondDualMultiplier_uniform_normalized_power_error hR
  have hlim : Tendsto (fun T : ℝ => C/T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).const_mul C
  have hhalf : 0 < ε/2 := by positivity
  filter_upwards [herror, hlim.eventually_lt_const hhalf,
    secondDualMultiplier_uniform_normalized_tendsto hR hhalf] with T hb hT hchi
  intro τ hτ σ hσ
  have hp := (hb τ hτ σ hσ).1
  have hc := hchi τ hτ σ hσ
  rw [norm_sub_rev] at hp
  have htri : ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)-
      Complex.exp (-(σ 0+σ 1))‖ ≤
      ‖secondDualPower (T*τ) (rawSecondMomentShifts T σ)-
        secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)‖+
      ‖secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
        Complex.exp (-(σ 0+σ 1))‖ := by
    have he : secondDualPower (T*τ) (rawSecondMomentShifts T σ)-
        Complex.exp (-(σ 0+σ 1)) =
        (secondDualPower (T*τ) (rawSecondMomentShifts T σ)-
          secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ))+
        (secondDualMultiplier (T*τ) (rawSecondMomentShifts T σ)-
          Complex.exp (-(σ 0+σ 1))) := by ring
    rw [he]
    exact norm_add_le _ _
  exact htri.trans_lt ((add_lt_add (hp.trans_lt hT) hc).trans_eq (by ring))

/-- The separated height-only power inherits the same compact-box limit. -/
theorem secondDualPower_base_uniform_normalized_tendsto {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : SecondMomentShifts,
      (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualPower T (rawSecondMomentShifts T σ)-
          Complex.exp (-(σ 0+σ 1))‖ < ε := by
  filter_upwards [secondDualPower_uniform_normalized_window_tendsto hR hε] with T hT
  intro σ hσ
  have hτ : (1:ℝ) ∈ Icc (1:ℝ) 2 := by norm_num
  simpa only [mul_one] using hT 1 hτ σ hσ

/-- In particular, a fixed normalized shift has the literal height-power
limit required after retaining the dyadic time factor. -/
theorem secondDualPower_base_normalized_tendsto {R : ℝ} (hR : 0 ≤ R)
    (σ : SecondMomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) :
    Tendsto (fun T : ℝ => secondDualPower T (rawSecondMomentShifts T σ))
      atTop (𝓝 (Complex.exp (-(σ 0+σ 1)))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [secondDualPower_base_uniform_normalized_tendsto hR hε] with T hT
  simpa only [dist_eq_norm] using hT σ hσ

/-- The separated height-only factor has one eventual compact-box bound. -/
theorem secondDualPower_base_uniform_normalized_norm_le {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : SecondMomentShifts,
      (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualPower T (rawSecondMomentShifts T σ)‖ ≤ secondDualBoxConstant R := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hL
  intro σ hσ
  have hτ : (1:ℝ) ∈ Icc (1:ℝ) 2 := by norm_num
  simpa only [mul_one] using secondDualPower_normalized_box_norm_le hT hR hL hτ σ hσ

end
end Sechstmoment.Source

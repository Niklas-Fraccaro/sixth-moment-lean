import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import SixthMoment.Zeta.AFE.Two.Contour
import SixthMoment.Zeta.AFE.Two.DirichletInterchange
import SixthMoment.Zeta.Gamma.MellinBounds

namespace SixthMoment
open Complex Real MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

def d02SecondAFEKernel (s r z : ℂ) : ℂ :=
  d02SecondAFEPoleKiller s r z / z *
    (Gammaℝ (s+z) * Gammaℝ (r+z)) / (Gammaℝ s * Gammaℝ r)

def d02SecondAFEWeight (s r : ℂ) (x : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ) * ∫ v : ℝ,
    d02SecondAFEKernel s r (1+(v:ℂ)*I) * (x:ℂ)^(-(1+(v:ℂ)*I))

def d02SecondAFESummand (s r : ℂ) (n : ℕ × ℕ) : ℂ :=
  d02SecondAFEWeight s r ((n.1+1:ℝ)*(n.2+1:ℝ)) /
    ((n.1+1:ℂ)^s * (n.2+1:ℂ)^r)

theorem d02SecondAFEPoleKiller_swap (s r z : ℂ) :
    d02SecondAFEPoleKiller s r z = d02SecondAFEPoleKiller r s z := by
  have hN : d02SecondAFENormalization r s=d02SecondAFENormalization s r := by
    unfold d02SecondAFENormalization
    ring
  unfold d02SecondAFEPoleKiller
  rw [hN]
  congr 1
  ring

theorem d02SecondAFEKernel_swap (s r z : ℂ) :
    d02SecondAFEKernel s r z = d02SecondAFEKernel r s z := by
  unfold d02SecondAFEKernel
  rw [d02SecondAFEPoleKiller_swap, mul_comm (Gammaℝ (s+z)) (Gammaℝ (r+z)),
    mul_comm (Gammaℝ s) (Gammaℝ r)]

theorem d02SecondAFEWeight_swap (s r : ℂ) (x : ℝ) :
    d02SecondAFEWeight s r x = d02SecondAFEWeight r s x := by
  unfold d02SecondAFEWeight
  simp_rw [d02SecondAFEKernel_swap s r]

theorem d02SecondAFESummand_swap (s r : ℂ) (n : ℕ × ℕ) :
    d02SecondAFESummand s r n = d02SecondAFESummand r s n.swap := by
  unfold d02SecondAFESummand
  rw [d02SecondAFEWeight_swap]
  simp only [Prod.fst_swap,Prod.snd_swap]
  rw [mul_comm (n.1+1:ℝ) (n.2+1:ℝ), mul_comm ((n.1+1:ℂ)^s) ((n.2+1:ℂ)^r)]

theorem d02SecondAFESeries_swap (s r : ℂ) :
    (∑' n : ℕ × ℕ,d02SecondAFESummand s r n) =
      ∑' n : ℕ × ℕ,d02SecondAFESummand r s n := by
  simp_rw [d02SecondAFESummand_swap s r]
  exact (Equiv.prodComm ℕ ℕ).tsum_eq _

theorem d02GammaReal_continuous_line {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun v : ℝ => Gammaℝ (s+1+(v:ℂ)*I)) := by
  unfold Gammaℝ
  apply Continuous.mul
  · apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]

theorem d02GammaReal_norm_line_le {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    ‖Gammaℝ (s+1+(v:ℂ)*I)‖ ≤
      Real.pi^(-(s.re+1)/2) * Real.Gamma ((s.re+1)/2) := by
  rw [Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hr : ((s+1+(v:ℂ)*I)/2).re = (s.re+1)/2 := by simp
  have hp : 0 < ((s+1+(v:ℂ)*I)/2).re := by rw [hr]; linarith
  simpa only [neg_re, Complex.div_ofNat_re, add_re, one_re,
    mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul,
    sub_self, add_zero, hr] using
      mul_le_mul_of_nonneg_left (gamma_norm_le_realGamma_re hp)
        (Real.rpow_nonneg Real.pi_pos.le _)

theorem d02SecondAFEPoleKiller_line_bound (s r : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖d02SecondAFEPoleKiller s r (1+(v:ℂ)*I)‖ ≤
        C*(1+|v|)^8*Real.exp (-v^2) := by
  let A : ℝ := 2+‖s‖+‖r‖
  refine ⟨Real.exp 1*A^8/‖d02SecondAFENormalization s r‖, by positivity, ?_⟩
  intro v
  let z : ℂ := 1+(v:ℂ)*I
  let W : ℝ := 1+|v|
  have hn : ‖z‖ ≤ W := by
    simpa [z, W] using Complex.norm_le_abs_re_add_abs_im z
  have hfactor (u : ℂ) (hu : ‖u‖ ≤ ‖s‖+‖r‖) :
      ‖u+z‖ ≤ A*W ∧ ‖1-u-z‖ ≤ A*W ∧
        ‖u-z‖ ≤ A*W ∧ ‖1-u+z‖ ≤ A*W := by
    have h1 := norm_add_le u z
    have h2 := norm_sub_le (1-u) z
    have h3 := norm_sub_le u z
    have h4 := norm_add_le (1-u) z
    have h5 := norm_sub_le (1:ℂ) u
    rw [norm_one] at h5
    dsimp [A, W] at *
    constructor
    · nlinarith [abs_nonneg v, norm_nonneg s, norm_nonneg r]
    constructor
    · nlinarith [abs_nonneg v, norm_nonneg s, norm_nonneg r]
    constructor <;> nlinarith [abs_nonneg v, norm_nonneg s, norm_nonneg r]
  have hs := hfactor s (by linarith [norm_nonneg r])
  have hr := hfactor r (by linarith [norm_nonneg s])
  have he : ‖Complex.exp (z^2)‖ = Real.exp 1*Real.exp (-v^2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [z, pow_two, mul_re]
    ring
  unfold d02SecondAFEPoleKiller
  rw [norm_div, norm_mul, he]
  simp only [norm_mul]
  calc
    _ ≤ (Real.exp 1*Real.exp (-v^2)) *
        ((A*W)*(A*W)*(A*W)*(A*W)*(A*W)*(A*W)*(A*W)*(A*W)) /
          ‖d02SecondAFENormalization s r‖ := by
      gcongr
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2.1
      · exact hs.2.2.2
      · exact hr.1
      · exact hr.2.1
      · exact hr.2.2.1
      · exact hr.2.2.2
    _ = _ := by dsimp [W]; ring

theorem d02SecondAFEKernel_integrable {s r : ℂ}
    (hs : 0 < s.re) (hr : 0 < r.re) :
    Integrable (fun v : ℝ => d02SecondAFEKernel s r (1+(v:ℂ)*I)) := by
  obtain ⟨C, hC, hbound⟩ := d02SecondAFEPoleKiller_line_bound s r
  let B : ℝ := Real.pi^(-(s.re+1)/2)*Real.Gamma ((s.re+1)/2) *
    (Real.pi^(-(r.re+1)/2)*Real.Gamma ((r.re+1)/2)) /
      ‖Gammaℝ s * Gammaℝ r‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg
      (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le)
      (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le))
      (norm_nonneg _)
  have hc : Continuous (fun v : ℝ => d02SecondAFEKernel s r (1+(v:ℂ)*I)) := by
    unfold d02SecondAFEKernel d02SecondAFEPoleKiller
    apply Continuous.div_const
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro v hv
        have h := congrArg Complex.re hv
        simp at h
    · simpa only [Pi.mul_def, add_assoc] using
        (d02GammaReal_continuous_line hs).mul (d02GammaReal_continuous_line hr)
  apply ((gaussianPolynomialExponential_integrable 8 0).const_mul (C*B)).mono'
    hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  have hz : 1 ≤ ‖(1:ℂ)+(v:ℂ)*I‖ := by
    simpa using Complex.abs_re_le_norm ((1:ℂ)+(v:ℂ)*I)
  have hq : ‖d02SecondAFEPoleKiller s r (1+(v:ℂ)*I) /
      (1+(v:ℂ)*I)‖ ≤ ‖d02SecondAFEPoleKiller s r (1+(v:ℂ)*I)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hz
  unfold d02SecondAFEKernel
  rw [norm_div, norm_mul, norm_mul]
  calc
    _ ≤ (C*(1+|v|)^8*Real.exp (-v^2)) *
        (Real.pi^(-(s.re+1)/2)*Real.Gamma ((s.re+1)/2) *
          (Real.pi^(-(r.re+1)/2)*Real.Gamma ((r.re+1)/2))) /
            ‖Gammaℝ s*Gammaℝ r‖ := by
      gcongr
      · exact hq.trans (hbound v)
      · simpa only [add_assoc] using d02GammaReal_norm_line_le hs v
      · simpa only [add_assoc] using d02GammaReal_norm_line_le hr v
    _ = _ := by dsimp [B]; simp only [zero_mul, zero_sub]; ring

theorem d02SecondAFESummand_integral (s r : ℂ) (n : ℕ × ℕ) :
    d02SecondAFESummand s r n = (1/(2*Real.pi):ℂ) * ∫ v : ℝ,
      d02SecondAFEKernel s r (1+(v:ℂ)*I) * d02PairDirichletKernel s r n v := by
  have h1 : (n.1+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n.1
  have h2 : (n.2+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n.2
  have hp (z : ℂ) :
      (((n.1+1:ℝ)*(n.2+1:ℝ):ℝ):ℂ)^(-z) /
        ((n.1+1:ℂ)^s*(n.2+1:ℂ)^r) =
          1/(n.1+1:ℂ)^(s+z) * (1/(n.2+1:ℂ)^(r+z)) := by
    have h := Complex.natCast_mul_natCast_cpow (n.1+1) (n.2+1) (-z)
    push_cast at h ⊢
    rw [h, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_add _ _ h1,
      Complex.cpow_add _ _ h2]
    field_simp
  unfold d02SecondAFESummand d02SecondAFEWeight
  rw [mul_div_assoc, ← integral_div]
  apply congrArg ((1/(2*Real.pi):ℂ) * ·)
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    dsimp only
    rw [mul_div_assoc, hp]
    unfold d02PairDirichletKernel
    simp only [← add_assoc]

theorem d02SecondAFESummand_summable {s r : ℂ}
    (hs : 0<s.re) (hr : 0<r.re) : Summable (d02SecondAFESummand s r) := by
  let C : ℝ := ‖(1/(2*Real.pi):ℂ)‖ *
    ∫ v : ℝ, ‖d02SecondAFEKernel s r (1+(v:ℂ)*I)‖
  apply Summable.of_norm
  apply ((d02PairDirichletMass_summable hs hr).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  rw [d02SecondAFESummand_integral, norm_mul]
  calc
    _ ≤ ‖(1/(2*Real.pi):ℂ)‖ * ∫ v : ℝ,
        ‖d02SecondAFEKernel s r (1+(v:ℂ)*I)*d02PairDirichletKernel s r n v‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = C*d02PairDirichletMass s r n := by
      simp_rw [norm_mul, d02PairDirichletKernel_norm]
      rw [integral_mul_const]
      dsimp [C]
      ring

theorem d02SecondAFEIntegral_eq_series {s r : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hr : 0 < r.re) (hr1 : r.re < 1) :
    d02SecondAFEIntegral s r = ∑' n : ℕ × ℕ, d02SecondAFESummand s r n := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hsne : s ≠ 1 := by intro h; simp [h] at hs1
  have hrne : r ≠ 1 := by intro h; simp [h] at hr1
  have hn := d02SecondAFENormalization_ne_zero hs0 hsne hr0 hrne
  have hg := mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos hr)
  simp_rw [d02SecondAFESummand_integral]
  rw [tsum_mul_left, d02PairDirichlet_integral_interchange hs hr _
    (d02SecondAFEKernel_integrable hs hr)]
  unfold d02SecondAFEIntegral d02SecondAFECompletedIntegral
  rw [div_div, ← integral_div]
  have hp : (2*Real.pi:ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    dsimp only
    simp only [add_assoc]
    have hsline : s+ (1+(v:ℂ)*I) ≠ 0 := by
      intro h; have e := congrArg Complex.re h; simp at e; linarith
    have hsline1 : s+ (1+(v:ℂ)*I) ≠ 1 := by
      intro h; have e := congrArg Complex.re h; simp at e; linarith
    have hrline : r+ (1+(v:ℂ)*I) ≠ 0 := by
      intro h; have e := congrArg Complex.re h; simp at e; linarith
    have hrline1 : r+ (1+(v:ℂ)*I) ≠ 1 := by
      intro h; have e := congrArg Complex.re h; simp at e; linarith
    rw [d02SecondAFEContour_eq hs0 hsne hr0 hrne hsline hsline1 hrline hrline1,
      riemannZeta_def_of_ne_zero hsline, riemannZeta_def_of_ne_zero hrline]
    have hgsline : Gammaℝ (s+(1+(v:ℂ)*I)) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hgrline : Gammaℝ (r+(1+(v:ℂ)*I)) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    unfold d02SecondAFEKernel
    field_simp [hgsline, hgrline]

theorem d02ZetaPair_secondAFE_series {s r : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1) (hr : 0 < r.re) (hr1 : r.re < 1) :
    riemannZeta s * riemannZeta r =
      (∑' n : ℕ × ℕ, d02SecondAFESummand s r n) +
        d02SecondAFEDualMultiplier s r *
          (∑' n : ℕ × ℕ, d02SecondAFESummand (1-s) (1-r) n) := by
  rw [d02ZetaPair_secondAFE hs hs1 hr hr1,
    d02SecondAFEIntegral_eq_series hs hs1 hr hr1,
    d02SecondAFEIntegral_eq_series (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)]

end
end SixthMoment

import Sechstmoment.Denominator.Balanced.MomentDefinitions
import Sechstmoment.Zeta.AFE.Two.DualPower
import Sechstmoment.Zeta.AFE.Two.Gaussian

namespace Sechstmoment
open Complex Real Source Filter Set
open scoped BigOperators Topology
noncomputable section

def d02DualSecondMomentShifts (α : SecondMomentShifts) : SecondMomentShifts :=
  ![-α 1,-α 0]

def d02ActualGaussianPair (t : ℝ) (α : SecondMomentShifts) : ℂ :=
  ∑' n : ℕ × ℕ,d02ActualGaussianSummand
    (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) t n

def d02CenteredGaussianPair (T t : ℝ) (σ : SecondMomentShifts) : ℂ :=
  Complex.exp ((σ 0+σ 1)/2) *
    (d02ActualGaussianPair t (rawSecondMomentShifts T σ) +
      secondDualPower t (rawSecondMomentShifts T σ) *
        d02ActualGaussianPair t (d02DualSecondMomentShifts (rawSecondMomentShifts T σ)))

theorem d02DualSecondMomentShifts_norm_le {α : SecondMomentShifts} {R : ℝ}
    (hα : ∀ j,‖α j‖≤R) : ∀ j,‖d02DualSecondMomentShifts α j‖≤R := by
  intro j
  fin_cases j
  · simpa [d02DualSecondMomentShifts] using hα 1
  · simpa [d02DualSecondMomentShifts] using hα 0

theorem d02RawSecondMomentShifts_eventually_small {R ε : ℝ} (hε : 0<ε) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : SecondMomentShifts, (∀ j,‖σ j‖≤R) →
      ∀ j,‖rawSecondMomentShifts T σ j‖≤ε := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (R/ε)))] with T hL
  intro σ hσ j
  have hLp : 0<Real.log T := zero_lt_one.trans_le ((le_max_left _ _).trans hL)
  rw [rawSecondMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
  apply (div_le_div_of_nonneg_right (hσ j) hLp.le).trans
  apply (div_le_iff₀ hLp).mpr
  have he := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hL)
  linarith

theorem d02SecondZetaPoints_re_bounds {ε : ℝ} (hε1 : ε≤1/4)
    {α : SecondMomentShifts} (hα : ∀ j,‖α j‖≤ε) (t : ℝ) (j : Fin 2) :
    1/2-ε≤(secondSourceZetaPoints t j+α j).re ∧
      0<(secondSourceZetaPoints t j+α j).re ∧
        (secondSourceZetaPoints t j+α j).re<1 := by
  have h := abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))
  simp only [Complex.add_re,secondSourceZetaPoints_re]
  constructor
  · linarith
  constructor <;> linarith

theorem d02SecondAFEDualMultiplier_eq_secondDualMultiplier (t : ℝ)
    (α : SecondMomentShifts) :
    d02SecondAFEDualMultiplier (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) = secondDualMultiplier t α := by
  unfold d02SecondAFEDualMultiplier secondDualMultiplier zetaChi
  exact mul_div_mul_comm _ _ _ _

theorem d02ActualZetaPair_secondAFE {ε : ℝ} (hε1 : ε≤1/4)
    (t : ℝ) (α : SecondMomentShifts) (hα : ∀ j,‖α j‖≤ε) :
    riemannZeta (secondSourceZetaPoints t 0+α 0) *
      riemannZeta (secondSourceZetaPoints t 1+α 1) =
      (∑' n : ℕ × ℕ,d02SecondAFESummand
        (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) n) +
      secondDualMultiplier t α *
        (∑' n : ℕ × ℕ,d02SecondAFESummand
          (secondSourceZetaPoints t 0+d02DualSecondMomentShifts α 0)
          (secondSourceZetaPoints t 1+d02DualSecondMomentShifts α 1) n) := by
  have hs := d02SecondZetaPoints_re_bounds hε1 hα t 0
  have hr := d02SecondZetaPoints_re_bounds hε1 hα t 1
  rw [d02ZetaPair_secondAFE_series hs.2.1 hs.2.2 hr.2.1 hr.2.2,
    d02SecondAFEDualMultiplier_eq_secondDualMultiplier]
  have h0 : 1-(secondSourceZetaPoints t 1+α 1) =
      secondSourceZetaPoints t 0+d02DualSecondMomentShifts α 0 := by
    simp only [secondSourceZetaPoints,d02DualSecondMomentShifts,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  have h1 : 1-(secondSourceZetaPoints t 0+α 0) =
      secondSourceZetaPoints t 1+d02DualSecondMomentShifts α 1 := by
    simp only [secondSourceZetaPoints,d02DualSecondMomentShifts,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  rw [d02SecondAFESeries_swap (1-(secondSourceZetaPoints t 0+α 0))
    (1-(secondSourceZetaPoints t 1+α 1)),h0,h1]

theorem d02ZetaGenerators_pair_eq (T t : ℝ) (σ : SecondMomentShifts) :
    zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1) =
      Complex.exp ((σ 0+σ 1)/2) *
        (riemannZeta (secondSourceZetaPoints t 0+rawSecondMomentShifts T σ 0)*
          riemannZeta (secondSourceZetaPoints t 1+rawSecondMomentShifts T σ 1)) := by
  unfold zetaCPlus zetaCMinus shiftedZetaGenerator rawSecondMomentShifts
  simp only [secondSourceZetaPoints,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [show (σ 0+σ 1)/2=σ 0/2+σ 1/2 by ring,Complex.exp_add]
  ring

theorem d02ZetaCentering_norm_le {R : ℝ} (σ : SecondMomentShifts)
    (hσ : ∀ j,‖σ j‖≤R) : ‖Complex.exp ((σ 0+σ 1)/2)‖≤Real.exp R := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h0 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hσ 0))).2
  have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hσ 1))).2
  simp only [Complex.div_ofNat_re,Complex.add_re]
  linarith

theorem d02ActualGaussianPair_uniform_norm {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/4) :
    ∃ G : ℝ,0≤G ∧ ∀ t : ℝ,0<t → ∀ α : SecondMomentShifts,
      (∀ j,‖α j‖≤ε) → ‖d02ActualGaussianPair t α‖≤G*t^(1/2+2*ε) := by
  let c : ℝ := 1/2+2*ε
  let b : ℝ := 1/2-ε
  refine ⟨d02GaussianPowerConstant c*(2*Real.pi)^(-c)*
      ∑' n : ℕ × ℕ,(d02PositivePairProduct n)^(-(b+c)),by
        apply mul_nonneg
        · exact mul_nonneg (d02GaussianPowerConstant_nonneg c) (by positivity)
        · exact tsum_nonneg fun n => Real.rpow_nonneg (d02PositivePairProduct_pos n).le _,?_⟩
  intro t ht α hα
  have hs := d02SecondZetaPoints_re_bounds hε1 hα t 0
  have hr := d02SecondZetaPoints_re_bounds hε1 hα t 1
  exact d02ActualGaussianSeries_norm_le ht hs.1 hr.1 (by dsimp [c]; linarith)
    (by dsimp [b,c]; linarith)

theorem d02ZetaPair_gaussian_window_error {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ t∈Icc T (2*T), ∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
        ‖zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)-d02CenteredGaussianPair T t σ‖≤
          C*t^(-1/2+2*ε) := by
  obtain ⟨K,hK,hgamma⟩ := d02SecondAFE_series_gaussian_error hε hε1
  obtain ⟨Q,hQ,hdual⟩ := secondDualMultiplier_normalized_box_error_and_norm hR
  obtain ⟨G,hG,hmass⟩ := d02ActualGaussianPair_uniform_norm hε hε1
  let c : ℝ := 1/2+2*ε
  refine ⟨Real.exp R*(K+Q*K+2*Q*G),by positivity,?_⟩
  filter_upwards [hdual,d02RawSecondMomentShifts_eventually_small hε,
    eventually_ge_atTop (10000:ℝ)] with T hdual hsmall hT
  intro t ht σ hσ
  have hTp : 0<T := by linarith
  have htp : 0<t := hTp.trans_le ht.1
  have hτ : t/T∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1),(div_le_iff₀ hTp).mpr ht.2⟩
  have htd : T*(t/T)=t := by field_simp
  have hd := hdual (t/T) hτ σ hσ
  rw [htd] at hd
  let α := rawSecondMomentShifts T σ
  let β := d02DualSecondMomentShifts α
  have hα : ∀ j,‖α j‖≤ε := hsmall σ hσ
  have hβ : ∀ j,‖β j‖≤ε := d02DualSecondMomentShifts_norm_le hα
  let A : SecondMomentShifts → ℂ := fun γ => ∑' n : ℕ × ℕ,d02SecondAFESummand
    (secondSourceZetaPoints t 0+γ 0) (secondSourceZetaPoints t 1+γ 1) n
  have hdirect : ‖A α-d02ActualGaussianPair t α‖≤K*t^(c-1) := by
    simpa only [A,d02ActualGaussianPair,show c-1=-1/2+2*ε by dsimp [c]; ring] using
      hgamma t (hT.trans ht.1) α hα
  have hdualGamma : ‖A β-d02ActualGaussianPair t β‖≤K*t^(c-1) := by
    simpa only [A,d02ActualGaussianPair,show c-1=-1/2+2*ε by dsimp [c]; ring] using
      hgamma t (hT.trans ht.1) β hβ
  have hmassβ : ‖d02ActualGaussianPair t β‖≤G*t^c := hmass t htp β hβ
  have hdualError : ‖secondDualMultiplier t α-secondDualPower t α‖≤2*Q/t := by
    apply hd.1.trans
    apply (div_le_div_iff₀ hTp htp).mpr
    calc
      Q*t ≤ Q*(2*T) := mul_le_mul_of_nonneg_left ht.2 hQ
      _ = 2*Q*T := by ring
  have he : zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)-d02CenteredGaussianPair T t σ =
      Complex.exp ((σ 0+σ 1)/2)*
        ((A α-d02ActualGaussianPair t α)+secondDualMultiplier t α*
          (A β-d02ActualGaussianPair t β)+
          (secondDualMultiplier t α-secondDualPower t α)*d02ActualGaussianPair t β) := by
    rw [d02ZetaGenerators_pair_eq,d02ActualZetaPair_secondAFE hε1 t α hα]
    unfold d02CenteredGaussianPair
    change Complex.exp ((σ 0+σ 1)/2)*(A α+secondDualMultiplier t α*A β)-
      Complex.exp ((σ 0+σ 1)/2)*(d02ActualGaussianPair t α+
        secondDualPower t α*d02ActualGaussianPair t β)=_
    ring
  rw [he,norm_mul]
  have hinside : ‖(A α-d02ActualGaussianPair t α)+secondDualMultiplier t α*
      (A β-d02ActualGaussianPair t β)+
      (secondDualMultiplier t α-secondDualPower t α)*d02ActualGaussianPair t β‖≤
        (K+Q*K+2*Q*G)*t^(c-1) := by
    calc
      _ ≤ ‖A α-d02ActualGaussianPair t α‖+
          ‖secondDualMultiplier t α‖*‖A β-d02ActualGaussianPair t β‖+
          ‖secondDualMultiplier t α-secondDualPower t α‖*‖d02ActualGaussianPair t β‖ := by
        simpa only [norm_mul] using (norm_add₃_le
          (a := A α-d02ActualGaussianPair t α)
          (b := secondDualMultiplier t α*(A β-d02ActualGaussianPair t β))
          (c := (secondDualMultiplier t α-secondDualPower t α)*d02ActualGaussianPair t β))
      _ ≤ K*t^(c-1)+Q*(K*t^(c-1))+(2*Q/t)*(G*t^c) := by
        exact add_le_add
          (add_le_add hdirect (mul_le_mul hd.2 hdualGamma (norm_nonneg _) hQ))
          (mul_le_mul hdualError hmassβ (norm_nonneg _) (by positivity))
      _ = _ := by
        have hp : t^c=t^(c-1)*t := by
          calc
            t^c = t^((c-1)+1) := by congr 1; ring
            _ = t^(c-1)*t := by rw [Real.rpow_add htp,Real.rpow_one]
        rw [hp]
        field_simp [htp.ne']
  have hbound := mul_le_mul (d02ZetaCentering_norm_le σ hσ) hinside
    (norm_nonneg _) (Real.exp_pos _).le
  simpa only [mul_assoc,show c-1=-1/2+2*ε by dsimp [c]; ring] using hbound

end
end Sechstmoment

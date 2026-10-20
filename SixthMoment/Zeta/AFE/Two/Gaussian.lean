import SixthMoment.Zeta.AFE.Two.AbsoluteMass
import SixthMoment.Zeta.AFE.Two.GammaWeight
import SixthMoment.Zeta.AFE.Two.Identity

namespace SixthMoment
open Complex Real Source MeasureTheory Filter
open scoped BigOperators
noncomputable section

def d02ActualPairCoefficient (s r : ℂ) (n : ℕ × ℕ) : ℂ :=
  1/((n.1+1:ℂ)^s*(n.2+1:ℂ)^r)

def d02ActualGaussianSummand (s r : ℂ) (t : ℝ) (n : ℕ × ℕ) : ℂ :=
  d02ActualPairCoefficient s r n *
    (d02GaussianV0 (2*Real.pi*d02PositivePairProduct n/t):ℂ)

theorem d02ActualPairCoefficient_norm (s r : ℂ) (n : ℕ × ℕ) :
    ‖d02ActualPairCoefficient s r n‖ =
      (n.1+1:ℝ)^(-s.re)*(n.2+1:ℝ)^(-r.re) := by
  unfold d02ActualPairCoefficient
  rw [norm_div, norm_one, norm_mul,
    show (n.1+1:ℂ)=((n.1+1:ℝ):ℂ) by push_cast; rfl,
    show (n.2+1:ℂ)=((n.2+1:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Real.rpow_neg (by positivity : (0:ℝ)≤n.1+1),
    Real.rpow_neg (by positivity : (0:ℝ)≤n.2+1)]
  simp only [one_div,mul_inv_rev]
  ring

theorem d02ActualPairCoefficient_norm_le {s r : ℂ} {b : ℝ}
    (hs : b≤s.re) (hr : b≤r.re) (n : ℕ × ℕ) :
    ‖d02ActualPairCoefficient s r n‖ ≤ (d02PositivePairProduct n)^(-b) := by
  rw [d02ActualPairCoefficient_norm, d02PositivePairProduct,
    Real.mul_rpow (by positivity) (by positivity)]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) n.1] : (1:ℝ)≤n.1+1) (by linarith))
    (Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) n.2] : (1:ℝ)≤n.2+1) (by linarith))
    (by positivity) (by positivity)

theorem d02ActualGaussianSummand_summable {s r : ℂ} {t b A : ℝ}
    (ht : 0<t) (hs : b≤s.re) (hr : b≤r.re) (hA : 0≤A) (hab : 1<b+A) :
    Summable (d02ActualGaussianSummand s r t) := by
  have hY : 0<t/(2*Real.pi) := by positivity
  have hsum := d02GaussianPairAbsoluteTerm_summable (d02ActualPairCoefficient s r)
    hY zero_le_one hA hab (fun n => by
      simpa only [one_mul] using d02ActualPairCoefficient_norm_le hs hr n)
  apply Summable.of_norm
  convert hsum using 1
  funext n
  unfold d02ActualGaussianSummand d02GaussianPairAbsoluteTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0≤d02GaussianV0 (2*Real.pi*d02PositivePairProduct n/t) from
      d02GaussianTail_nonneg _)]
  congr 2
  field_simp

theorem d02ActualGaussianSeries_norm_le {s r : ℂ} {t b c : ℝ}
    (ht : 0<t) (hs : b≤s.re) (hr : b≤r.re) (hc : 0≤c) (hbc : 1<b+c) :
    ‖∑' n : ℕ × ℕ,d02ActualGaussianSummand s r t n‖ ≤
      (d02GaussianPowerConstant c * (2*Real.pi)^(-c) *
        ∑' n : ℕ × ℕ,(d02PositivePairProduct n)^(-(b+c))) * t^c := by
  have hY : 0<t/(2*Real.pi) := by positivity
  have hsum := d02ActualGaussianSummand_summable ht hs hr hc hbc
  have hmass := d02GaussianPairAbsoluteMass_bound (d02ActualPairCoefficient s r)
    hY zero_le_one hc hbc (fun n => by
      simpa only [one_mul] using d02ActualPairCoefficient_norm_le hs hr n)
  have hnorm (n : ℕ × ℕ) :
      ‖d02ActualGaussianSummand s r t n‖ =
        d02GaussianPairAbsoluteTerm (d02ActualPairCoefficient s r) (t/(2*Real.pi)) n := by
    unfold d02ActualGaussianSummand d02GaussianPairAbsoluteTerm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0≤d02GaussianV0 (2*Real.pi*d02PositivePairProduct n/t) from
        d02GaussianTail_nonneg _)]
    congr 2
    field_simp
  calc
    _ ≤ ∑' n : ℕ × ℕ,‖d02ActualGaussianSummand s r t n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n : ℕ × ℕ,d02GaussianPairAbsoluteTerm
        (d02ActualPairCoefficient s r) (t/(2*Real.pi)) n := tsum_congr hnorm
    _ ≤ _ := hmass
    _ = _ := by
      rw [Real.div_rpow ht.le (by positivity), Real.rpow_neg (by positivity : 0≤2*Real.pi)]
      ring

theorem d02SecondAFEWeight_eq_correctedWeight (t : ℝ) (α : SecondMomentShifts)
    (h0 : 0<(secondSourceZetaPoints t 0+α 0).re)
    (h1 : (secondSourceZetaPoints t 0+α 0).re<1)
    (h2 : 0<(secondSourceZetaPoints t 1+α 1).re)
    (h3 : (secondSourceZetaPoints t 1+α 1).re<1) (x : ℝ) :
    d02SecondAFEWeight (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) x = secondCorrectedWeightOnLine 1 t α x := by
  rw [d02SecondAFEWeight_eq_gammaWeight t α h0 h1 h2 h3]
  rfl

theorem d02SecondAFE_series_gaussian_error {ε : ℝ} (hε : 0<ε) (hε1 : ε≤1/4) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 10000≤t → ∀ α : SecondMomentShifts,
      (∀ j, ‖α j‖≤ε) →
        ‖(∑' n : ℕ × ℕ,
          d02SecondAFESummand (secondSourceZetaPoints t 0+α 0)
            (secondSourceZetaPoints t 1+α 1) n) -
          (∑' n : ℕ × ℕ,
            d02ActualGaussianSummand (secondSourceZetaPoints t 0+α 0)
              (secondSourceZetaPoints t 1+α 1) t n)‖ ≤ C*t^(-1/2+2*ε) := by
  let c : ℝ := 1/2+2*ε
  let b : ℝ := 1/2-ε
  have hc : 0<c := by dsimp [c]; linarith
  have hc1 : c≤1 := by dsimp [c]; linarith
  have hbc : b+c=1+ε := by dsimp [b,c]; ring
  have hp : 1<b+c := by rw [hbc]; linarith
  obtain ⟨K,hK,hweight⟩ := secondCorrectedWeightOnLine_one_gaussian_error hc hc1
  let M : ℝ := ∑' n : ℕ × ℕ, (d02PositivePairProduct n)^(-(b+c))
  have hM : 0≤M := tsum_nonneg (fun n => Real.rpow_nonneg
    (d02PositivePairProduct_pos n).le _)
  refine ⟨K*M, mul_nonneg hK hM, ?_⟩
  intro t ht α hα
  let s : ℂ := secondSourceZetaPoints t 0+α 0
  let r : ℂ := secondSourceZetaPoints t 1+α 1
  have hsre : b≤s.re ∧ 0<s.re ∧ s.re<1 := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα 0)))
    dsimp [s,b,secondSourceZetaPoints]
    simp only [criticalLinePoint_re]
    constructor
    · linarith
    constructor <;> linarith
  have hrre : b≤r.re ∧ 0<r.re ∧ r.re<1 := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα 1)))
    dsimp [r,b,secondSourceZetaPoints]
    simp only [criticalLinePoint_re]
    constructor
    · linarith
    constructor <;> linarith
  have hα1 : ∀ j, ‖α j‖≤1/4 := fun j => (hα j).trans hε1
  have htp : 0<t := by linarith
  have hS := d02SecondAFESummand_summable hsre.2.1 hrre.2.1
  have hG := d02ActualGaussianSummand_summable htp hsre.1 hrre.1 hc.le hp
  have hterm (n : ℕ × ℕ) :
      ‖d02SecondAFESummand s r n-d02ActualGaussianSummand s r t n‖ ≤
        (K*t^(c-1))*(d02PositivePairProduct n)^(-(b+c)) := by
    have hx := d02PositivePairProduct_pos n
    have hw := hweight t (d02PositivePairProduct n) ht hx α hα1
    rw [←d02SecondAFEWeight_eq_correctedWeight t α
      hsre.2.1 hsre.2.2 hrre.2.1 hrre.2.2] at hw
    have he : d02SecondAFESummand s r n-d02ActualGaussianSummand s r t n =
        d02ActualPairCoefficient s r n *
          (d02SecondAFEWeight s r (d02PositivePairProduct n) -
            (d02GaussianV0 (2*Real.pi*d02PositivePairProduct n/t):ℂ)) := by
      unfold d02SecondAFESummand d02ActualGaussianSummand d02ActualPairCoefficient
        d02PositivePairProduct
      ring
    rw [he,norm_mul]
    calc
      _ ≤ (d02PositivePairProduct n)^(-b)*
          (K*t^(c-1)*(d02PositivePairProduct n)^(-c)) :=
        mul_le_mul (d02ActualPairCoefficient_norm_le hsre.1 hrre.1 n) hw
          (norm_nonneg _) (by positivity)
      _ = (K*t^(c-1))*((d02PositivePairProduct n)^(-b)*
          (d02PositivePairProduct n)^(-c)) := by ring
      _ = _ := by
        rw [←Real.rpow_add hx, show -b+-c=-(b+c) by ring]
  rw [←hS.tsum_sub hG]
  calc
    _ ≤ ∑' n : ℕ × ℕ, ‖d02SecondAFESummand s r n-d02ActualGaussianSummand s r t n‖ :=
      norm_tsum_le_tsum_norm (hS.sub hG).norm
    _ ≤ ∑' n : ℕ × ℕ, (K*t^(c-1))*(d02PositivePairProduct n)^(-(b+c)) :=
      ((hS.sub hG).norm).tsum_le_tsum hterm
        ((d02_pair_power_summable hp).mul_left _)
    _ = (K*M)*t^(-1/2+2*ε) := by
      rw [tsum_mul_left]
      have hcE : c-1=-1/2+2*ε := by dsimp [c]; ring
      rw [hcE]
      dsimp [M]
      ring

theorem d02SecondAFE_normalized_series_gaussian_error {R ε : ℝ}
    (_hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ t∈Set.Icc T (2*T), ∀ σ : SecondMomentShifts, (∀ j,‖σ j‖≤R) →
        ‖(∑' n : ℕ × ℕ,
          d02SecondAFESummand (secondSourceZetaPoints t 0+σ 0/(Real.log T:ℂ))
            (secondSourceZetaPoints t 1+σ 1/(Real.log T:ℂ)) n) -
          (∑' n : ℕ × ℕ,
            d02ActualGaussianSummand (secondSourceZetaPoints t 0+σ 0/(Real.log T:ℂ))
              (secondSourceZetaPoints t 1+σ 1/(Real.log T:ℂ)) t n)‖ ≤
                C*t^(-1/2+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := d02SecondAFE_series_gaussian_error hε hε1
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (10000:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (max 1 (R/ε)))]
    with T hT hL
  intro t ht σ hσ
  have hLp : 0<Real.log T := zero_lt_one.trans_le ((le_max_left _ _).trans hL)
  apply hbound t (hT.trans ht.1) (fun j => σ j/(Real.log T:ℂ))
  intro j
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLp]
  apply (div_le_div_of_nonneg_right (hσ j) hLp.le).trans
  apply (div_le_iff₀ hLp).mpr
  have he := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hL)
  linarith

end
end SixthMoment

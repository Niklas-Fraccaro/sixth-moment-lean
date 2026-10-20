import Mathlib.MeasureTheory.Integral.DominatedConvergence
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.ArchEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.InitialKernel
import SixthMoment.Numerator.U.ZeroModes.Ratio.FullMeasurability

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

abbrev A03GCDMellinCoordinates := ℝ × (ℝ × (ℝ × ℝ))

def a03GCDMellinMeasure : Measure A03GCDMellinCoordinates :=
  (volume.restrict (Ioi 0)).prod (volume.prod (volume.prod volume))

instance a03GCDMellinMeasure_sFinite : SFinite a03GCDMellinMeasure := by
  unfold a03GCDMellinMeasure
  infer_instance

def a03GCDMellinU (ε : ℝ) (p : A03GCDMellinCoordinates) : ℂ :=
  (ε:ℂ)+(p.2.1:ℂ)*I

def a03GCDMellinV (ε : ℝ) (p : A03GCDMellinCoordinates) : ℂ :=
  (ε:ℂ)+(p.2.2.1:ℂ)*I

def a03GCDMellinS (ε : ℝ) (p : A03GCDMellinCoordinates) : ℂ :=
  ((1+ε:ℝ):ℂ)+(p.2.2.2:ℂ)*I

def a03GCDCountableMajorant (ε : ℝ) (k : (ℕ×ℕ)×ℕ) : ℝ :=
  ‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.1.1‖*
    ‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.1.2‖*
      ‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.2‖

theorem a03GCDCountableMajorant_nonneg (ε : ℝ) (k : (ℕ×ℕ)×ℕ) :
    0≤a03GCDCountableMajorant ε k := by unfold a03GCDCountableMajorant; positivity

theorem a03GCDCountableMajorant_summable {ε : ℝ} (hε : 0<ε) :
    Summable (a03GCDCountableMajorant ε) := by
  have h : Summable (fun n : ℕ => ‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) n‖) :=
    shiftedPowerArithmetic_norm_summable (by simp only [ofReal_re]; linarith)
  have hmn := h.mul_of_nonneg h (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact hmn.mul_of_nonneg h (fun _ => by positivity) (fun _ => norm_nonneg _)

theorem a03ShiftedPowerArithmetic_norm_le {ε : ℝ} {z : ℂ}
    (hz : 1+ε≤z.re) (n : ℕ) :
    ‖shiftedPowerArithmetic z n‖≤‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) n‖ := by
  by_cases hn : n=0
  · simp [hn]
  rw [shiftedPowerArithmetic_apply _ hn,shiftedPowerArithmetic_apply _ hn,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [neg_re,ofReal_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hn)
    (by linarith)

theorem a03GCDInitialArithmetic_norm_le {ε : ℝ} (hε : 0<ε)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (_hb : 0<b) {u v s : ℂ}
    (hu : u.re=ε) (hv : v.re=ε) (hs : s.re=1+ε) (k : (ℕ×ℕ)×ℕ) :
    ‖shiftedPowerArithmetic s k.2*
      a03GCDDirichletTerm a b (α 0-α 1+2*u) (α 2-α 3+2*v) s k.1‖≤
        a03GCDCountableMajorant ε k := by
  have h0 := abs_le.mp ((Complex.abs_re_le_norm (α 0)).trans (hα 0))
  have h1 := abs_le.mp ((Complex.abs_re_le_norm (α 1)).trans (hα 1))
  have h2 := abs_le.mp ((Complex.abs_re_le_norm (α 2)).trans (hα 2))
  have h3 := abs_le.mp ((Complex.abs_re_le_norm (α 3)).trans (hα 3))
  have hm := a03ShiftedPowerArithmetic_norm_le (ε := ε)
    (z := 1+(α 0-α 1+2*u)) (by simp only [add_re,sub_re,mul_re,re_ofNat,im_ofNat,zero_mul,sub_zero,one_re,hu]; linarith) k.1.1
  have hn := a03ShiftedPowerArithmetic_norm_le (ε := ε)
    (z := 1+(α 2-α 3+2*v)) (by simp only [add_re,sub_re,mul_re,re_ofNat,im_ofNat,zero_mul,sub_zero,one_re,hv]; linarith) k.1.2
  have hh := a03ShiftedPowerArithmetic_norm_le hs.ge k.2
  by_cases hm0 : k.1.1=0
  · simp [a03GCDDirichletTerm,hm0,a03GCDCountableMajorant]
  by_cases hn0 : k.1.2=0
  · simp [a03GCDDirichletTerm,hn0,a03GCDCountableMajorant]
  have hgcd : 0<Nat.gcd (a*k.1.1) (b*k.1.2) :=
    Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha (Nat.pos_of_ne_zero hm0))
  have hgcd1 : (1:ℝ)≤Nat.gcd (a*k.1.1) (b*k.1.2) := by exact_mod_cast hgcd
  have hgpow : ‖(Nat.gcd (a*k.1.1) (b*k.1.2):ℂ)^(1-s)‖≤1 := by
    rw [Complex.norm_natCast_cpow_of_pos hgcd]
    apply Real.rpow_le_one_of_one_le_of_nonpos hgcd1
    simp only [sub_re,one_re,hs]
    linarith
  unfold a03GCDDirichletTerm a03GCDCountableMajorant
  simp only [norm_mul]
  calc
    _≤‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.2‖*
        (1*‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.1.1‖*
          ‖shiftedPowerArithmetic ((1+ε:ℝ):ℂ) k.1.2‖) := by gcongr
    _=_ := by ring

theorem a03ShiftedPowerArithmetic_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    {Z : Ω→ℂ} (hZ : Measurable Z) (n : ℕ) :
    Measurable (fun p => shiftedPowerArithmetic (Z p) n) := by
  by_cases hn : n=0
  · simp only [hn,ArithmeticFunction.map_zero]; exact measurable_const
  simp only [shiftedPowerArithmetic_apply _ hn]
  exact a03MeasurableCPow measurable_const hZ.neg

theorem a03GCDInitialArithmetic_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (α : MomentShifts) (a b : ℕ) {U V S : Ω→ℂ}
    (hU : Measurable U) (hV : Measurable V) (hS : Measurable S) (k : (ℕ×ℕ)×ℕ) :
    Measurable (fun p => shiftedPowerArithmetic (S p) k.2*
      a03GCDDirichletTerm a b (α 0-α 1+2*U p) (α 2-α 3+2*V p) (S p) k.1) := by
  unfold a03GCDDirichletTerm
  have hM : Measurable (fun p => 1+(α 0-α 1+2*U p)) :=
    measurable_const.add (measurable_const.add (hU.const_mul 2))
  have hN : Measurable (fun p => 1+(α 2-α 3+2*V p)) :=
    measurable_const.add (measurable_const.add (hV.const_mul 2))
  have hG : Measurable (fun p => (Nat.gcd (a*k.1.1) (b*k.1.2):ℂ)^(1-S p)) :=
    a03MeasurableCPow measurable_const (measurable_const.sub hS)
  exact (a03ShiftedPowerArithmetic_measurable_comp hS k.2).mul
    ((hG.mul (a03ShiftedPowerArithmetic_measurable_comp hM k.1.1)).mul
      (a03ShiftedPowerArithmetic_measurable_comp hN k.1.2))

def a03GCDContourMajorant (r Y : ℝ) (p : A03GCDMellinCoordinates) : ℝ :=
  (p.1^(r-1)*a03ZeroModeRatioXEnvelope Y p.1)*
    ((1+|p.2.1|)^4*Real.exp (-p.2.1^2))*
      ((1+|p.2.2.1|)^4*Real.exp (-p.2.2.1^2))*(1+p.2.2.2^2)⁻¹

theorem a03GCDContourMajorant_nonneg (r Y : ℝ) (p : A03GCDMellinCoordinates) (hp : 0≤p.1) :
    0≤a03GCDContourMajorant r Y p := by
  unfold a03GCDContourMajorant
  have h := a03ZeroModeRatioXEnvelope_nonneg Y p.1
  positivity

theorem a03GCDContourMajorant_integrable {r Y : ℝ} (hY : 0<Y) (hr : 0<r) (hr2 : r<2) :
    Integrable (a03GCDContourMajorant r Y) a03GCDMellinMeasure := by
  have hP := a03ZeroModeRatioXEnvelope_weight_integrable hY hr hr2
  have hG : Integrable (fun y : ℝ => (1+|y|)^4*Real.exp (-y^2)) := by
    simpa only [zero_mul,zero_sub] using SixthMoment.gaussianPolynomialExponential_integrable 4 0
  unfold a03GCDMellinMeasure
  convert hP.mul_prod (hG.mul_prod (hG.mul_prod integrable_inv_one_add_sq)) using 1
  funext p
  unfold a03GCDContourMajorant
  ring

theorem a03GCDRatioWeight_line_bound {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    (α : MomentShifts) (y : ℝ) :
    ‖a03ZeroModeRatioWeight α ((ε:ℂ)+(y:ℂ)*I)/((ε:ℂ)+(y:ℂ)*I)‖≤
      (a03ZeroModeRatioGaussianConstant α 1/ε)*((1+|y|)^4*Real.exp (-y^2)) := by
  let u : ℂ := (ε:ℂ)+(y:ℂ)*I
  have hC := a03ZeroModeRatioGaussianConstant_nonneg α 1
  have hu : u.re=ε := by simp [u]
  have hden : ε≤‖u‖ := by simpa only [hu,abs_of_pos hε] using Complex.abs_re_le_norm u
  have hpow := a03ZeroModeRatioWeight_gaussian_bound α (by norm_num : (0:ℝ)≤1)
    (z := u) (by rw [hu,abs_of_pos hε]; exact hε1.le)
  have hum : u.im=y := by simp [u]
  rw [hum] at hpow
  rw [norm_div]
  calc
    _≤(a03ZeroModeRatioGaussianConstant α 1*(1+|y|)^4*Real.exp (-y^2))/ε :=
      div_le_div₀ (by positivity) hpow hε hden
    _=_ := by ring

def a03ZeroModeGCDInitialTimeBase (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) : ℂ :=
  A a*B b*(a:ℂ)^(-1+α 1-u)*(b:ℂ)^(-1+α 3-v)*
    (x:ℂ)^(-1-α 1-α 3+u+v)*
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        a03ZeroModeGCDArchTimeKernel Φ T σ 1 a b x s

theorem a03ZeroModeGCDInitialTimeBase_measurable
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T ε : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) :
    Measurable (fun p : A03GCDMellinCoordinates => a03ZeroModeGCDInitialTimeBase Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)) := by
  have hU : Measurable (a03GCDMellinU ε) := by unfold a03GCDMellinU; fun_prop
  have hV : Measurable (a03GCDMellinV ε) := by unfold a03GCDMellinV; fun_prop
  have hS : Measurable (a03GCDMellinS ε) := by unfold a03GCDMellinS; fun_prop
  have hX : Measurable (fun p : A03GCDMellinCoordinates => (p.1:ℂ)) := by fun_prop
  have hA : Measurable (fun p : A03GCDMellinCoordinates => (a:ℂ)^(-1+α 1-a03GCDMellinU ε p)) :=
    a03MeasurableCPow (f := fun _ : A03GCDMellinCoordinates => (a:ℂ))
    measurable_const (measurable_const.sub hU)
  have hB : Measurable (fun p : A03GCDMellinCoordinates => (b:ℂ)^(-1+α 3-a03GCDMellinV ε p)) :=
    a03MeasurableCPow (f := fun _ : A03GCDMellinCoordinates => (b:ℂ))
    measurable_const (measurable_const.sub hV)
  have hXp : Measurable (fun p : A03GCDMellinCoordinates =>
      (p.1:ℂ)^(-1-α 1-α 3+a03GCDMellinU ε p+a03GCDMellinV ε p)) :=
    a03MeasurableCPow hX ((measurable_const.add hU).add hV)
  have hG := (a03ZeroModeRatioWeight_differentiable α).continuous.measurable
  have hAr := a03ZeroModeGCDArchTimeKernel_measurable_comp Φ hΦ T σ 1 a b measurable_fst hS
  unfold a03ZeroModeGCDInitialTimeBase
  exact ((((((measurable_const.mul hA).mul hB).mul hXp).mul ((hG.comp hU).div hU)).mul
    ((hG.comp hV).div hV)).mul hAr)

theorem a03ZeroModeGCDInitialBase_aestronglyMeasurable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (σ α : MomentShifts)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    AEStronglyMeasurable (fun p : A03GCDMellinCoordinates => a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)) a03GCDMellinMeasure := by
  have hPos : ∀ᵐ p : A03GCDMellinCoordinates ∂a03GCDMellinMeasure,0<p.1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  apply (a03ZeroModeGCDInitialTimeBase_measurable Φ hΦ.continuous.measurable T ε σ α a b A B).aestronglyMeasurable.congr
  filter_upwards [hPos] with p hp
  unfold a03ZeroModeGCDInitialTimeBase a03ZeroModeGCDInitialBase
  rw [a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ (by norm_num : 0<(1:ℕ)) ha hb hp
    (by simp only [a03GCDMellinS,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]; linarith)]

theorem a03ZeroModeGCDInitialBase_joint_majorant
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    ∃ C : ℝ,0≤C ∧ ∀ p : A03GCDMellinCoordinates,0<p.1 →
      ‖a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)‖≤
      C*a03GCDContourMajorant (1+3*ε-(α 1).re-(α 3).re)
        (T*Real.sqrt ((a:ℝ)*(b:ℝ))) p := by
  have hcs : 1+ε∈Icc (1/8:ℝ) (15/8) := by constructor <;> linarith
  obtain ⟨D,hD,hArch⟩ := a03ZeroModeGCDArchKernel_full_height_envelope hΦ hSupp hcs 2
  let Q : ℝ := ‖A a‖*‖B b‖*(a:ℝ)^(-1+(α 1).re-ε)*(b:ℝ)^(-1+(α 3).re-ε)
  let R : ℝ := a03ZeroModeRatioGaussianConstant α 1/ε
  let C : ℝ := Q*R^2*D*(1+polarGaussianConstant T σ 1)*T^(-(1+ε))
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hR : 0≤R := div_nonneg (a03ZeroModeRatioGaussianConstant_nonneg _ _) hε.le
  have hCG := polarGaussianConstant_nonneg T σ 1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro p hp
  let u := a03GCDMellinU ε p
  let v := a03GCDMellinV ε p
  let s := a03GCDMellinS ε p
  have hu : u.re=ε := by simp [u,a03GCDMellinU]
  have hv : v.re=ε := by simp [v,a03GCDMellinV]
  have hs : s.re=1+ε := by simp [s,a03GCDMellinS]
  have hsi : s.im=p.2.2.2 := by simp [s,a03GCDMellinS]
  have hW1 := a03GCDRatioWeight_line_bound hε (by linarith : ε<1) α p.2.1
  have hW2 := a03GCDRatioWeight_line_bound hε (by linarith : ε<1) α p.2.2.1
  change ‖a03ZeroModeRatioWeight α u/u‖≤R*((1+|p.2.1|)^4*Real.exp (-p.2.1^2)) at hW1
  change ‖a03ZeroModeRatioWeight α v/v‖≤R*((1+|p.2.2.1|)^4*Real.exp (-p.2.2.1^2)) at hW2
  have hAr := hArch T hT σ 1 a b (by norm_num) ha hb p.1 hp s hs
  simp only [Nat.cast_one,mul_one,hsi] at hAr
  let Y : ℝ := T*Real.sqrt ((a:ℝ)*(b:ℝ))
  have hEnv := a03ZeroModeRatioXEnvelope_nonneg Y p.1
  have hAr' : ‖a03ZeroModeGCDArchKernel Φ T σ 1 a b p.1 s‖≤
      D*(1+polarGaussianConstant T σ 1)*(p.1/T)^(1+ε)*
        a03ZeroModeRatioXEnvelope Y p.1*(1+p.2.2.2^2)⁻¹ := by
    have hm : ‖a03ZeroModeGCDArchKernel Φ T σ 1 a b p.1 s‖*(1+p.2.2.2^2)≤
        D*(1+polarGaussianConstant T σ 1)*(p.1/T)^(1+ε)*a03ZeroModeRatioXEnvelope Y p.1 := by
      apply le_trans _ hAr
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith [sq_abs p.2.2.2,abs_nonneg p.2.2.2]
    simpa only [div_eq_mul_inv] using (le_div_iff₀ (by positivity : 0<1+p.2.2.2^2)).mpr hm
  have hnorm : ‖a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1 u v s‖=
      Q*p.1^(-1-(α 1).re-(α 3).re+2*ε)*
        ‖a03ZeroModeRatioWeight α u/u‖*‖a03ZeroModeRatioWeight α v/v‖*
          ‖a03ZeroModeGCDArchKernel Φ T σ 1 a b p.1 s‖ := by
    unfold a03ZeroModeGCDInitialBase
    simp only [norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos ha,Complex.norm_natCast_cpow_of_pos hb,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [add_re,sub_re,neg_re,one_re,hu,hv]
    dsimp [Q]
    rw [show -1-(α 1).re-(α 3).re+ε+ε= -1-(α 1).re-(α 3).re+2*ε by ring]
  change ‖a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1 u v s‖≤_
  rw [hnorm]
  calc
    _≤Q*p.1^(-1-(α 1).re-(α 3).re+2*ε)*
      (R*((1+|p.2.1|)^4*Real.exp (-p.2.1^2)))*
        (R*((1+|p.2.2.1|)^4*Real.exp (-p.2.2.1^2)))*
          (D*(1+polarGaussianConstant T σ 1)*(p.1/T)^(1+ε)*
            a03ZeroModeRatioXEnvelope Y p.1*(1+p.2.2.2^2)⁻¹) := by gcongr
    _=_ := by
      have hpow : p.1^(-1-(α 1).re-(α 3).re+2*ε)*(p.1/T)^(1+ε)=
          T^(-(1+ε))*p.1^((1+3*ε-(α 1).re-(α 3).re)-1) := by
        rw [Real.div_rpow hp.le hT.le,div_eq_mul_inv,←Real.rpow_neg hT.le]
        calc
          _=(p.1^(-1-(α 1).re-(α 3).re+2*ε)*p.1^(1+ε))*T^(-(1+ε)) := by ring
          _=_ := by
            rw [←Real.rpow_add hp]
            rw [show (-1-(α 1).re-(α 3).re+2*ε)+(1+ε)=(1+3*ε-(α 1).re-(α 3).re)-1 by ring]
            ring
      dsimp only [C,a03GCDContourMajorant]
      calc
        _=(Q*R^2*D*(1+polarGaussianConstant T σ 1))*
          (p.1^(-1-(α 1).re-(α 3).re+2*ε)*(p.1/T)^(1+ε))*
            a03ZeroModeRatioXEnvelope Y p.1*((1+|p.2.1|)^4*Real.exp (-p.2.1^2))*
              ((1+|p.2.2.1|)^4*Real.exp (-p.2.2.1^2))*(1+p.2.2.2^2)⁻¹ := by ring
        _=_ := by rw [hpow]; ring

theorem a03ZeroModeGCDInitialBase_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    Integrable (fun p : A03GCDMellinCoordinates => a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)) a03GCDMellinMeasure := by
  have hβ := abs_le.mp ((Complex.abs_re_le_norm (α 1)).trans (hα 1))
  have hδ := abs_le.mp ((Complex.abs_re_le_norm (α 3)).trans (hα 3))
  have hr : 0<1+3*ε-(α 1).re-(α 3).re := by linarith
  have hr2 : 1+3*ε-(α 1).re-(α 3).re<2 := by linarith
  have hY : 0<T*Real.sqrt ((a:ℝ)*(b:ℝ)) :=
    mul_pos hT (Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast ha) (by exact_mod_cast hb)))
  obtain ⟨C,_hC,hbound⟩ := a03ZeroModeGCDInitialBase_joint_majorant hΦ hSupp hT hε hε1 σ α ha hb A B
  have hi := (a03GCDContourMajorant_integrable hY hr hr2).const_mul C
  apply hi.mono' (a03ZeroModeGCDInitialBase_aestronglyMeasurable hΦ hSupp hT hε σ α ha hb A B)
  have hPos : ∀ᵐ p : A03GCDMellinCoordinates ∂a03GCDMellinMeasure,0<p.1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hPos] with p hp
  exact hbound p hp

theorem a03ZeroModeGCDInitialMNHKernel_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) (k : (ℕ×ℕ)×ℕ) :
    Integrable (fun p : A03GCDMellinCoordinates => a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) k) a03GCDMellinMeasure := by
  have hBase := a03ZeroModeGCDInitialBase_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B
  have hU : Measurable (a03GCDMellinU ε) := by unfold a03GCDMellinU; fun_prop
  have hV : Measurable (a03GCDMellinV ε) := by unfold a03GCDMellinV; fun_prop
  have hS : Measurable (a03GCDMellinS ε) := by unfold a03GCDMellinS; fun_prop
  have hAr := (a03GCDInitialArithmetic_measurable_comp α a b hU hV hS k).aestronglyMeasurable (μ := a03GCDMellinMeasure)
  have hMeas := hBase.aestronglyMeasurable.mul hAr
  apply (hBase.norm.const_mul (a03GCDCountableMajorant ε k)).mono'
    (hMeas.congr (ae_of_all _ (fun p => by simp only [Pi.mul_apply]; unfold a03ZeroModeGCDInitialMNHKernel; ring)))
  apply ae_of_all
  intro p
  have hbnd := a03GCDInitialArithmetic_norm_le hε α hα ha hb
    (u := a03GCDMellinU ε p) (v := a03GCDMellinV ε p) (s := a03GCDMellinS ε p)
    (by simp [a03GCDMellinU]) (by simp [a03GCDMellinV]) (by simp [a03GCDMellinS]) k
  unfold a03ZeroModeGCDInitialMNHKernel
  rw [mul_assoc,norm_mul]
  exact (mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem a03ZeroModeGCDInitialMNHKernel_integral_norm_summable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    Summable (fun k : (ℕ×ℕ)×ℕ => ∫ p : A03GCDMellinCoordinates,
      ‖a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) k‖ ∂a03GCDMellinMeasure) := by
  have hBase := a03ZeroModeGCDInitialBase_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B
  let M : ℝ := ∫ p : A03GCDMellinCoordinates,‖a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1
    (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)‖ ∂a03GCDMellinMeasure
  apply ((a03GCDCountableMajorant_summable hε).mul_right M).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro k
  have hInt := a03ZeroModeGCDInitialMNHKernel_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B k
  calc
    _≤∫ p : A03GCDMellinCoordinates,a03GCDCountableMajorant ε k*
      ‖a03ZeroModeGCDInitialBase Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)‖ ∂a03GCDMellinMeasure := by
      apply integral_mono_ae hInt.norm (hBase.norm.const_mul _)
      apply ae_of_all
      intro p
      dsimp only []
      have hbnd := a03GCDInitialArithmetic_norm_le hε α hα ha hb
        (u := a03GCDMellinU ε p) (v := a03GCDMellinV ε p) (s := a03GCDMellinS ε p)
        (by simp [a03GCDMellinU]) (by simp [a03GCDMellinV]) (by simp [a03GCDMellinS]) k
      unfold a03ZeroModeGCDInitialMNHKernel
      rw [mul_assoc,norm_mul]
      exact (mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)).trans_eq (mul_comm _ _)
    _=a03GCDCountableMajorant ε k*M := integral_const_mul _ _

theorem a03ShiftedPowerArithmetic_tsum {s : ℂ} (hs : 1<s.re) :
    (∑' n : ℕ,shiftedPowerArithmetic s n)=riemannZeta s := by
  rw [←LSeries_one_eq_riemannZeta hs]
  unfold LSeries
  apply tsum_congr
  intro n
  rw [LSeries.term_def]
  by_cases hn : n=0
  · simp [hn]
  · simp only [hn,ite_false,shiftedPowerArithmetic_apply _ hn,Pi.one_apply,
      one_div,Complex.cpow_neg]

theorem a03ZeroModeGCDInitialMNHKernel_norm_summable
    {ε : ℝ} (hε : 0<ε) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8) {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (A B : ℕ→ℂ) (x : ℝ) {u v s : ℂ} (hu : u.re=ε) (hv : v.re=ε) (hs : s.re=1+ε) :
    Summable (fun k : (ℕ×ℕ)×ℕ => ‖a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B x u v s k‖) := by
  apply ((a03GCDCountableMajorant_summable hε).mul_left
    ‖a03ZeroModeGCDInitialBase Φ T σ α a b A B x u v s‖).of_nonneg_of_le
      (fun _ => norm_nonneg _)
  intro k
  unfold a03ZeroModeGCDInitialMNHKernel
  rw [mul_assoc,norm_mul]
  exact mul_le_mul_of_nonneg_left (a03GCDInitialArithmetic_norm_le hε α hα ha hb hu hv hs k) (norm_nonneg _)

theorem a03ZeroModeGCDInitialMNHKernel_tsum
    {ε : ℝ} (hε : 0<ε) (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8) {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (A B : ℕ→ℂ) (x : ℝ) {u v s : ℂ} (hu : u.re=ε) (hv : v.re=ε) (hs : s.re=1+ε) :
    (∑' k : (ℕ×ℕ)×ℕ,a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B x u v s k)=
      a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s := by
  have hsum := (a03ZeroModeGCDInitialMNHKernel_norm_summable hε Φ T σ α hα ha hb A B x hu hv hs).of_norm
  rw [hsum.tsum_prod]
  unfold a03ZeroModeGCDInitialMNHKernel a03ZeroModeGCDInitialKernel a03GCDDirichlet
  simp_rw [mul_assoc,tsum_mul_left,tsum_mul_right,a03ShiftedPowerArithmetic_tsum (by rw [hs]; linarith : 1<s.re)]
  rw [tsum_mul_left]

theorem a03ZeroModeGCDInitialMNHKernel_countable_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    Integrable (fun q : ((ℕ×ℕ)×ℕ)×A03GCDMellinCoordinates =>
      a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B q.2.1
        (a03GCDMellinU ε q.2) (a03GCDMellinV ε q.2) (a03GCDMellinS ε q.2) q.1)
      (Measure.count.prod a03GCDMellinMeasure) := by
  let F : ((ℕ×ℕ)×ℕ)×A03GCDMellinCoordinates→ℂ := fun q =>
    a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B q.2.1
      (a03GCDMellinU ε q.2) (a03GCDMellinV ε q.2) (a03GCDMellinS ε q.2) q.1
  let Ft : ((ℕ×ℕ)×ℕ)×A03GCDMellinCoordinates→ℂ := fun q =>
    a03ZeroModeGCDInitialTimeBase Φ T σ α a b A B q.2.1
      (a03GCDMellinU ε q.2) (a03GCDMellinV ε q.2) (a03GCDMellinS ε q.2)*
        (shiftedPowerArithmetic (a03GCDMellinS ε q.2) q.1.2*
          a03GCDDirichletTerm a b (α 0-α 1+2*a03GCDMellinU ε q.2)
            (α 2-α 3+2*a03GCDMellinV ε q.2) (a03GCDMellinS ε q.2) q.1.1)
  have hFt : Measurable Ft := by
    apply measurable_from_prod_countable_right
    intro k
    have hU : Measurable (a03GCDMellinU ε) := by unfold a03GCDMellinU; fun_prop
    have hV : Measurable (a03GCDMellinV ε) := by unfold a03GCDMellinV; fun_prop
    have hS : Measurable (a03GCDMellinS ε) := by unfold a03GCDMellinS; fun_prop
    exact (a03ZeroModeGCDInitialTimeBase_measurable Φ hΦ.continuous.measurable T ε σ α a b A B).mul
      (a03GCDInitialArithmetic_measurable_comp α a b hU hV hS k)
  have hPos : ∀ᵐ p : A03GCDMellinCoordinates ∂a03GCDMellinMeasure,0<p.1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  have hPos2 : ∀ᵐ q : ((ℕ×ℕ)×ℕ)×A03GCDMellinCoordinates ∂(Measure.count.prod a03GCDMellinMeasure),0<q.2.1 :=
    Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hPos
  have hMeas : AEStronglyMeasurable F (Measure.count.prod a03GCDMellinMeasure) := by
    apply hFt.aestronglyMeasurable.congr
    filter_upwards [hPos2] with q hq
    dsimp [Ft,F]
    unfold a03ZeroModeGCDInitialTimeBase a03ZeroModeGCDInitialMNHKernel a03ZeroModeGCDInitialBase
    rw [a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ (by norm_num : 0<(1:ℕ)) ha hb hq
      (by simp [a03GCDMellinS]; linarith)]
    ring
  apply (integrable_prod_iff hMeas).mpr
  refine ⟨ae_of_all _ (fun k => a03ZeroModeGCDInitialMNHKernel_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B k),?_⟩
  apply integrable_count_iff.mpr
  apply (a03ZeroModeGCDInitialMNHKernel_integral_norm_summable hΦ hSupp hT hε hε1 σ α hα ha hb A B).congr
  intro k
  exact (Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))).symm

theorem a03ZeroModeGCDInitialKernel_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    Integrable (fun p : A03GCDMellinCoordinates => a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)) a03GCDMellinMeasure := by
  have hJoint := a03ZeroModeGCDInitialMNHKernel_countable_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B
  apply hJoint.integral_prod_right.congr
  apply ae_of_all
  intro p
  change (∫ k : (ℕ×ℕ)×ℕ,a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
    (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) k ∂Measure.count)=
      a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)
  have hsum := a03ZeroModeGCDInitialMNHKernel_norm_summable hε Φ T σ α hα ha hb A B p.1
    (u := a03GCDMellinU ε p) (v := a03GCDMellinV ε p) (s := a03GCDMellinS ε p)
    (by simp [a03GCDMellinU]) (by simp [a03GCDMellinV]) (by simp [a03GCDMellinS])
  rw [integral_countable (integrable_count_iff.mpr hsum)]
  simp only [count_real_singleton,one_smul]
  exact a03ZeroModeGCDInitialMNHKernel_tsum hε Φ T σ α hα ha hb A B p.1
    (by simp [a03GCDMellinU]) (by simp [a03GCDMellinV]) (by simp [a03GCDMellinS])

theorem a03ZeroModeGCDInitialMNHKernel_integral_tsum
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    (∑' k : (ℕ×ℕ)×ℕ,∫ p : A03GCDMellinCoordinates,
      a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) k ∂a03GCDMellinMeasure)=
      ∫ p : A03GCDMellinCoordinates,a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ∂a03GCDMellinMeasure := by
  rw [integral_tsum_of_summable_integral_norm
    (a03ZeroModeGCDInitialMNHKernel_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B)
    (a03ZeroModeGCDInitialMNHKernel_integral_norm_summable hΦ hSupp hT hε hε1 σ α hα ha hb A B)]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  exact a03ZeroModeGCDInitialMNHKernel_tsum hε Φ T σ α hα ha hb A B p.1
    (by simp [a03GCDMellinU]) (by simp [a03GCDMellinV]) (by simp [a03GCDMellinS])

def a03GCDMellinRotate : A03GCDMellinCoordinates ≃ᵐ (ℝ×(ℝ×(ℝ×ℝ))) :=
  (((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.prodAssoc.symm : (ℝ×(ℝ×ℝ)) ≃ᵐ ((ℝ×ℝ)×ℝ))).trans
      (MeasurableEquiv.prodAssoc.symm : (ℝ×((ℝ×ℝ)×ℝ)) ≃ᵐ ((ℝ×(ℝ×ℝ))×ℝ))).trans
        MeasurableEquiv.prodComm

theorem a03GCDMellinRotate_measurePreserving :
    MeasurePreserving a03GCDMellinRotate a03GCDMellinMeasure
      (volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))) := by
  have h1 := (MeasurePreserving.id (volume.restrict (Ioi (0:ℝ)))).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)))
  have h2 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume.restrict (Ioi (0:ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) (volume : Measure ℝ))
  exact Measure.measurePreserving_swap.comp (h2.comp h1)

theorem a03ZeroModeGCDInitialKernel_joint_integrable_s_outer
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    Integrable (fun q : ℝ×(ℝ×(ℝ×ℝ)) => a03ZeroModeGCDInitialKernel Φ T σ α a b A B q.2.1
      ((ε:ℂ)+(q.2.2.1:ℂ)*I) ((ε:ℂ)+(q.2.2.2:ℂ)*I) (((1+ε:ℝ):ℂ)+(q.1:ℂ)*I))
      (volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))) := by
  apply (a03GCDMellinRotate_measurePreserving.integrable_comp_emb a03GCDMellinRotate.measurableEmbedding).mp
  exact a03ZeroModeGCDInitialKernel_joint_integrable hΦ hSupp hT hε hε1 σ α hα ha hb A B

end
end SixthMoment.Source

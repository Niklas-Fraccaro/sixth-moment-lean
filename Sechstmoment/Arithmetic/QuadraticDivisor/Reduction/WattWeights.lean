import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WattProfiles
import Std



namespace DivisorProof
open Real MeasureTheory Set Finset Classical Filter
open scoped BigOperators ContDiff Topology
noncomputable section
set_option maxHeartbeats 2000000

def positiveFrequencyTransition (t : ℝ) : ℝ := Real.smoothTransition (2*t-1)

theorem positiveFrequencyTransition_smooth : ContDiff ℝ ∞ positiveFrequencyTransition := by
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id |>.sub contDiff_const)

theorem positiveFrequencyTransition_zero {t : ℝ} (ht : t ≤ 1/2) :
    positiveFrequencyTransition t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

theorem positiveFrequencyTransition_one {t : ℝ} (ht : 1 ≤ t) :
    positiveFrequencyTransition t = 1 := Real.smoothTransition.one_of_one_le (by linarith)

theorem positiveFrequencyTransition_norm (t : ℝ) : ‖positiveFrequencyTransition t‖ ≤ 1 := by
  unfold positiveFrequencyTransition
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem positiveFrequencyTransition_derivative_zero {j : ℕ} (hj : j ≠ 0)
    {t : ℝ} (ht : t ∉ Icc (1/2:ℝ) 1) :
    iteratedDeriv j positiveFrequencyTransition t = 0 := by
  have hh : t < 1/2 ∨ 1 < t := by simpa only [Set.mem_Icc,not_and_or,not_le] using ht
  rcases hh with ht | ht
  · have he : positiveFrequencyTransition =ᶠ[𝓝 t] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with y hy
      exact positiveFrequencyTransition_zero hy.le
    simpa only [iteratedDeriv_const,hj,ite_false] using he.iteratedDeriv_eq j
  · have he : positiveFrequencyTransition =ᶠ[𝓝 t] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy
      exact positiveFrequencyTransition_one hy.le
    simpa only [iteratedDeriv_const,hj,ite_false] using he.iteratedDeriv_eq j

theorem positiveFrequencyTransition_derivative_bounds :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧ ∀ j t, 0 < t →
      ‖iteratedDeriv j positiveFrequencyTransition t‖ ≤ b j*t^(-(j:ℝ)) := by
  have hex (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t →
      ‖iteratedDeriv j positiveFrequencyTransition t‖ ≤ C*t^(-(j:ℝ)) := by
    by_cases hj : j = 0
    · refine ⟨1,by norm_num,?_⟩
      intro t _
      simpa only [hj,iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one]
        using positiveFrequencyTransition_norm t
    obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/2:ℝ) 1)).exists_bound_of_continuousOn
      (positiveFrequencyTransition_smooth.continuous_iteratedDeriv j (by exact_mod_cast le_top)).continuousOn
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro t ht
    by_cases hts : t ∈ Icc (1/2:ℝ) 1
    · have hp : 1 ≤ t^(-(j:ℝ)) := by
        rw [Real.rpow_neg ht.le]
        exact (one_le_inv₀ (Real.rpow_pos_of_pos ht _)).mpr
          (Real.rpow_le_one ht.le hts.2 (Nat.cast_nonneg _))
      exact ((hC t hts).trans (le_max_left _ _)).trans
        (le_mul_of_one_le_right (le_max_right _ _) hp)
    · rw [positiveFrequencyTransition_derivative_zero hj hts,norm_zero]
      positivity
  choose b hb hder using hex
  exact ⟨b,hb,hder⟩

theorem norm_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (fun t => (f t:ℂ)) t‖ = ‖iteratedDeriv j f t‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)

theorem smooth_real_weight_scaled_derivative {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (fun t => (f (a*t):ℂ)) t‖ =
      a^j*‖iteratedDeriv j f (a*t)‖ := by
  have hfc : ContDiff ℝ ∞ (fun t => (f t:ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  rw [iteratedDeriv_comp_const_smul (hfc.of_le (by exact_mod_cast le_top)) a]
  dsimp only
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg ha.le _),norm_iteratedDeriv_ofReal hf]

theorem smooth_real_weight_multiplicative_derivative {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hs : tsupport f ⊆ Icc (-R) R) {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hder : ∀ j t, ‖iteratedDeriv j f t‖ ≤ b j)
    (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv j (fun t => (f (a*t):ℂ)) t‖ ≤ (R^j*b j)*t^(-(j:ℝ)) := by
  have hb0 := hb j
  rw [smooth_real_weight_scaled_derivative hf ha]
  by_cases hz : iteratedDeriv j f (a*t) = 0
  · rw [hz,norm_zero,mul_zero]; positivity
  have hne : iteratedFDeriv ℝ j f (a*t) ≠ 0 := by
    intro hh
    have hn := norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := j) (f := f) (x := a*t)
    rw [hh,norm_zero] at hn
    exact hz (norm_eq_zero.mp hn.symm)
  have hupper := (hs (support_iteratedFDeriv_subset j hne)).2
  have hap : a ≤ R/t := (le_div_iff₀ ht).mpr hupper
  have hp : a^j ≤ R^j*t^(-(j:ℝ)) := by
    rw [Real.rpow_neg ht.le,Real.rpow_natCast,← div_eq_mul_inv,← div_pow]
    exact pow_le_pow_left₀ ha.le hap _
  calc _ ≤ (R^j*t^(-(j:ℝ)))*b j := mul_le_mul hp (hder j (a*t)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def derivativeProductBound (a b : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1), (j.choose i:ℝ)*a i*b (j-i)

theorem derivativeProductBound_nonneg {a b : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    0 ≤ derivativeProductBound a b j := by
  apply sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i)) (hb (j-i))

theorem multiplicative_derivative_product {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {a b : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hdf : ∀ j t, 0 < t → ‖iteratedDeriv j f t‖ ≤ a j*t^(-(j:ℝ)))
    (hdg : ∀ j t, 0 < t → ‖iteratedDeriv j g t‖ ≤ b j*t^(-(j:ℝ)))
    (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv j (fun t => f t*g t) t‖ ≤ derivativeProductBound a b j*t^(-(j:ℝ)) := by
  rw [iteratedDeriv_fun_mul (hf.of_le (by exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold derivativeProductBound
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hij : i ≤ j := Nat.le_of_lt_succ (mem_range.mp hi)
  have he : t^(-(i:ℝ))*t^(-((j-i:ℕ):ℝ)) = t^(-(j:ℝ)) := by
    rw [← Real.rpow_add ht,Nat.cast_sub hij]
    congr 1
    ring
  simp only [norm_mul,Complex.norm_natCast]
  calc _ ≤ (j.choose i:ℝ)*(a i*t^(-(i:ℝ)))*(b (j-i)*t^(-((j-i:ℕ):ℝ))) := by
        have ha0 := ha i
        have hb0 := hb (j-i)
        gcongr
        · exact hdf i t ht
        · exact hdg (j-i) t ht
    _ = _ := by
      calc _ = ((j.choose i:ℝ)*a i*b (j-i))*(t^(-(i:ℝ))*t^(-((j-i:ℕ):ℝ))) := by ring
        _ = _ := by rw [he]

theorem ePhase_hasDerivAt (u t : ℝ) :
    HasDerivAt (fun t => ePhase (u*t)) ((2*(Real.pi:ℂ)*Complex.I*(u:ℂ))*ePhase (u*t)) t := by
  have hd := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
    (2*(Real.pi:ℂ)*Complex.I*(u:ℂ))).cexp)
  simpa only [ePhase,Complex.ofReal_mul,Complex.ofRealCLM_apply,
    Complex.ofReal_one,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hd

theorem ePhase_iteratedDeriv (u : ℝ) (j : ℕ) :
    iteratedDeriv j (fun t => ePhase (u*t)) =
      fun t => (2*(Real.pi:ℂ)*Complex.I*(u:ℂ))^j*ePhase (u*t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [deriv_const_mul_field,(ePhase_hasDerivAt u t).deriv,pow_succ]
    ring

theorem ePhase_iteratedDeriv_norm (u : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv j (fun t => ePhase (u*t)) t‖ = (2*Real.pi*|u|)^j := by
  rw [ePhase_iteratedDeriv]
  simp [norm_pow,norm_ePhase]

theorem sourceCutoff_derivative_bounds :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧ ∀ j t, ‖iteratedDeriv j sourceCutoff t‖ ≤ b j := by
  have hex (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv j sourceCutoff t‖ ≤ C := by
    obtain ⟨C,hC⟩ := (sourceCutoff_hasCompactSupport.iteratedFDeriv j).exists_bound_of_continuous
      (sourceCutoff_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro t
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hC t).trans (le_max_left _ _)
  choose b hb hder using hex
  exact ⟨b,hb,hder⟩

theorem sourceCutoff_tsupport_subset : tsupport sourceCutoff ⊆ Icc (-2:ℝ) 2 := by
  rw [show tsupport sourceCutoff = Metric.closedBall (0:ℝ) 2 from sourceBump.tsupport_eq]
  intro t ht
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_le,Set.mem_Icc] using ht

def positiveFrequencyProfile (L : ℝ) (t : ℝ) : ℂ :=
  (positiveFrequencyTransition t:ℂ)*(sourceCutoff (t/L):ℂ)

theorem positiveFrequencyProfile_smooth (L : ℝ) : ContDiff ℝ ∞ (positiveFrequencyProfile L) := by
  unfold positiveFrequencyProfile
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp positiveFrequencyTransition_smooth
  · exact Complex.ofRealCLM.contDiff.comp (sourceCutoff_contDiff.comp (contDiff_id.div_const _))

theorem positiveFrequencyProfile_support {L : ℝ} (hL : 0 < L) :
    tsupport (positiveFrequencyProfile L) ⊆ Icc (1/2) (2*L) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hθ : positiveFrequencyTransition t ≠ 0 := by
    intro hz; exact ht (by simp [positiveFrequencyProfile,hz])
  have hχ : sourceCutoff (t/L) ≠ 0 := by
    intro hz; exact ht (by simp [positiveFrequencyProfile,hz])
  have htlo : 1/2 < t := by
    by_contra hh; exact hθ (positiveFrequencyTransition_zero (not_lt.mp hh))
  refine ⟨htlo.le,?_⟩
  by_contra hh
  apply hχ
  apply sourceCutoff_zero
  rw [abs_of_pos (div_pos (by linarith) hL)]
  exact (le_div_iff₀ hL).mpr (by linarith)

theorem positiveFrequencyProfile_nat {L : ℝ} {n : ℕ} (hn : 0 < n) :
    positiveFrequencyProfile L n = (sourceCutoff ((n:ℝ)/L):ℂ) := by
  rw [positiveFrequencyProfile,positiveFrequencyTransition_one (by exact_mod_cast hn),
    Complex.ofReal_one,one_mul]

theorem positiveFrequencyProfile_derivative_bounds :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧ ∀ L : ℝ, 0 < L → ∀ j t, 0 < t →
      ‖iteratedDeriv j (positiveFrequencyProfile L) t‖ ≤ b j*t^(-(j:ℝ)) := by
  obtain ⟨a,ha,hθ⟩ := positiveFrequencyTransition_derivative_bounds
  obtain ⟨c,hc,hχ⟩ := sourceCutoff_derivative_bounds
  let bχ : ℕ → ℝ := fun j => 2^j*c j
  have hbχ (j : ℕ) : 0 ≤ bχ j := by dsimp [bχ]; exact mul_nonneg (by positivity) (hc j)
  refine ⟨derivativeProductBound a bχ,derivativeProductBound_nonneg ha hbχ,?_⟩
  intro L hL j t ht
  apply multiplicative_derivative_product
    (Complex.ofRealCLM.contDiff.comp positiveFrequencyTransition_smooth)
    (Complex.ofRealCLM.contDiff.comp (sourceCutoff_contDiff.comp (contDiff_id.div_const L)))
    ha hbχ _ _ j ht
  · intro i y hy
    change ‖iteratedDeriv i (fun t => (positiveFrequencyTransition t:ℂ)) y‖ ≤ _
    rw [norm_iteratedDeriv_ofReal positiveFrequencyTransition_smooth]
    exact hθ i y hy
  · intro i y hy
    have he : (fun t : ℝ => (sourceCutoff (t/L):ℂ)) =
        fun t => (sourceCutoff (L⁻¹*t):ℂ) := by funext t; congr 2; ring
    change ‖iteratedDeriv i (fun t => (sourceCutoff (t/L):ℂ)) y‖ ≤ _
    rw [he]
    exact smooth_real_weight_multiplicative_derivative sourceCutoff_contDiff
      (by norm_num : (0:ℝ) < 2) (inv_pos.mpr hL) sourceCutoff_tsupport_subset hc hχ i hy

def oscillatoryDerivativeBound (a : ℕ → ℝ) (K : ℝ) : ℕ → ℝ :=
  derivativeProductBound a (fun j => (4*Real.pi*K)^j)

theorem oscillatory_profile_derivative {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {L K E x : ℝ}
    (_hL : 0 < L) (hK : 0 ≤ K) (hE : 1 ≤ E) (hx : L*|x| ≤ K*E)
    (hs : tsupport f ⊆ Icc (1/2) (2*L)) {a : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j)
    (hdf : ∀ j t, 0 < t → ‖iteratedDeriv j f t‖ ≤ a j*t^(-(j:ℝ)))
    (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv j (fun t => f t*ePhase (x*t)) t‖ ≤
      oscillatoryDerivativeBound a K j*E^j*t^(-(j:ℝ)) := by
  have he : ContDiff ℝ ∞ (fun t => ePhase (x*t)) := by
    unfold ePhase
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))).cexp
  rw [iteratedDeriv_fun_mul (hf.of_le (by exact_mod_cast le_top)).contDiffAt
    (he.of_le (by exact_mod_cast le_top)).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold oscillatoryDerivativeBound derivativeProductBound
  rw [sum_mul,sum_mul]
  apply sum_le_sum
  intro i hi
  have hij : i ≤ j := Nat.le_of_lt_succ (mem_range.mp hi)
  have ha0 := ha i
  simp only [norm_mul,Complex.norm_natCast,ePhase_iteratedDeriv_norm]
  by_cases hz : iteratedDeriv i f t = 0
  · rw [hz,norm_zero,mul_zero,zero_mul]; positivity
  have hne : iteratedFDeriv ℝ i f t ≠ 0 := by
    intro hh
    have hn := norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := i) (f := f) (x := t)
    rw [hh,norm_zero] at hn
    exact hz (norm_eq_zero.mp hn.symm)
  have htL := (hs (support_iteratedFDeriv_subset i hne)).2
  have hphase : 2*Real.pi*|x| ≤ (4*Real.pi*K*E)/t := by
    apply (le_div_iff₀ ht).mpr
    have hx' := mul_le_mul_of_nonneg_right htL (abs_nonneg x)
    nlinarith [Real.pi_pos]
  have hp : (2*Real.pi*|x|)^(j-i) ≤
      (4*Real.pi*K)^(j-i)*E^j*t^(-((j-i:ℕ):ℝ)) := by
    calc _ ≤ ((4*Real.pi*K*E)/t)^(j-i) := pow_le_pow_left₀ (by positivity) hphase _
      _ = (4*Real.pi*K)^(j-i)*E^(j-i)*t^(-((j-i:ℕ):ℝ)) := by
        rw [div_pow,mul_pow,Real.rpow_neg ht.le,Real.rpow_natCast]; ring
      _ ≤ _ := by
        gcongr
        exact Nat.sub_le j i
  have hpow : t^(-(i:ℝ))*t^(-((j-i:ℕ):ℝ)) = t^(-(j:ℝ)) := by
    rw [← Real.rpow_add ht,Nat.cast_sub hij]
    congr 1
    ring
  calc _ ≤ (j.choose i:ℝ)*(a i*t^(-(i:ℝ)))*
      ((4*Real.pi*K)^(j-i)*E^j*t^(-((j-i:ℕ):ℝ))) := by gcongr; exact hdf i t ht
    _ = _ := by
      calc _ = ((j.choose i:ℝ)*a i*(4*Real.pi*K)^(j-i))*E^j*
          (t^(-(i:ℝ))*t^(-((j-i:ℕ):ℝ))) := by ring
        _ = _ := by rw [hpow]

def wattShiftWeight (q : QuadraticScales) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (t : ℝ) : ℂ :=
  (W 0 ((d:ℝ)*t/q.H):ℂ)

def wattFrequencyWeight (q : QuadraticScales) (ρ : ℝ) (d : ℕ)
    (x : ℝ) (frequencyPositive : Bool) (t : ℝ) : ℂ :=
  positiveFrequencyProfile (poissonLength q ρ d) t*
    ePhase ((if frequencyPositive then x else -x)*t)

theorem wattShiftWeight_smooth {q : QuadraticScales} {W : Fin 5 → ℝ → ℝ}
    (hW : SmoothDyadicWeight (W 0)) (d : ℕ) : ContDiff ℝ ∞ (wattShiftWeight q W d) := by
  exact Complex.ofRealCLM.contDiff.comp
    (hW.1.comp ((contDiff_const.mul contDiff_id).div_const q.H))

theorem wattFrequencyWeight_smooth (q : QuadraticScales) (ρ : ℝ) (d : ℕ)
    (x : ℝ) (frequencyPositive : Bool) :
    ContDiff ℝ ∞ (wattFrequencyWeight q ρ d x frequencyPositive) := by
  apply (positiveFrequencyProfile_smooth _).mul
  unfold ePhase
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id))).cexp

theorem wattShiftWeight_support {q : QuadraticScales} {W : Fin 5 → ℝ → ℝ}
    (hW : SmoothDyadicWeight (W 0)) (hH : 0 < q.H) {d : ℕ} (hd : 0 < d)
    (hscale : 1 ≤ 2*q.H/(d:ℝ)) :
    tsupport (wattShiftWeight q W d) ⊆ Icc (1/2) (2*q.H/(d:ℝ)) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hwne : W 0 ((d:ℝ)*t/q.H) ≠ 0 := by
    intro hz; exact ht (by simp [wattShiftWeight,hz])
  have hs := dyadic_weight_argument_bounds hW hH hwne
  refine ⟨?_,(le_div_iff₀ hdr).mpr (by nlinarith [hs.2])⟩
  have hlo := (le_div_iff₀ hdr).mp hscale
  nlinarith [hs.1]

theorem wattFrequencyWeight_support {q : QuadraticScales} {ρ : ℝ} {d : ℕ}
    (hL : 0 < poissonLength q ρ d) (x : ℝ) (frequencyPositive : Bool) :
    tsupport (wattFrequencyWeight q ρ d x frequencyPositive) ⊆
      Icc (1/2) (2*poissonLength q ρ d) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  apply positiveFrequencyProfile_support hL
  apply subset_tsupport
  intro hz
  exact ht (by simp [wattFrequencyWeight,hz])

theorem inverse_scale_derivative_identity {E t : ℝ} (hE : 0 < E) (ht : 0 < t) (j : ℕ) :
    E^j*t^(-(j:ℝ)) = (E⁻¹*t)^(-(j:ℝ)) := by
  rw [Real.rpow_neg ht.le,Real.rpow_neg (by positivity : 0 ≤ E⁻¹*t),
    Real.rpow_natCast,Real.rpow_natCast,mul_pow]
  simp only [mul_inv_rev,inv_pow,inv_inv]
  ring

theorem actualWatt_frequency_weight_bounds {ρ K : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
        ScaleGeometry ρ K q → NormalizedWeightData bounds q α β W →
        ∀ d : ℕ, 0 < d → ∀ x : ℝ,
          x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d) →
          ∀ frequencyPositive : Bool, ∀ j t, 0 < t →
            ‖iteratedDeriv j (wattShiftWeight q W d) t‖+
              ‖iteratedDeriv j (wattFrequencyWeight q ρ d x frequencyPositive) t‖ ≤
                b j*(q.mass^(-10*ρ)*t)^(-(j:ℝ)) := by
  obtain ⟨a,ha,hprofile⟩ := positiveFrequencyProfile_derivative_bounds
  let bshift : ℕ → ℝ := fun j => 2^j*bounds j
  let bfrequency := oscillatoryDerivativeBound a (2*K)
  have hshift (j : ℕ) : 0 ≤ bshift j := mul_nonneg (by positivity) (hb j)
  have hfrequency (j : ℕ) : 0 ≤ bfrequency j :=
    derivativeProductBound_nonneg ha (fun i => pow_nonneg (by positivity) i) j
  refine ⟨fun j => bshift j+bfrequency j,fun j => add_nonneg (hshift j) (hfrequency j),?_⟩
  intro q α β W h hw d hd x hx frequencyPositive j t ht
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hL := poissonLength_pos q h.scales ρ hdr
  let E := q.mass^(10*ρ)
  have hEp : 0 < E := Real.rpow_pos_of_pos hQ _
  have hE : 1 ≤ E := Real.one_le_rpow (poisson_scale_bounds q h.scales).1 (by positivity)
  have hΔ : q.mass^(-10*ρ) = E⁻¹ := by
    dsimp [E]
    rw [show -10*ρ = -(10*ρ) by ring,Real.rpow_neg hQ.le]
  have hw0support : tsupport (W 0) ⊆ Icc (-2:ℝ) 2 := by
    intro y hy
    have hs := (hw.smooth 0).2 hy
    exact ⟨by linarith [hs.1],hs.2⟩
  have hu₀ := smooth_real_weight_multiplicative_derivative (hw.smooth 0).1
    (by norm_num : (0:ℝ) < 2) (div_pos hdr hH) hw0support hb
    (fun i y => hw.derivatives i 0 y) j ht
  have heq : (fun t : ℝ => (W 0 (((d:ℝ)/q.H)*t):ℂ)) = wattShiftWeight q W d := by
    funext y; unfold wattShiftWeight; congr 2; ring
  rw [heq] at hu₀
  have hxp : 0 ≤ x := by
    have hr := poissonRadius_pos q h.scales hdr
    linarith [hx.1]
  have hspatial : poissonLength q ρ d*|if frequencyPositive then x else -x| ≤ (2*K)*E := by
    have hrad := poissonLength_radius_le h hK hdr
    have habs : |if frequencyPositive then x else -x| = x := by
      cases frequencyPositive <;> simp [abs_of_nonneg hxp]
    rw [habs]
    calc _ ≤ poissonLength q ρ d*(2*poissonRadius q d) := mul_le_mul_of_nonneg_left hx.2 hL.le
      _ ≤ _ := by dsimp [E]; nlinarith
  have hu₁ := oscillatory_profile_derivative (positiveFrequencyProfile_smooth _)
    hL (by positivity : 0 ≤ 2*K) hE hspatial (positiveFrequencyProfile_support hL) ha
    (hprofile _ hL) j ht
  change ‖iteratedDeriv j (wattFrequencyWeight q ρ d x frequencyPositive) t‖ ≤
    bfrequency j*E^j*t^(-(j:ℝ)) at hu₁
  rw [hΔ,← inverse_scale_derivative_identity hEp ht j]
  calc _ ≤ (bshift j*t^(-(j:ℝ)))*E^j+bfrequency j*E^j*t^(-(j:ℝ)) := by
        apply add_le_add _ hu₁
        exact hu₀.trans (le_mul_of_one_le_right
          (mul_nonneg (hshift j) (Real.rpow_nonneg ht.le _)) (one_le_pow₀ hE))
    _ = _ := by ring

end
end DivisorProof




namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1600000

def actualWattCoefficient (α : ℕ → ℂ) (d₁ d₂ r : ℕ) : ℂ :=
  if r.Coprime d₂ then α (d₁*r) else 0

def actualWattGamma (q : QuadraticScales) (W : Fin 5 → ℝ → ℝ)
    (d₁ d₂ d₃ d₄ : ℕ) (x : ℝ) (r s : ℕ) (v p : ℝ) : ℂ :=
  if (r:ℝ) ≤ 2*q.A/(d₁:ℝ) ∧ (s:ℝ) ≤ 2*q.B/(d₃:ℝ) then
    separatedWattProfile W ((d₂:ℝ)/q.M₁) ((r:ℝ)*x/q.N₂)
      ((d₄:ℝ)/q.N₁) ((s:ℝ)*x/q.M₂) v p else 0

theorem actualWattCoefficient_norm {α : ℕ → ℂ} (hα : ∀ n, ‖α n‖ ≤ 1)
    (d₁ d₂ r : ℕ) : ‖actualWattCoefficient α d₁ d₂ r‖ ≤ 1 := by
  unfold actualWattCoefficient
  split_ifs
  · exact hα _
  · simp

theorem actualWattCoefficient_support {α : ℕ → ℂ} {A : ℝ}
    (hα : ∀ n : ℕ, (n:ℝ) ∉ Icc A (2*A) → α n = 0)
    {d₁ : ℕ} (h₁ : 0 < d₁) (d₂ r : ℕ)
    (hr : (r:ℝ) ∉ Icc (A/(d₁:ℝ)) (2*A/(d₁:ℝ))) :
    actualWattCoefficient α d₁ d₂ r = 0 := by
  have h₁r : (0:ℝ) < d₁ := by exact_mod_cast h₁
  unfold actualWattCoefficient
  split_ifs
  · apply hα
    intro hh
    apply hr
    constructor
    · apply (div_le_iff₀ h₁r).mpr
      simpa only [Nat.cast_mul,mul_comm] using hh.1
    · apply (le_div_iff₀ h₁r).mpr
      simpa only [Nat.cast_mul,mul_comm] using hh.2
  · rfl

theorem separatedWattProfile_tsupport {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) :
    tsupport (fun z : ℝ × ℝ => separatedWattProfile W a b c d z.1 z.2) ⊆
      Icc (1/a) (2/a) ×ˢ Icc (1/c) (2/c) := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro z hz
  have hv : poissonProfile (W 1) (W 4) a b z.1 ≠ 0 := by
    intro hh; exact hz (by simp [separatedWattProfile,hh])
  have hp : poissonProfile (W 3) (W 2) c d z.2 ≠ 0 := by
    intro hh; exact hz (by simp [separatedWattProfile,hh])
  exact ⟨poissonProfile_tsupport_dyadic (hW 1) ha (subset_tsupport _ hv),
    poissonProfile_tsupport_dyadic (hW 3) hc (subset_tsupport _ hp)⟩

theorem actualWattGamma_smooth {q : QuadraticScales} {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) (d₁ d₂ d₃ d₄ : ℕ) (x : ℝ) (r s : ℕ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => actualWattGamma q W d₁ d₂ d₃ d₄ x r s z.1 z.2) := by
  unfold actualWattGamma
  split_ifs
  · exact separatedWattProfile_contDiff hW _ _ _ _
  · exact contDiff_const

theorem actualWattGamma_support {q : QuadraticScales} {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) (hM : 0 < q.M₁) (hN : 0 < q.N₁)
    (d₁ : ℕ) {d₂ : ℕ} (h₂ : 0 < d₂) (d₃ : ℕ) {d₄ : ℕ} (h₄ : 0 < d₄)
    (x : ℝ) (r s : ℕ) :
    tsupport (fun z : ℝ × ℝ => actualWattGamma q W d₁ d₂ d₃ d₄ x r s z.1 z.2) ⊆
      Icc (q.M₁/(d₂:ℝ)) (2*q.M₁/(d₂:ℝ)) ×ˢ Icc (q.N₁/(d₄:ℝ)) (2*q.N₁/(d₄:ℝ)) := by
  have h₂r : (0:ℝ) < d₂ := by exact_mod_cast h₂
  have h₄r : (0:ℝ) < d₄ := by exact_mod_cast h₄
  unfold actualWattGamma
  split_ifs
  · have hs := separatedWattProfile_tsupport hW (div_pos h₂r hM) (div_pos h₄r hN)
      (b := (r:ℝ)*x/q.N₂) (d := (s:ℝ)*x/q.M₂)
    convert hs using 1
    field_simp
  · change tsupport (0 : (ℝ × ℝ) → ℂ) ⊆ _
    simp only [tsupport_zero,Set.empty_subset]

def actualWattGammaBounds (bounds : ℕ → ℝ) (K : ℝ) (i j : ℕ) : ℝ :=
  (2^i*profileDerivativeBound bounds (4*K) i)*(2^j*profileDerivativeBound bounds (4*K) j)

theorem actualWattGammaBounds_nonneg {bounds : ℕ → ℝ} {K : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) (i j : ℕ) :
    0 ≤ actualWattGammaBounds bounds K i j := by
  have hi := profileDerivativeBound_nonneg hb (by positivity : 0 ≤ 4*K) i
  have hj := profileDerivativeBound_nonneg hb (by positivity : 0 ≤ 4*K) j
  unfold actualWattGammaBounds
  positivity

theorem actualWattGamma_derivatives {ρ K : ℝ} {q : QuadraticScales}
    {bounds : ℕ → ℝ} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hw : NormalizedWeightData bounds q α β W)
    {d d₁ d₂ d₃ d₄ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d) {x : ℝ}
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d))
    (r s i j : ℕ) {v p : ℝ} (hv : 0 < v) (hp : 0 < p) :
    ‖iteratedDeriv j (fun p => iteratedDeriv i
      (fun v => actualWattGamma q W d₁ d₂ d₃ d₄ x r s v p) v) p‖ ≤
        actualWattGammaBounds bounds K i j*v^(-(i:ℝ))*p^(-(j:ℝ)) := by
  have h₁r : (0:ℝ) < d₁ := by exact_mod_cast h₁
  have h₂r : (0:ℝ) < d₂ := by exact_mod_cast h₂
  have h₃r : (0:ℝ) < d₃ := by exact_mod_cast h₃
  have h₄r : (0:ℝ) < d₄ := by exact_mod_cast h₄
  have h₁₂r : (d₁:ℝ)*d₂ = d := by exact_mod_cast h₁₂
  have h₃₄r : (d₃:ℝ)*d₄ = d := by exact_mod_cast h₃₄
  have hG := actualWattGammaBounds_nonneg hw.bounds_nonneg (by linarith : 0 ≤ K) i j
  unfold actualWattGamma
  split_ifs with hactive
  · exact naturalWatt_gamma_mixed_bound h hK hw h₁r h₂r h₃r h₄r h₁₂r h₃₄r
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hactive.1 hactive.2 hx i j hv hp
  · simp only [iteratedDeriv_fun_const_zero,norm_zero]
    positivity

theorem actualWatt_weight_data {ρ K : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧
      ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
        ScaleGeometry ρ K q → NormalizedWeightData bounds q α β W →
        ∀ d d₁ d₂ d₃ d₄ : ℕ, 0 < d₁ → 0 < d₂ → 0 < d₃ → 0 < d₄ →
          d₁*d₂ = d → d₃*d₄ = d →
        let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
        (∀ i, 1 ≤ p.size i) → ∀ x : ℝ,
          x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d) →
          ∀ frequencyPositive : Bool,
            WattWeightData b (actualWattGammaBounds bounds K) p (q.mass^(-10*ρ))
              (actualWattCoefficient α d₁ d₂) (actualWattCoefficient β d₃ d₄)
              (wattShiftWeight q W d) (wattFrequencyWeight q ρ d x frequencyPositive)
              (actualWattGamma q W d₁ d₂ d₃ d₄ x) := by
  obtain ⟨b,hb',hder⟩ := actualWatt_frequency_weight_bounds hρ hK bounds hb
  refine ⟨b,hb',?_⟩
  intro q α β W h hw d d₁ d₂ d₃ d₄ h₁ h₂ h₃ h₄ h₁₂ h₃₄ p hscales x hx frequencyPositive
  have hd : 0 < d := h₁₂ ▸ Nat.mul_pos h₁ h₂
  have hM := h.pos.2.2.1
  have hN := h.pos.2.2.2.2.1
  have hH := h.pos.2.2.2.2.2.2.1
  have hL := poissonLength_pos q h.scales ρ (by exact_mod_cast hd : (0:ℝ) < d)
  have hR : Icc (p.R/2) p.R = Icc (q.A/(d₁:ℝ)) (2*q.A/(d₁:ℝ)) := by
    dsimp [p,naturalWattScales,WattScales.doubled]
    congr 1 <;> ring
  have hS : Icc (p.S/2) p.S = Icc (q.B/(d₃:ℝ)) (2*q.B/(d₃:ℝ)) := by
    dsimp [p,naturalWattScales,WattScales.doubled]
    congr 1 <;> ring
  have hV : Icc (p.V/2) p.V = Icc (q.M₁/(d₂:ℝ)) (2*q.M₁/(d₂:ℝ)) := by
    dsimp [p,naturalWattScales,WattScales.doubled]
    congr 1 <;> ring
  have hP : Icc (p.P/2) p.P = Icc (q.N₁/(d₄:ℝ)) (2*q.N₁/(d₄:ℝ)) := by
    dsimp [p,naturalWattScales,WattScales.doubled]
    congr 1 <;> ring
  refine ⟨?_,?_,actualWattCoefficient_norm hw.alpha_bound _ _,
    actualWattCoefficient_norm hw.beta_bound _ _,wattShiftWeight_smooth (hw.smooth 0) d,
    wattFrequencyWeight_smooth _ _ _ _ _,?_,?_,?_,?_,?_,?_⟩
  · intro n hn
    apply actualWattCoefficient_support hw.alpha_support h₁ d₂ n
    rwa [hR] at hn
  · intro n hn
    apply actualWattCoefficient_support hw.beta_support h₃ d₄ n
    rwa [hS] at hn
  · convert wattShiftWeight_support (hw.smooth 0) hH hd
      (by simpa [p,WattScales.size,naturalWattScales,WattScales.doubled,mul_div_assoc] using hscales 0) using 1
    dsimp [p,naturalWattScales,WattScales.doubled]
    rw [mul_div_assoc]
  · exact wattFrequencyWeight_support hL x frequencyPositive
  · exact hder q α β W h hw d hd x hx frequencyPositive
  · exact actualWattGamma_smooth hw.smooth _ _ _ _ _
  · intro r s
    rw [hV,hP]
    exact actualWattGamma_support hw.smooth hM hN d₁ h₂ d₃ h₄ x r s
  · intro r s i j v pp hv hp
    exact actualWattGamma_derivatives h hK hw h₁ h₂ h₃ h₄ h₁₂ h₃₄ hx r s i j hv hp

end
end DivisorProof




namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1800000

def wattLift (d d₁ d₃ : ℕ) (m : Fin 6 → ℕ) : Fin 5 → ℕ :=
  ![d₁*m 2,d₃*m 3,(d/d₁)*m 4,(d/d₃)*m 5,m 0]

def wattProject (d : ℕ) (n : Fin 5 → ℕ) (l : ℕ) : Fin 6 → ℕ :=
  ![n 4,l,splitCoefficient (n 0) d,splitCoefficient (n 1) d,
    splitInner (n 0) (n 2) d,splitInner (n 1) (n 3) d]

theorem wattLift_project {d : ℕ} (hd : 0 < d) (n : Fin 5 → ℕ) (l : ℕ)
    (hg : outerGCD n = d) :
    wattLift d (splitLeft (n 0) d) (splitLeft (n 1) d) (wattProject d n l) = n := by
  have hdiv₁ : d ∣ n 0*n 2 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
  have hdiv₂ : d ∣ n 1*n 3 := by rw [← hg]; exact Nat.gcd_dvd_right _ _
  funext i
  fin_cases i <;> dsimp [wattLift,wattProject]
  · exact split_coefficient_mul _ _
  · exact split_coefficient_mul _ _
  · exact split_inner_mul hd hdiv₁
  · exact split_inner_mul hd hdiv₂

theorem wattLift_gcd {d d₁ d₃ : ℕ} (h₁ : d₁ ∣ d) (h₃ : d₃ ∣ d)
    (m : Fin 6 → ℕ) (hcop : (m 2*m 4).Coprime (m 3*m 5)) :
    outerGCD (wattLift d d₁ d₃ m) = d := by
  have h₁₂ := Nat.mul_div_cancel' h₁
  have h₃₄ := Nat.mul_div_cancel' h₃
  have hl : (d₁*m 2)*((d/d₁)*m 4) = d*(m 2*m 4) := by
    calc _ = (d₁*(d/d₁))*(m 2*m 4) := by ring
      _ = _ := by rw [h₁₂]
  have hr : (d₃*m 3)*((d/d₃)*m 5) = d*(m 3*m 5) := by
    calc _ = (d₃*(d/d₃))*(m 3*m 5) := by ring
      _ = _ := by rw [h₃₄]
  change Nat.gcd ((d₁*m 2)*((d/d₁)*m 4)) ((d₃*m 3)*((d/d₃)*m 5)) = d
  rw [hl,hr,Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]

theorem wattProject_lift {d d₁ d₃ : ℕ} (hd : 0 < d)
    (h₁ : d₁ ∣ d) (h₃ : d₃ ∣ d) (m : Fin 6 → ℕ)
    (hr : (m 2).Coprime (d/d₁)) (hs : (m 3).Coprime (d/d₃)) :
    splitLeft (wattLift d d₁ d₃ m 0) d = d₁ ∧
      splitLeft (wattLift d d₁ d₃ m 1) d = d₃ ∧
      wattProject d (wattLift d d₁ d₃ m) (m 1) = m := by
  have h₁₂ : d = d₁*(d/d₁) := (Nat.mul_div_cancel' h₁).symm
  have h₃₄ : d = d₃*(d/d₃) := (Nat.mul_div_cancel' h₃).symm
  obtain ⟨he₁,_,hr₁,hv₁⟩ := split_decomposition_unique hd
    (show wattLift d d₁ d₃ m 0 = d₁*m 2 from rfl) h₁₂
    (show wattLift d d₁ d₃ m 2 = (d/d₁)*m 4 from rfl) hr
  obtain ⟨he₃,_,hs₁,hp₁⟩ := split_decomposition_unique hd
    (show wattLift d d₁ d₃ m 1 = d₃*m 3 from rfl) h₃₄
    (show wattLift d d₁ d₃ m 3 = (d/d₃)*m 5 from rfl) hs
  refine ⟨he₁,he₃,?_⟩
  funext i
  fin_cases i <;> dsimp only [wattProject] <;> first | assumption | rfl

def originalWattTerm (positive frequencyPositive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (d : ℕ) (x : ℝ) (n : Fin 5 → ℕ) (l : ℕ) : ℂ :=
  poissonOuterWeight q α β W n*outerPoissonProfile q W n x*
    (sourceCutoff ((l:ℝ)/poissonLength q ρ d):ℂ)*
      ePhase ((signedShift frequencyPositive l:ℝ)*x)*
        ePhase (-(signedShift frequencyPositive l:ℝ)*outerPoissonPhase positive n)

def concreteWattTerm (positive frequencyPositive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    (d d₁ d₃ : ℕ) (x : ℝ) (m : Fin 6 → ℕ) : ℂ :=
  wattShiftWeight q W d (m 0)*wattFrequencyWeight q ρ d x frequencyPositive (m 1)*
    actualWattCoefficient α d₁ (d/d₁) (m 2)*actualWattCoefficient β d₃ (d/d₃) (m 3)*
      actualWattGamma q W d₁ (d/d₁) d₃ (d/d₃) x (m 2) (m 3) (m 4) (m 5)*
        ePhase ((if positive != frequencyPositive then (1:ℝ) else -1)*(m 0:ℝ)*m 1*
          (inverseRepresentative (m 2*m 4) (m 3*m 5):ℝ)/(m 3*m 5:ℕ))

theorem originalWattTerm_lift (positive frequencyPositive : Bool)
    (q : QuadraticScales) (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ)
    {d d₁ d₃ : ℕ} (hd : 0 < d) (h₁ : d₁ ∣ d) (h₃ : d₃ ∣ d)
    (x : ℝ) (m : Fin 6 → ℕ) (hl : 0 < m 1)
    (hr : (m 2).Coprime (d/d₁)) (hs : (m 3).Coprime (d/d₃))
    (hcop : (m 2*m 4).Coprime (m 3*m 5))
    (hgate : (m 2:ℝ) ≤ 2*q.A/(d₁:ℝ) ∧ (m 3:ℝ) ≤ 2*q.B/(d₃:ℝ)) :
    originalWattTerm positive frequencyPositive q ρ α β W d x (wattLift d d₁ d₃ m) (m 1) =
      concreteWattTerm positive frequencyPositive q ρ α β W d d₁ d₃ x m := by
  have hg := wattLift_gcd h₁ h₃ m hcop
  have h₁₂ := Nat.mul_div_cancel' h₁
  have h₃₄ := Nat.mul_div_cancel' h₃
  have hleft : outerLeft (wattLift d d₁ d₃ m) = d*(m 2*m 4) := by
    change (d₁*m 2)*((d/d₁)*m 4) = _
    calc _ = (d₁*(d/d₁))*(m 2*m 4) := by ring
      _ = _ := by rw [h₁₂]
  have hright : outerRight (wattLift d d₁ d₃ m) = d*(m 3*m 5) := by
    change (d₃*m 3)*((d/d₃)*m 5) = _
    calc _ = (d₃*(d/d₃))*(m 3*m 5) := by ring
      _ = _ := by rw [h₃₄]
  have hdr : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have harg₂ : ((d:ℝ)*(m 3*m 5:ℕ))/((d:ℝ)*q.M₂)*x =
      ((m 3:ℝ)*x/q.M₂)*(m 5:ℝ) := by push_cast; field_simp
  have harg₄ : ((d:ℝ)*(m 2*m 4:ℕ))/((d:ℝ)*q.N₂)*x =
      ((m 2:ℝ)*x/q.N₂)*(m 4:ℝ) := by push_cast; field_simp
  have harg₁ : ((d/d₁*m 4:ℕ):ℝ)/q.M₁ = ((d/d₁:ℕ):ℝ)/q.M₁*(m 4:ℝ) := by push_cast; ring
  have harg₃ : ((d/d₃*m 5:ℕ):ℝ)/q.N₁ = ((d/d₃:ℕ):ℝ)/q.N₁*(m 5:ℝ) := by push_cast; ring
  have hphase : -(signedShift frequencyPositive (m 1):ℝ)*
      ((signedShift positive (m 0):ℝ)*(inverseRepresentative (m 2*m 4) (m 3*m 5):ℝ)/(m 3*m 5:ℕ)) =
      (if positive != frequencyPositive then (1:ℝ) else -1)*(m 0:ℝ)*m 1*
        (inverseRepresentative (m 2*m 4) (m 3*m 5):ℝ)/(m 3*m 5:ℕ) := by
    cases positive <;> cases frequencyPositive <;> norm_num [signedShift] <;> ring
  have hfreq : (signedShift frequencyPositive (m 1):ℝ)*x =
      (if frequencyPositive then x else -x)*(m 1:ℝ) := by
    cases frequencyPositive <;> simp [signedShift] <;> ring
  unfold originalWattTerm concreteWattTerm outerPoissonPhase
  rw [hg,hleft,hright,Nat.mul_div_cancel_left _ hd,Nat.mul_div_cancel_left _ hd]
  dsimp only [poissonOuterWeight,outerPoissonProfile]
  rw [hg,hleft,hright]
  simp only [Nat.cast_mul]
  change _ = _
  unfold wattShiftWeight wattFrequencyWeight actualWattCoefficient actualWattGamma
  rw [ite_eq_left hr,ite_eq_left hs,ite_eq_left hgate,positiveFrequencyProfile_nat hl]
  dsimp [wattLift]
  push_cast at hphase harg₂ harg₄
  rw [harg₁,harg₃,hfreq,hphase]
  dsimp [separatedWattProfile,poissonProfile]
  rw [harg₂,harg₄]
  ring

theorem positive_divisor_mem_scaled_range {A : ℝ} (hA : 0 ≤ A) {a e : ℕ}
    (ha : a ∈ Finset.Icc 1 ⌊2*A⌋₊) (he : 0 < e) (hea : e ∣ a) :
    a/e ∈ Finset.Icc 1 ⌊2*(A/(e:ℝ))⌋₊ := by
  have hap : 0 < a := (Finset.mem_Icc.mp ha).1
  have her : (0:ℝ) < e := by exact_mod_cast he
  refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hap hea) he,?_⟩
  apply (Nat.le_floor_iff (by positivity)).mpr
  rw [Nat.cast_div_charZero hea]
  have ha' : (a:ℝ) ≤ 2*A :=
    (show (a:ℝ) ≤ (⌊2*A⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp ha).2).trans
      (Nat.floor_le (by positivity))
  calc _ ≤ (2*A)/(e:ℝ) := div_le_div_of_nonneg_right ha' her.le
    _ = _ := by ring

theorem wattProject_mem {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hq : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive frequencyPositive : Bool) (ρ : ℝ) {d : ℕ} (hd : 0 < d) {x : ℝ}
    {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q) (hg : outerGCD n = d)
    {l : ℕ} (hl : l ∈ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊)
    (hne : originalWattTerm positive frequencyPositive q ρ α β W d x n l ≠ 0) :
    wattProject d n l ∈ wattIndexSet
      ((naturalWattScales q ρ d (splitLeft (n 0) d) (splitRight (n 0) d)
        (splitLeft (n 1) d) (splitRight (n 1) d)).doubled) := by
  have hp (i : Fin 5) := (quadraticMainIndexSet_coordinate_bounds q hq hn i).1
  have hdiv₁ : d ∣ n 0*n 2 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
  have hdiv₂ : d ∣ n 1*n 3 := by rw [← hg]; exact Nat.gcd_dvd_right _ _
  have hn0 : n 0 ∈ Finset.Icc 1 ⌊2*q.A⌋₊ := by
    simpa [quadraticMainIndexSet] using Fintype.mem_piFinset.mp hn 0
  have hn1 : n 1 ∈ Finset.Icc 1 ⌊2*q.B⌋₊ := by
    simpa [quadraticMainIndexSet] using Fintype.mem_piFinset.mp hn 1
  have hn2 : n 2 ∈ Finset.Icc 1 ⌊2*q.M₁⌋₊ := by
    simpa [quadraticMainIndexSet] using Fintype.mem_piFinset.mp hn 2
  have hn3 : n 3 ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊ := by
    simpa [quadraticMainIndexSet] using Fintype.mem_piFinset.mp hn 3
  have hwne : poissonOuterWeight q α β W n ≠ 0 := by
    intro hz; exact hne (by simp [originalWattTerm,hz])
  have hk := outer_weight_shift_bound hq hw hwne
  rw [hg] at hk
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (hq 6)
  have hk' : n 4 ∈ Finset.Icc 1 ⌊2*(q.H/(d:ℝ))⌋₊ := by
    refine Finset.mem_Icc.mpr ⟨hp 4,(Nat.le_floor_iff (by positivity)).mpr ?_⟩
    have he : 2*(q.H/(d:ℝ)) = 2*q.H/(d:ℝ) := by ring
    rw [he]
    exact (le_div_iff₀ hdr).mpr (by nlinarith)
  have hr := positive_divisor_mem_scaled_range
    (zero_le_one.trans (show 1 ≤ q.A from hq 0)) hn0 (splitLeft_pos (n 0) hd)
      (Nat.gcd_dvd_left (n 0) d)
  have hs := positive_divisor_mem_scaled_range
    (zero_le_one.trans (show 1 ≤ q.B from hq 1)) hn1 (splitLeft_pos (n 1) hd)
      (Nat.gcd_dvd_left (n 1) d)
  have hv := positive_divisor_mem_scaled_range
    (zero_le_one.trans (show 1 ≤ q.M₁ from hq 2)) hn2 (splitRight_pos (n 0) hd)
      (splitRight_dvd_inner hd hdiv₁)
  have hpp := positive_divisor_mem_scaled_range
    (zero_le_one.trans (show 1 ≤ q.N₁ from hq 4)) hn3 (splitRight_pos (n 1) hd)
      (splitRight_dvd_inner hd hdiv₂)
  apply Fintype.mem_piFinset.mpr
  intro i
  fin_cases i <;> dsimp [wattProject,WattScales.size,naturalWattScales,WattScales.doubled]
  · exact hk'
  · exact hl
  · exact hr
  · exact hs
  · exact hv
  · exact hpp

theorem originalWattTerm_nonzero_index {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hq : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive frequencyPositive : Bool) (ρ : ℝ) {d : ℕ} (hd : 0 < d) {x : ℝ}
    {n : Fin 5 → ℕ} (hpos : ∀ i, 0 < n i) (hg : outerGCD n = d) {l : ℕ}
    (hne : originalWattTerm positive frequencyPositive q ρ α β W d x n l ≠ 0) :
    n ∈ quadraticMainIndexSet q := by
  have hwne : poissonOuterWeight q α β W n ≠ 0 := by
    intro hz; exact hne (by simp [originalWattTerm,hz])
  have hα : α (n 0) ≠ 0 := by intro hz; exact hwne (by simp [poissonOuterWeight,hz])
  have hβ : β (n 1) ≠ 0 := by intro hz; exact hwne (by simp [poissonOuterWeight,hz])
  have hm : W 1 ((n 2:ℝ)/q.M₁) ≠ 0 := by intro hz; exact hwne (by simp [poissonOuterWeight,hz])
  have hn : W 3 ((n 3:ℝ)/q.N₁) ≠ 0 := by intro hz; exact hwne (by simp [poissonOuterWeight,hz])
  have ha : (n 0:ℝ) ≤ 2*q.A := by
    by_contra hh
    exact hα (hw.alpha_support _ (by intro ht; exact hh ht.2))
  have hb : (n 1:ℝ) ≤ 2*q.B := by
    by_contra hh
    exact hβ (hw.beta_support _ (by intro ht; exact hh ht.2))
  have hM : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (hq 2)
  have hN : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (hq 4)
  have hmb := (dyadic_weight_argument_bounds (hw.smooth 1) hM hm).2
  have hnb := (dyadic_weight_argument_bounds (hw.smooth 3) hN hn).2
  have hk := outer_weight_shift_bound hq hw hwne
  rw [hg] at hk
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hkb : (n 4:ℝ) ≤ 2*q.H :=
    (le_mul_of_one_le_left (Nat.cast_nonneg _) hdr).trans hk
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  refine ⟨hpos i,(Nat.le_floor_iff (by
    fin_cases i <;> dsimp <;> first | positivity | linarith [hq 0])).mpr ?_⟩
  fin_cases i <;> dsimp <;> assumption

theorem concreteWattTerm_active {positive frequencyPositive : Bool}
    {q : QuadraticScales} {ρ : ℝ} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    {d d₁ d₃ : ℕ} {x : ℝ} {m : Fin 6 → ℕ}
    (hne : concreteWattTerm positive frequencyPositive q ρ α β W d d₁ d₃ x m ≠ 0) :
    (m 2).Coprime (d/d₁) ∧ (m 3).Coprime (d/d₃) ∧
      (m 2:ℝ) ≤ 2*q.A/(d₁:ℝ) ∧ (m 3:ℝ) ≤ 2*q.B/(d₃:ℝ) := by
  have hr : (m 2).Coprime (d/d₁) := by
    by_contra hh
    exact hne (by simp [concreteWattTerm,actualWattCoefficient,hh])
  have hs : (m 3).Coprime (d/d₃) := by
    by_contra hh
    exact hne (by simp [concreteWattTerm,actualWattCoefficient,hh])
  have hg : (m 2:ℝ) ≤ 2*q.A/(d₁:ℝ) ∧ (m 3:ℝ) ≤ 2*q.B/(d₃:ℝ) := by
    by_contra hh
    exact hne (by simp [concreteWattTerm,actualWattGamma,hh])
  exact ⟨hr,hs,hg⟩

def originalWattFibre (q : QuadraticScales) (ρ : ℝ) (d e f : ℕ) :
    Finset ((Fin 5 → ℕ) × ℕ) :=
  (quadraticMainIndexSet q ×ˢ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊).filter
    (fun p => outerGCD p.1 = d ∧ splitLeft (p.1 0) d = e ∧ splitLeft (p.1 1) d = f)

theorem wattProject_gate {q : QuadraticScales} (hq : ∀ j, 1 ≤ q.size j)
    {d : ℕ} (hd : 0 < d) {n : Fin 5 → ℕ} (hn : n ∈ quadraticMainIndexSet q) (l : ℕ) :
    ((wattProject d n l) 2:ℝ) ≤ 2*q.A/(splitLeft (n 0) d:ℝ) ∧
      ((wattProject d n l) 3:ℝ) ≤ 2*q.B/(splitLeft (n 1) d:ℝ) := by
  have h₁ : (0:ℝ) < splitLeft (n 0) d := by exact_mod_cast splitLeft_pos (n 0) hd
  have h₃ : (0:ℝ) < splitLeft (n 1) d := by exact_mod_cast splitLeft_pos (n 1) hd
  have he : (splitLeft (n 0) d:ℝ)*splitCoefficient (n 0) d = (n 0:ℝ) := by
    exact_mod_cast split_coefficient_mul (n 0) d
  have hf : (splitLeft (n 1) d:ℝ)*splitCoefficient (n 1) d = (n 1:ℝ) := by
    exact_mod_cast split_coefficient_mul (n 1) d
  constructor
  · apply (le_div_iff₀ h₁).mpr
    have ha : (n 0:ℝ) ≤ 2*q.A := by simpa using (quadraticMainIndexSet_coordinate_bounds q hq hn 0).2
    change (splitCoefficient (n 0) d:ℝ)*splitLeft (n 0) d ≤ _
    nlinarith
  · apply (le_div_iff₀ h₃).mpr
    have hb : (n 1:ℝ) ≤ 2*q.B := by simpa using (quadraticMainIndexSet_coordinate_bounds q hq hn 1).2
    change (splitCoefficient (n 1) d:ℝ)*splitLeft (n 1) d ≤ _
    nlinarith

theorem wattProject_coprime {n : Fin 5 → ℕ} {d : ℕ} (hg : outerGCD n = d)
    (hb : 0 < n 1*n 3) (l : ℕ) :
    ((wattProject d n l) 2*(wattProject d n l) 4).Coprime
      ((wattProject d n l) 3*(wattProject d n l) 5) := by
  have hc := split_residual_coprime (a := n 0) (m := n 2) (b := n 1) (n := n 3) hb
  dsimp only at hc
  rw [show Nat.gcd (n 0*n 2) (n 1*n 3) = d from hg] at hc
  exact hc

theorem originalWattFibre_sum_eq {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hq : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    (positive frequencyPositive : Bool) (ρ : ℝ) {d e f : ℕ} (hd : 0 < d)
    (he : e ∈ d.divisors) (hf : f ∈ d.divisors) (x : ℝ) :
    (∑ p ∈ originalWattFibre q ρ d e f,
      originalWattTerm positive frequencyPositive q ρ α β W d x p.1 p.2) =
      weightedWattSum (positive != frequencyPositive)
        ((naturalWattScales q ρ d e (d/e:ℕ) f (d/f:ℕ)).doubled)
        (actualWattCoefficient α e (d/e)) (actualWattCoefficient β f (d/f))
        (wattShiftWeight q W d) (wattFrequencyWeight q ρ d x frequencyPositive)
        (actualWattGamma q W e (d/e) f (d/f) x) := by
  have hediv := (Nat.mem_divisors.mp he).1
  have hfdiv := (Nat.mem_divisors.mp hf).1
  have hep := Nat.pos_of_mem_divisors he
  have hfp := Nat.pos_of_mem_divisors hf
  have he₂p := Nat.div_pos (Nat.le_of_dvd hd hediv) hep
  have hf₄p := Nat.div_pos (Nat.le_of_dvd hd hfdiv) hfp
  let p := (naturalWattScales q ρ d e (d/e:ℕ) f (d/f:ℕ)).doubled
  change _ = ∑ m ∈ (wattIndexSet p).filter (fun m => (m 2*m 4).Coprime (m 3*m 5)),
    concreteWattTerm positive frequencyPositive q ρ α β W d e f x m
  apply Finset.sum_bij_ne_zero (fun a _ _ => wattProject d a.1 a.2)
  · intro a ha hne
    obtain ⟨hpair,hg,hae,haf⟩ := mem_filter.mp ha
    obtain ⟨hn,hl⟩ := mem_product.mp hpair
    have hm := wattProject_mem hq hw positive frequencyPositive ρ hd hn hg hl hne
    have hm' : wattProject d a.1 a.2 ∈ wattIndexSet p := by
      simpa only [p,splitRight,hae,haf] using hm
    refine mem_filter.mpr ⟨hm',?_⟩
    have hpos (i : Fin 5) := (quadraticMainIndexSet_coordinate_bounds q hq hn i).1
    exact wattProject_coprime hg (Nat.mul_pos (hpos 1) (hpos 3)) a.2
  · intro a ha _ b hb _ heq
    obtain ⟨_,hga,hae,haf⟩ := mem_filter.mp ha
    obtain ⟨_,hgb,hbe,hbf⟩ := mem_filter.mp hb
    apply Prod.ext
    · have hla := wattLift_project hd a.1 a.2 hga
      have hlb := wattLift_project hd b.1 b.2 hgb
      rw [hae,haf] at hla
      rw [hbe,hbf] at hlb
      exact hla.symm.trans ((congrArg (wattLift d e f) heq).trans hlb)
    · have hl := congrFun heq 1
      simpa [wattProject] using hl
  · intro m hm hne
    obtain ⟨hm,hcop⟩ := mem_filter.mp hm
    have hpos (i : Fin 6) : 0 < m i := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)).1
    obtain ⟨hr,hs,hgate⟩ := concreteWattTerm_active hne
    let n := wattLift d e f m
    have hg : outerGCD n = d := wattLift_gcd hediv hfdiv m hcop
    have hi := originalWattTerm_lift positive frequencyPositive q ρ α β W hd hediv hfdiv
      x m (hpos 1) hr hs hcop hgate
    have hne' : originalWattTerm positive frequencyPositive q ρ α β W d x n (m 1) ≠ 0 := by
      rw [hi]
      exact hne
    have hnp : ∀ i, 0 < n i := by
      have h0 := hpos 0; have h2 := hpos 2; have h3 := hpos 3
      have h4 := hpos 4; have h5 := hpos 5
      intro i; fin_cases i <;> dsimp [n,wattLift] <;> positivity
    have hn := originalWattTerm_nonzero_index hq hw positive frequencyPositive ρ hd hnp hg hne'
    have hl : m 1 ∈ Finset.Icc 1 ⌊2*poissonLength q ρ d⌋₊ := by
      simpa [p,naturalWattScales,WattScales.doubled,WattScales.size] using Fintype.mem_piFinset.mp hm 1
    obtain ⟨hleft,hright,hproj⟩ := wattProject_lift hd hediv hfdiv m hr hs
    refine ⟨(n,m 1),mem_filter.mpr ⟨mem_product.mpr ⟨hn,hl⟩,hg,hleft,hright⟩,hne',hproj⟩
  · intro a ha _
    obtain ⟨hpair,hg,hae,haf⟩ := mem_filter.mp ha
    obtain ⟨hn,hl⟩ := mem_product.mp hpair
    have hpos (i : Fin 5) := (quadraticMainIndexSet_coordinate_bounds q hq hn i).1
    have hcop := wattProject_coprime hg (Nat.mul_pos (hpos 1) (hpos 3)) a.2
    have hgate := wattProject_gate hq hd hn a.2
    rw [hae,haf] at hgate
    have hr : ((wattProject d a.1 a.2) 2).Coprime (d/e) := by
      simpa [wattProject,← hae,splitRight] using split_coprime (a.1 0) hd
    have hs : ((wattProject d a.1 a.2) 3).Coprime (d/f) := by
      simpa [wattProject,← haf,splitRight] using split_coprime (a.1 1) hd
    have hi := originalWattTerm_lift positive frequencyPositive q ρ α β W hd hediv hfdiv
      x (wattProject d a.1 a.2) (Finset.mem_Icc.mp hl).1 hr hs hcop hgate
    have hlift := wattLift_project hd a.1 a.2 hg
    rw [hae,haf] at hlift
    have hlproj : (wattProject d a.1 a.2) 1 = a.2 := by simp [wattProject]
    rw [hlift,hlproj] at hi
    exact hi

end
end DivisorProof




namespace DivisorProof
open Real Set Finset Classical
noncomputable section

theorem NormalizedWeightData.admissible {ρ δ K : ℝ} {bounds : ℕ → ℝ}
    {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hw : NormalizedWeightData bounds q α β W) (h : ScaleGeometry ρ K q)
    (hρ : 0 ≤ ρ) (hK : 1 ≤ K) (hsize : (q.A*q.B)^δ ≤ K*q.M*q.N) :
    QuadraticAdmissible ρ δ K bounds q α β W := by
  have hA : 1 ≤ q.A^ρ := Real.one_le_rpow (h.scales 0) hρ
  have hB : 1 ≤ q.B^ρ := Real.one_le_rpow (h.scales 1) hρ
  have hQ : 1 ≤ q.mass^ρ := Real.one_le_rpow (poisson_scale_bounds q h.scales).1 hρ
  refine ⟨h.scales,h.orderM,h.orderN,h.shift,hsize,h.balanceM,h.balanceN,h.orientation,
    hw.alpha_support,hw.beta_support,?_,?_,hw.smooth,?_⟩
  · intro n
    exact (hw.alpha_bound n).trans (one_le_mul_of_one_le_of_one_le hK hA)
  · intro n
    exact (hw.beta_bound n).trans (one_le_mul_of_one_le_of_one_le hK hB)
  · intro j i x
    exact (hw.derivatives j i x).trans
      (le_mul_of_one_le_right (hw.bounds_nonneg j) hQ)

end
end DivisorProof

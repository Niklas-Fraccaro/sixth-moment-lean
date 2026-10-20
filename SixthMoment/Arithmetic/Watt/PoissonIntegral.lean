import SixthMoment.Arithmetic.Watt.CurveWeights
import SixthMoment.Arithmetic.Watt.Poisson


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem classicalKloostermanSum_neg_neg {c : ℕ} (hc : 0 < c) (m n : ℤ) :
    classicalKloostermanSum (-m) (-n) c = classicalKloostermanSum m n c := by
  have : NeZero c := ⟨hc.ne'⟩
  unfold classicalKloostermanSum
  rw [kloostermanSum_eq_salt hc,kloostermanSum_eq_salt hc]
  simpa using Salt.Weil.kloosterman_reindex_units (n : ZMod c) (m : ZMod c) (-(1 : (ZMod c)ˣ))

theorem classicalKloostermanSum_phaseSign {c : ℕ} (hc : 0 < c)
    (positive : Bool) (m l : ℤ) :
    classicalKloostermanSum (phaseSign positive*m) (-l) c =
      classicalKloostermanSum m (-phaseSign positive*l) c := by
  cases positive with
  | false => simpa only [phaseSign,Bool.false_eq_true,ite_false,neg_one_mul,neg_neg,one_mul]
      using classicalKloostermanSum_neg_neg hc m l
  | true => simp only [phaseSign,ite_true,one_mul,neg_one_mul]

def completedIntegrand (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool)
    (h k r s t : ℕ) (l : ℤ) (y : ℝ) : ℂ :=
  curveWeight γ y r s t*ePhase ((l : ℝ)*y)*
    classicalKloostermanSum
      (phaseSign positive*(h : ℤ)*k*inverseRepresentative r (s*t)) (-l) (s*t)

theorem completedTerm_eq_integral (p : WattScales) (γ : ℕ → ℕ → ℝ → ℝ → ℂ)
    (positive : Bool) (h k r s t : ℕ) (l : ℤ) :
    completedTerm p γ positive h k r s t l =
      ∫ y : ℝ, completedIntegrand γ positive h k r s t l y := by
  unfold completedTerm fourierCoefficient completedIntegrand
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  have he : γ r s (((s*t : ℕ) : ℝ)*y) t = curveWeight γ y r s t := by
    unfold curveWeight
    push_cast
    congr 1
    ring
  rw [he]

theorem completedIntegrand_continuous {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) (h k r s t : ℕ) (l : ℤ) :
    Continuous (completedIntegrand γ positive h k r s t l) := by
  have hγ : Continuous (fun y => curveWeight γ y r s t) :=
    (hw.gamma_smooth r s).continuous.comp
      (((continuous_const.mul continuous_id).mul continuous_const).prodMk continuous_const)
  exact (hγ.mul (continuous_ePhase.comp (continuous_const.mul continuous_id))).mul continuous_const

theorem completedIntegrand_support {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (positive : Bool) (h k r : ℕ) {s : ℕ} (hs : s ∈ dyadicRange p.S) (t : ℕ) (l : ℤ) :
    tsupport (completedIntegrand γ positive h k r s t l) ⊆
      Icc (p.V/(2*p.S*p.P)) (4*p.V/(p.S*p.P)) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  apply gamma_curve_y_support hw hV hP hS r hs t
  apply subset_tsupport
  intro hz
  exact hy (by simp only [completedIntegrand,hz,zero_mul])

theorem completedIntegrand_integrable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (positive : Bool) (h k r : ℕ) {s : ℕ} (hs : s ∈ dyadicRange p.S) (t : ℕ) (l : ℤ) :
    Integrable (completedIntegrand γ positive h k r s t l) :=
  (completedIntegrand_continuous hw positive h k r s t l).integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (completedIntegrand_support hw hV hP hS positive h k r hs t l))

def pairFrequencyIntegrand (p : WattScales) (u₀ u₁ : ℝ → ℂ)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool) (r s : ℕ) (l : ℤ) (y : ℝ) : ℂ :=
  ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, u₀ h*u₁ k*
    ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
      completedIntegrand γ positive h k r s t l y

theorem pairFrequencyIntegrand_integrable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (positive : Bool) (r : ℕ) {s : ℕ} (hs : s ∈ dyadicRange p.S) (l : ℤ) :
    Integrable (pairFrequencyIntegrand p u₀ u₁ γ positive r s l) := by
  apply integrable_finsetSum
  intro h _
  apply integrable_finsetSum
  intro k _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  exact completedIntegrand_integrable hw hV hP hS positive h k r hs t l

theorem pairFrequencySum_eq_integral {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (positive : Bool) (r : ℕ) {s : ℕ} (hs : s ∈ dyadicRange p.S) (l : ℤ) :
    pairFrequencySum p u₀ u₁ γ positive r s l =
      ∫ y : ℝ, pairFrequencyIntegrand p u₀ u₁ γ positive r s l y := by
  have hi (h k t : ℕ) := completedIntegrand_integrable hw hV hP hS positive h k r hs t l
  have ht (h k : ℕ) := integrable_finsetSum ((positiveRange p.P).filter (fun t => t.Coprime r))
    (fun t _ => hi h k t)
  unfold pairFrequencySum pairFrequencyIntegrand
  rw [integral_finsetSum _ (fun h _ =>
    integrable_finsetSum _ (fun k _ => (ht h k).const_mul _))]
  apply sum_congr rfl
  intro h _
  rw [integral_finsetSum _ (fun k _ => (ht h k).const_mul _)]
  apply sum_congr rfl
  intro k _
  rw [integral_const_mul,integral_finsetSum _ (fun t _ => hi h k t)]
  simp only [completedTerm_eq_integral]

end
end Watt41
end DivisorProof

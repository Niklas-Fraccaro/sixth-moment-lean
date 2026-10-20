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
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.BlockSums
import Std

namespace DivisorProof
open Real Classical
noncomputable section
set_option maxHeartbeats 1800000

def WattScales.doubled (p : WattScales) : WattScales :=
  ⟨2*p.H,2*p.C,2*p.R,2*p.S,2*p.V,2*p.P⟩

theorem WattScales.doubled_product (p : WattScales) :
    p.doubled.product = 16*p.product := by
  dsimp [WattScales.doubled,WattScales.product]
  ring

theorem WattScales.doubled_X (p : WattScales) : p.doubled.X = 2*p.X := by
  have hratio : p.doubled.product/(p.doubled.H*p.doubled.C) =
      4*(p.product/(p.H*p.C)) := by
    rw [p.doubled_product]
    dsimp [WattScales.doubled]
    ring
  unfold WattScales.X
  rw [hratio,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num

theorem WattScales.doubled_sizes {p : WattScales} {ρ F : ℝ}
    (hp : 0 ≤ p.product) (_hH : 0 ≤ p.H) (hC : 0 ≤ p.C)
    (hS : 0 ≤ p.S) (hP : 0 ≤ p.P) (hV : 0 ≤ p.V)
    (hF : 1 ≤ F)
    (hfirst : (16^ρ*(F+1))*p.product^ρ ≤ p.X)
    (hsecond : (16^ρ*(F+1))*(p.H^2*p.C) ≤ (p.R*p.S)^2)
    (hthird : (16^ρ*(F+1))*(p.S*p.P/p.V)*p.product^ρ ≤ (p.R*p.S)^2)
    (hρ : 0 ≤ ρ) :
    F*p.doubled.product^ρ ≤ p.doubled.X ∧
      p.doubled.H^2*p.doubled.C ≤ (p.doubled.R*p.doubled.S)^2 ∧
      (p.doubled.S*p.doubled.P/p.doubled.V)*p.doubled.product^ρ ≤
        (p.doubled.R*p.doubled.S)^2 := by
  have h16 : 1 ≤ (16:ℝ)^ρ := Real.one_le_rpow (by norm_num) hρ
  have hres : 1 ≤ (16:ℝ)^ρ*(F+1) := by nlinarith
  have hsecond' : p.H^2*p.C ≤ (p.R*p.S)^2 :=
    (le_mul_of_one_le_left (by positivity) hres).trans hsecond
  have hthird' : (16:ℝ)^ρ*((p.S*p.P/p.V)*p.product^ρ) ≤ (p.R*p.S)^2 := by
    apply le_trans _ hthird
    have hz : 0 ≤ (p.S*p.P/p.V)*p.product^ρ := by positivity
    calc (16:ℝ)^ρ*((p.S*p.P/p.V)*p.product^ρ) ≤
        ((16:ℝ)^ρ*((p.S*p.P/p.V)*p.product^ρ))*(F+1) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
      _ = _ := by ring
  rw [p.doubled_product,p.doubled_X,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hp]
  refine ⟨?_,?_,?_⟩
  · have hnonneg : 0 ≤ p.X := Real.sqrt_nonneg _
    have h0 : 0 ≤ p.product^ρ := Real.rpow_nonneg hp _
    nlinarith
  · dsimp [WattScales.doubled]
    nlinarith [sq_nonneg (p.R*p.S)]
  · have hid : (2*p.S)*(2*p.P)/(2*p.V) = 2*(p.S*p.P/p.V) := by ring
    dsimp only [WattScales.doubled]
    rw [hid]
    nlinarith [sq_nonneg (p.R*p.S)]

theorem weightedWatt_at_doubled_natural_scales (hWatt : WeightedWattBound)
    {ρ δ K : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hbound : ρ ≤ δ/(1000*(1+δ))) (hK : 1 ≤ K)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧
      ∀ (bounds : ℕ → ℝ) (q : QuadraticScales) (α β : ℕ → ℂ)
        (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W → Q₀ ≤ q.mass →
      ∀ d d₁ d₂ d₃ d₄ : ℝ, 1 ≤ d → 1 ≤ d₁ → 1 ≤ d₂ → 1 ≤ d₃ → 1 ≤ d₄ →
        d₁*d₂ = d → d₃*d₄ = d → d₃ ≤ 2*q.B → d ≤ gcdCutoff q ρ →
      let p := (naturalWattScales q ρ d d₁ d₂ d₃ d₄).doubled
      ∀ (Δ : ℝ) (a bcoeff : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
        (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        (∀ i, 1 ≤ p.size i) → 0 < Δ → Δ ≤ 1 →
        WattWeightData b g p Δ a bcoeff u₀ u₁ γ → ∀ positive : Bool,
          ‖weightedWattSum positive p a bcoeff u₀ u₁ γ‖ ≤ C*wattMajorant p Δ ρ := by
  obtain ⟨C,F,hC,hF,hinput⟩ := hWatt ρ hρ b hb g hg
  have hres : 0 ≤ (16:ℝ)^ρ*(F+1) := by positivity
  obtain ⟨Q₀,hQ₀,hsize⟩ := naturalWatt_all_sizes_eventually hρ hδ hbound hK hres
  refine ⟨Q₀,C,hQ₀,hC,?_⟩
  intro bounds q α β W hadm hmass d d₁ d₂ d₃ d₄ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄ hd₃B hcut
  dsimp only
  intro Δ a bcoeff u₀ u₁ γ hscales hΔ hΔ₁ hweights positive
  let p := naturalWattScales q ρ d d₁ d₂ d₃ d₄
  obtain ⟨hfirst,hsecond,hthird⟩ := hsize bounds q α β W hadm hmass
    d d₁ d₂ d₃ d₄ hd h₁ h₂ h₃ h₄ h₁₂ h₃₄ hd₃B hcut
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (hadm.1 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (hadm.1 1)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (hadm.1 2)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (hadm.1 4)
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (hadm.1 6)
  have hp : 0 ≤ p.product := by dsimp [p,naturalWattScales,WattScales.product]; positivity
  have hpH : 0 ≤ p.H := by dsimp [p,naturalWattScales]; positivity
  have hpC : 0 ≤ p.C := (poissonLength_pos q hadm.1 ρ (by linarith : 0 < d)).le
  have hpS : 0 ≤ p.S := by dsimp [p,naturalWattScales]; positivity
  have hpP : 0 ≤ p.P := by dsimp [p,naturalWattScales]; positivity
  have hpV : 0 ≤ p.V := by dsimp [p,naturalWattScales]; positivity
  obtain ⟨h₁',h₂',h₃'⟩ := WattScales.doubled_sizes hp hpH hpC hpS hpP hpV hF
    hfirst hsecond hthird hρ.le
  exact hinput p.doubled Δ a bcoeff u₀ u₁ γ hscales hΔ hΔ₁ hweights h₁' h₂' h₃' positive

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem poissonProfile_tsupport_dyadic {W₂ W₄ : ℝ → ℝ} {a b : ℝ}
    (h₂ : SmoothDyadicWeight W₂) (ha : 0 < a) :
    tsupport (poissonProfile W₂ W₄ a b) ⊆ Icc (1/a) (2/a) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hW : W₂ (a*x) ≠ 0 := by
    intro hz
    exact hx (by simp [poissonProfile,hz])
  have hs := h₂.2 (subset_tsupport _ hW)
  exact ⟨(div_le_iff₀ ha).mpr (by nlinarith [hs.1]),
    (le_div_iff₀ ha).mpr (by nlinarith [hs.2])⟩

theorem poissonProfile_scaled_derivative_bound {W₂ W₄ : ℝ → ℝ}
    {a b V K : ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hV : 0 < V) (ha : a*V = 1) (hb : 0 ≤ b*V) (hK : 1 ≤ K) (hbK : b*V ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (poissonProfile W₂ W₄ a b) x‖ ≤
      V^(-(j:ℝ))*profileDerivativeBound bounds K j := by
  have hvn : V ≠ 0 := hV.ne'
  have heq : poissonProfile W₂ W₄ a b = fun x : ℝ =>
      poissonProfile W₂ W₄ (a*V) (b*V) (V⁻¹*x) := by
    funext x
    unfold poissonProfile
    congr 2 <;> field_simp
  rw [heq,iteratedDeriv_comp_const_smul
    ((poissonProfile_contDiff (a*V) (b*V) h₂ h₄).of_le (by exact_mod_cast le_top))]
  dsimp only
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hV).le _),
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    poissonProfile_norm_iteratedFDeriv (a*V) (b*V) h₂ h₄]
  have hbound := realPoissonProfile_derivative_bound h₂ h₄
    (by rw [ha]; norm_num : 0 ≤ a*V) hb (ha ▸ hK) hbK hder₂ hder₄ j (V⁻¹*x)
  have hpow : (V⁻¹)^j = V^(-(j:ℝ)) := by
    rw [Real.rpow_neg hV.le,Real.rpow_natCast,inv_pow]
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hV.le _)

theorem poissonProfile_multiplicative_derivative_bound {W₂ W₄ : ℝ → ℝ}
    {a b V K : ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (hV : 0 < V) (ha : a*V = 1) (hb : 0 ≤ b*V) (hK : 1 ≤ K) (hbK : b*V ≤ K)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv j (poissonProfile W₂ W₄ a b) x‖ ≤
      (2^j*profileDerivativeBound bounds K j)*x^(-(j:ℝ)) := by
  have hC : 0 ≤ profileDerivativeBound bounds K j :=
    profileDerivativeBound_nonneg (fun i => (norm_nonneg _).trans (hder₂ i 0)) (by linarith) j
  by_cases hz : iteratedDeriv j (poissonProfile W₂ W₄ a b) x = 0
  · rw [hz,norm_zero]
    positivity
  have hap : 0 < a := by nlinarith
  have hfne : iteratedFDeriv ℝ j (poissonProfile W₂ W₄ a b) x ≠ 0 := by
    intro heq
    have hn := norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ)
      (n := j) (f := poissonProfile W₂ W₄ a b) (x := x)
    rw [heq,norm_zero] at hn
    exact hz (norm_eq_zero.mp hn.symm)
  have hxs := poissonProfile_tsupport_dyadic h₂ hap (support_iteratedFDeriv_subset j hfne)
  have hxe : x ≤ 2*V := by
    have ha' : a = V⁻¹ := by
      rw [← one_div]
      exact (eq_div_iff hV.ne').mpr ha
    simpa [ha',hV.ne'] using hxs.2
  have hpow : V^(-(j:ℝ)) ≤ 2^j*x^(-(j:ℝ)) := by
    rw [Real.rpow_neg hV.le,Real.rpow_neg hx.le,Real.rpow_natCast,Real.rpow_natCast]
    rw [← one_div (V^j),← div_eq_mul_inv]
    apply (div_le_div_iff₀ (pow_pos hV j) (pow_pos hx j)).mpr
    simpa only [one_mul,mul_pow] using pow_le_pow_left₀ hx.le hxe j
  exact (poissonProfile_scaled_derivative_bound h₂ h₄ hV ha hb hK hbK hder₂ hder₄ j x).trans
    (by calc _ ≤ (2^j*x^(-(j:ℝ)))*profileDerivativeBound bounds K j :=
        mul_le_mul_of_nonneg_right hpow hC
      _ = _ := by ring)

def separatedWattProfile (W : Fin 5 → ℝ → ℝ) (a b c d : ℝ) (v p : ℝ) : ℂ :=
  poissonProfile (W 1) (W 4) a b v*poissonProfile (W 3) (W 2) c d p

theorem separatedWattProfile_contDiff {W : Fin 5 → ℝ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i)) (a b c d : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => separatedWattProfile W a b c d z.1 z.2) :=
  ((poissonProfile_contDiff a b (hW 1) (hW 4)).comp contDiff_fst).mul
    ((poissonProfile_contDiff c d (hW 3) (hW 2)).comp contDiff_snd)

theorem separatedWattProfile_mixed_derivative (W : Fin 5 → ℝ → ℝ)
    (a b c d : ℝ) (i j : ℕ) (x y : ℝ) :
    iteratedDeriv j (fun y => iteratedDeriv i
      (fun x => separatedWattProfile W a b c d x y) x) y =
      iteratedDeriv i (poissonProfile (W 1) (W 4) a b) x*
        iteratedDeriv j (poissonProfile (W 3) (W 2) c d) y := by
  simp only [separatedWattProfile,iteratedDeriv_mul_const_field,iteratedDeriv_const_mul_field]

theorem separatedWattProfile_mixed_bound {W : Fin 5 → ℝ → ℝ}
    {a b c d V P K : ℝ} {bounds : ℕ → ℝ}
    (hW : ∀ i, SmoothDyadicWeight (W i))
    (hder : ∀ j i x, ‖iteratedDeriv j (W i) x‖ ≤ bounds j)
    (hV : 0 < V) (hP : 0 < P) (ha : a*V = 1) (hc : c*P = 1)
    (hb : 0 ≤ b*V) (hd : 0 ≤ d*P) (hK : 1 ≤ K) (hbK : b*V ≤ K) (hdK : d*P ≤ K)
    (i j : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖iteratedDeriv j (fun y => iteratedDeriv i
      (fun x => separatedWattProfile W a b c d x y) x) y‖ ≤
      ((2^i*profileDerivativeBound bounds K i)*(2^j*profileDerivativeBound bounds K j))*
        x^(-(i:ℝ))*y^(-(j:ℝ)) := by
  rw [separatedWattProfile_mixed_derivative,norm_mul]
  have h₁ := poissonProfile_multiplicative_derivative_bound (hW 1) (hW 4)
    hV ha hb hK hbK (fun n z => hder n 1 z) (fun n z => hder n 4 z) i hx
  have h₂ := poissonProfile_multiplicative_derivative_bound (hW 3) (hW 2)
    hP hc hd hK hdK (fun n z => hder n 3 z) (fun n z => hder n 2 z) j hy
  calc _ ≤ ((2^i*profileDerivativeBound bounds K i)*x^(-(i:ℝ)))*
      ((2^j*profileDerivativeBound bounds K j)*y^(-(j:ℝ))) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
    _ = _ := by ring

theorem naturalWatt_profile_slopes {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K)
    {d d₁ d₂ d₃ d₄ r s x : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrb : r ≤ 2*q.A/d₁) (hsb : s ≤ 2*q.B/d₃)
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)) :
    0 ≤ (r*x/q.N₂)*(q.M₁/d₂) ∧ (r*x/q.N₂)*(q.M₁/d₂) ≤ 4*K ∧
    0 ≤ (s*x/q.M₂)*(q.N₁/d₄) ∧ (s*x/q.M₂)*(q.N₁/d₄) ≤ 4*K := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hd : 0 < d := h₁₂ ▸ mul_pos h₁ h₂
  have hrad := poissonRadius_pos q h.scales hd
  have hxp : 0 ≤ x := by linarith [hx.1]
  have hN : 0 < q.N := by dsimp [QuadraticScales.N]; positivity
  have hratio : (q.A*q.M)/(q.B*q.N) ≤ K :=
    (div_le_iff₀ (mul_pos hB hN)).mpr (by nlinarith [h.balanceM])
  have hid₁ : (((2*q.A/d₁)*(2*poissonRadius q d))/q.N₂)*(q.M₁/d₂) =
      4*((q.A*q.M)/(q.B*q.N)) := by
    unfold poissonRadius QuadraticScales.M QuadraticScales.N
    rw [← h₁₂]
    field_simp
    ring
  have hid₂ : (((2*q.B/d₃)*(2*poissonRadius q d))/q.M₂)*(q.N₁/d₄) = 4 := by
    unfold poissonRadius
    rw [← h₃₄]
    field_simp
    ring
  refine ⟨by positivity,?_,by positivity,?_⟩
  · calc _ ≤ (((2*q.A/d₁)*(2*poissonRadius q d))/q.N₂)*(q.M₁/d₂) := by gcongr; exact hx.2
      _ = 4*((q.A*q.M)/(q.B*q.N)) := hid₁
      _ ≤ 4*K := by linarith
  · calc _ ≤ (((2*q.B/d₃)*(2*poissonRadius q d))/q.M₂)*(q.N₁/d₄) := by gcongr; exact hx.2
      _ = 4 := hid₂
      _ ≤ 4*K := by linarith

theorem naturalWatt_gamma_mixed_bound {ρ K : ℝ} {q : QuadraticScales}
    {bounds : ℕ → ℝ} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K)
    (hw : NormalizedWeightData bounds q α β W)
    {d d₁ d₂ d₃ d₄ r s x : ℝ}
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h₃ : 0 < d₃) (h₄ : 0 < d₄)
    (h₁₂ : d₁*d₂ = d) (h₃₄ : d₃*d₄ = d)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrb : r ≤ 2*q.A/d₁) (hsb : s ≤ 2*q.B/d₃)
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d))
    (i j : ℕ) {v p : ℝ} (hv : 0 < v) (hp : 0 < p) :
    ‖iteratedDeriv j (fun p => iteratedDeriv i (fun v =>
      separatedWattProfile W (d₂/q.M₁) (r*x/q.N₂) (d₄/q.N₁) (s*x/q.M₂) v p) v) p‖ ≤
      ((2^i*profileDerivativeBound bounds (4*K) i)*(2^j*profileDerivativeBound bounds (4*K) j))*
        v^(-(i:ℝ))*p^(-(j:ℝ)) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  obtain ⟨hb,hbK,hd,hdK⟩ := naturalWatt_profile_slopes h hK h₁ h₂ h₃ h₄
    h₁₂ h₃₄ hr hs hrb hsb hx
  apply separatedWattProfile_mixed_bound hw.smooth hw.derivatives
    (div_pos hM₁ h₂) (div_pos hN₁ h₄) _ _ hb hd (by linarith : 1 ≤ 4*K) hbK hdK i j hv hp
  · field_simp
  · field_simp

end
end DivisorProof

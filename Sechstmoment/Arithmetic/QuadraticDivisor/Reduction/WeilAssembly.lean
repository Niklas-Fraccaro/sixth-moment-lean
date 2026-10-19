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
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WeilReindexing
import Std

/-! ## Weil Assembly -/


namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000

theorem gcdWeilInnerSum_zero_of_not_dvd {W₁ W₄ : ℝ → ℝ}
    {a w d : ℕ} (hdw : ¬ d ∣ w) (M N x : ℝ) (k : ℤ) :
    gcdWeilInnerSum W₁ W₄ a w d M N x k = 0 := by
  apply sum_eq_zero
  intro m hm
  have he := (mem_filter.mp hm).2
  exact (hdw (he ▸ Nat.gcd_dvd_right (a*m) w)).elim

theorem weilOuterCoefficient_norm {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hw : NormalizedWeightData bounds q α β W) (a b n k d : ℕ) (x : ℝ) :
    ‖weilOuterCoefficient q α β W a b n k d x‖ ≤ (bounds 0)^3 := by
  unfold weilOuterCoefficient
  simp only [norm_mul,Complex.norm_real]
  have hC := hw.bounds_nonneg 0
  have hα := hw.alpha_bound a
  have hβ := hw.beta_bound b
  have h0 := hw.weight_norm 0 ((d:ℝ)*k/q.H)
  have h3 := hw.weight_norm 3 ((n:ℝ)/q.N₁)
  have h2 := hw.weight_norm 2 (((b*n:ℕ):ℝ)*x/((d:ℝ)*q.M₂))
  calc _ ≤ 1*1*bounds 0*bounds 0*bounds 0 := by
        gcongr
    _ = _ := by ring

theorem weilOuterCoefficient_active {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hw : NormalizedWeightData bounds q α β W)
    {a b n k d : ℕ} (hd : 0 < d) {x : ℝ}
    (hne : weilOuterCoefficient q α β W a b n k d x ≠ 0) :
    q.B*q.N₁ ≤ (b*n:ℕ) ∧ k ≤ ⌊2*q.H/(d:ℝ)⌋₊ := by
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hN : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (h 6)
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hb : β b ≠ 0 := by intro hz; exact hne (by simp [weilOuterCoefficient,hz])
  have hn : W 3 ((n:ℝ)/q.N₁) ≠ 0 := by
    intro hz; exact hne (by simp [weilOuterCoefficient,hz])
  have hk : W 0 ((d:ℝ)*k/q.H) ≠ 0 := by
    intro hz; exact hne (by simp [weilOuterCoefficient,hz])
  have hb' : (b:ℝ) ∈ Icc q.B (2*q.B) := by
    by_contra hh; exact hb (hw.beta_support b hh)
  have hn' := (dyadic_weight_argument_bounds (hw.smooth 3) hN hn).1
  have hk' := (dyadic_weight_argument_bounds (hw.smooth 0) hH hk).2
  refine ⟨?_,(Nat.le_floor_iff (by positivity)).mpr ?_⟩
  · simpa only [Nat.cast_mul] using mul_le_mul hb'.1 hn' hN.le (by positivity : (0:ℝ) ≤ b)
  · apply (le_div_iff₀ hdr).mpr
    nlinarith

theorem pair_product_sum_bound {B N : ℝ} (_hB : 0 < B) (_hN : 0 < N)
    (s : Finset ℕ) (F : ℕ → ℝ) (hF : ∀ w, 0 ≤ F w) :
    (∑ b ∈ Finset.Icc 1 ⌊2*B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*N⌋₊,
      if b*n ∈ s then F (b*n) else 0) ≤
      ∑ w ∈ s, (w.divisors.card:ℝ)*F w := by
  let t := (Finset.Icc 1 ⌊2*B⌋₊ ×ˢ Finset.Icc 1 ⌊2*N⌋₊).filter
    (fun p : ℕ × ℕ => p.1*p.2 ∈ s)
  have hmap : ∀ p ∈ t, p.1*p.2 ∈ s := fun p hp => (mem_filter.mp hp).2
  have heq : (∑ b ∈ Finset.Icc 1 ⌊2*B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*N⌋₊,
      if b*n ∈ s then F (b*n) else 0) = ∑ p ∈ t, F (p.1*p.2) := by
    rw [← Finset.sum_product']
    exact (Finset.sum_filter _ _).symm
  rw [heq,← Finset.sum_fiberwise_of_maps_to' hmap F]
  apply sum_le_sum
  intro w hw
  by_cases hwp : 0 < w
  · rw [Finset.sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hF w)
    have hsub : {p ∈ t | p.1*p.2 = w} ⊆
        ((Finset.Icc 1 ⌊2*B⌋₊ ×ˢ Finset.Icc 1 ⌊2*N⌋₊).filter
          (fun p : ℕ × ℕ => p.1*p.2 = w)) := by
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
    exact_mod_cast (Finset.card_le_card hsub).trans (positive_pair_product_fiber_card_le B N hwp)
  · have hz : {p ∈ t | p.1*p.2 = w} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpt := (mem_filter.mp (mem_filter.mp hp).1).1
      have hprod : 0 < p.1*p.2 := Nat.mul_pos
        (Finset.mem_Icc.mp (mem_product.mp hpt).1).1
        (Finset.mem_Icc.mp (mem_product.mp hpt).2).1
      rw [(mem_filter.mp hp).2] at hprod
      exact hwp hprod
    rw [hz,sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) (hF w)

def weilProductSet (q : QuadraticScales) (d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊4*(q.B*q.N₁)⌋₊).filter (fun w : ℕ => q.B*q.N₁ ≤ (w:ℝ) ∧ d ∣ w)

theorem pair_mem_weilProductSet {ρ K : ℝ} {q : QuadraticScales}
    (h : ScaleGeometry ρ K q) {b n d : ℕ}
    (hb : b ∈ Finset.Icc 1 ⌊2*q.B⌋₊) (hn : n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊)
    (hlow : q.B*q.N₁ ≤ (b*n:ℕ)) (hdw : d ∣ b*n) : b*n ∈ weilProductSet q d := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hb' : (b:ℝ) ≤ 2*q.B :=
    (show (b:ℝ) ≤ (⌊2*q.B⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp hb).2).trans
      (Nat.floor_le (by positivity))
  have hn' : (n:ℝ) ≤ 2*q.N₁ :=
    (show (n:ℝ) ≤ (⌊2*q.N₁⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
      (Nat.floor_le (by positivity))
  apply mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hn).1,?_⟩,
    hlow,hdw⟩
  apply (Nat.le_floor_iff (by positivity)).mpr
  have he := mul_le_mul hb' hn' (Nat.cast_nonneg n) (by positivity : 0 ≤ 2*q.B)
  push_cast
  nlinarith

theorem Estermann.outer_term_norm_le
    {ρ K : ℝ} {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hw : NormalizedWeightData bounds q α β W)
    {a b n k d : ℕ} (ha : a ∈ Finset.Icc 1 ⌊2*q.A⌋₊)
    (hb : b ∈ Finset.Icc 1 ⌊2*q.B⌋₊) (hn : n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊)
    (hd : 0 < d) {x : ℝ}
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)) (positive : Bool) (l : ℤ) :
    ‖weilOuterCoefficient q α β W a b n k d x*
      gcdWeilInnerSum (W 1) (W 4) a (b*n) d q.M₁ q.N₂ x (-l*signedShift positive k)‖ ≤
      if b*n ∈ weilProductSet q d ∧ k ≤ ⌊2*q.H/(d:ℝ)⌋₊ then
        (bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*
          (b*n/d:ℕ)^(1/2:ℝ)*Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d))*
            (1+(Nat.gcd a d:ℝ)*q.M₁/(b*n:ℕ)) else 0 := by
  have hC := hw.bounds_nonneg 0
  have hcomp := completionProfileConstant_nonneg hw.bounds_nonneg (by linarith : 0 ≤ K)
  have hM : 0 < q.M₁ := h.pos.2.2.1
  by_cases hc : weilOuterCoefficient q α β W a b n k d x = 0
  · rw [hc,zero_mul,norm_zero]
    split_ifs <;> positivity
  have hact := weilOuterCoefficient_active h.scales hw hd hc
  by_cases hdw : d ∣ b*n
  · have hs := pair_mem_weilProductSet h hb hn hact.1 hdw
    rw [ite_eq_left ⟨hs,hact.2⟩,norm_mul]
    have hi := Estermann.actual_inner_bound h hK hw ha hb hn hd hdw hx (-l*signedShift positive k)
    simp only [Int.natAbs_mul,Int.natAbs_neg,signedShift_natAbs,splitLeft,
      ← Real.sqrt_eq_rpow] at hi ⊢
    calc _ ≤ (bounds 0)^3*
        (completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*Real.sqrt (b*n/d:ℕ)*
          Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d))*(1+(Nat.gcd a d:ℝ)*q.M₁/(b*n:ℕ))) :=
        mul_le_mul (weilOuterCoefficient_norm hw a b n k d x) hi (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gcdWeilInnerSum_zero_of_not_dvd hdw,mul_zero,norm_zero]
    rw [ite_eq_right (by intro hh; exact hdw (mem_filter.mp hh.1).2.2)]

theorem Estermann.fixed_frequency_norm_le
    {ρ K : ℝ} {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hw : NormalizedWeightData bounds q α β W)
    {d : ℕ} (hd : 0 < d) {x : ℝ}
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)) (positive : Bool) (l : ℤ) :
    ‖fixedGcdFourierSum positive q α β W d l x‖ ≤
      ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
        if b*n ∈ weilProductSet q d then
          (bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*
            (b*n/d:ℕ)^(1/2:ℝ)*
              (∑ k ∈ Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊, Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d)))*
                (2*q.A*(d.divisors.card:ℝ)*(1+q.M₁/(b*n:ℕ))) else 0 := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hbc := hw.bounds_nonneg 0
  have hc := completionProfileConstant_nonneg hw.bounds_nonneg (by linarith : 0 ≤ K)
  rw [fixedGcdFourierSum_eq_weil_inner]
  have htri := norm_sum_le (Finset.Icc 1 ⌊2*q.A⌋₊)
    (fun a => ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊,
        weilOuterCoefficient q α β W a b n k d x*
          gcdWeilInnerSum (W 1) (W 4) a (b*n) d q.M₁ q.N₂ x (-l*signedShift positive k))
  apply le_trans htri
  have houter : (∑ a ∈ Finset.Icc 1 ⌊2*q.A⌋₊,
      ‖∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
        ∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊,
          weilOuterCoefficient q α β W a b n k d x*
            gcdWeilInnerSum (W 1) (W 4) a (b*n) d q.M₁ q.N₂ x (-l*signedShift positive k)‖) ≤
      ∑ a ∈ Finset.Icc 1 ⌊2*q.A⌋₊, ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊, ∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊,
          if b*n ∈ weilProductSet q d ∧ k ≤ ⌊2*q.H/(d:ℝ)⌋₊ then
            (bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*
              (b*n/d:ℕ)^(1/2:ℝ)*Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d))*
                (1+(Nat.gcd a d:ℝ)*q.M₁/(b*n:ℕ)) else 0 := by
    apply sum_le_sum; intro a ha
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro b hb
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro n hn
    apply (norm_sum_le _ _).trans
    apply sum_le_sum; intro k _
    exact Estermann.outer_term_norm_le h hK hw ha hb hn hd hx positive l
  apply houter.trans
  rw [sum_comm]
  apply sum_le_sum; intro b hb
  rw [sum_comm]
  apply sum_le_sum; intro n hn
  by_cases hs : b*n ∈ weilProductSet q d
  · simp only [hs,true_and,ite_true]
    have hwp : (0:ℝ) < (b*n:ℕ) := by
      exact_mod_cast Nat.mul_pos (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hn).1
    have hsub : Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊ ⊆ Finset.Icc 1 ⌊2*q.H⌋₊ := by
      apply Finset.Icc_subset_Icc le_rfl
      apply Nat.floor_le_floor
      exact div_le_self (by positivity) (by exact_mod_cast hd)
    have heq (a : ℕ) :
        (∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊, if k ≤ ⌊2*q.H/(d:ℝ)⌋₊ then
          (bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*
            (b*n/d:ℕ)^(1/2:ℝ)*Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d))*
              (1+(Nat.gcd a d:ℝ)*q.M₁/(b*n:ℕ)) else 0) =
        ((bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*
          (b*n/d:ℕ)^(1/2:ℝ)*
            (∑ k ∈ Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊, Real.sqrt (Nat.gcd (l.natAbs*k) (b*n/d))))*
              (1+(Nat.gcd a d:ℝ)*q.M₁/(b*n:ℕ)) := by
      rw [← Finset.sum_filter]
      have hfilter : {k ∈ Finset.Icc 1 ⌊2*q.H⌋₊ | k ≤ ⌊2*q.H/(d:ℝ)⌋₊} =
          Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊ := by
        ext k
        constructor
        · intro hk; exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩
        · intro hk; exact mem_filter.mpr ⟨hsub hk,(Finset.mem_Icc.mp hk).2⟩
      rw [hfilter,mul_sum,sum_mul]
    simp_rw [heq]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_weil_coefficient_factor_le hA.le hM₁.le hwp hd)
      (by positivity)
  · simp only [hs,false_and,ite_false,sum_const_zero]
    exact le_rfl

theorem Estermann.actual_weil_divisor_sum
    {ρ K : ℝ} {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hw : NormalizedWeightData bounds q α β W)
    {d : ℕ} (hd : 0 < d) {x : ℝ}
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)) (positive : Bool) :
    ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
      (16*(bounds 0)^3*completionProfileConstant bounds K*q.A*poissonLength q ρ d*q.H*
        (d.divisors.card:ℝ)/(d:ℝ))*
          ∑ w ∈ weilProductSet q d,
            twoAdicWeight (w/d)*(w.divisors.card:ℝ)*((w/d).divisors.card:ℝ)^3*
              (w/d:ℕ)^(1/2:ℝ)*(1+q.M₁/(w:ℝ)) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hL := poissonLength_pos q h.scales ρ hdr
  have hC := hw.bounds_nonneg 0
  have hcomp := completionProfileConstant_nonneg hw.bounds_nonneg (by linarith : 0 ≤ K)
  let F : ℕ → ℤ → ℝ := fun w l =>
    (bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (w/d)*((w/d).divisors.card:ℝ)*
      (w/d:ℕ)^(1/2:ℝ)*
        (∑ k ∈ Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊, Real.sqrt (Nat.gcd (l.natAbs*k) (w/d)))*
          (2*q.A*(d.divisors.card:ℝ)*(1+q.M₁/(w:ℝ)))
  have hF (w : ℕ) (l : ℤ) : 0 ≤ F w l := by dsimp [F]; positivity
  have htri : ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
      ∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else
        ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
          if b*n ∈ weilProductSet q d then F (b*n) l else 0 := by
    rw [gcdBlockIntegrand_eq_frequency_sum]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro l _
    by_cases hl : l = 0
    · simp only [hl,ite_true,norm_zero]; exact le_rfl
    · simp only [ite_eq_right hl,norm_mul,norm_ePhase,mul_one]
      have hcut : ‖(sourceCutoff ((l:ℝ)/poissonLength q ρ d):ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using sourceCutoff_norm ((l:ℝ)/poissonLength q ρ d)
      calc _ ≤ 1*‖fixedGcdFourierSum positive q α β W d l x‖ :=
          mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
        _ ≤ _ := by
          rw [one_mul]
          exact Estermann.fixed_frequency_norm_le h hK hw hd hx positive l
  have heq : (∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else
      ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
        if b*n ∈ weilProductSet q d then F (b*n) l else 0) =
      ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
        if b*n ∈ weilProductSet q d then
          ∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else F (b*n) l else 0 := by
    calc _ = ∑ l ∈ frequencySet (2*poissonLength q ρ d),
          ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
            if b*n ∈ weilProductSet q d then (if l = 0 then 0 else F (b*n) l) else 0 := by
          apply sum_congr rfl; intro l _
          by_cases hl : l = 0 <;> simp [hl]
      _ = ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
          ∑ l ∈ frequencySet (2*poissonLength q ρ d),
            if b*n ∈ weilProductSet q d then (if l = 0 then 0 else F (b*n) l) else 0 := by
          rw [Finset.sum_comm]
          apply sum_congr rfl; intro b _
          rw [Finset.sum_comm]
      _ = _ := by
          apply sum_congr rfl; intro b _
          apply sum_congr rfl; intro n _
          by_cases hs : b*n ∈ weilProductSet q d <;> simp [hs]
  rw [heq] at htri
  have hgroup := pair_product_sum_bound hB hN₁ (weilProductSet q d)
    (fun w => ∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else F w l)
    (fun w => sum_nonneg (fun l _ => by split_ifs <;> first | exact le_rfl | exact hF w l))
  apply (htri.trans hgroup).trans
  rw [mul_sum]
  apply sum_le_sum
  intro w hw'
  obtain ⟨hw',hWw,hdw⟩ := mem_filter.mp hw'
  have hwp : 0 < w := (Finset.mem_Icc.mp hw').1
  have hc : 0 < w/d := Nat.div_pos (Nat.le_of_dvd hwp hdw) hd
  have hav := signed_frequency_sqrt_gcd_average (by positivity : 0 ≤ 2*poissonLength q ρ d)
    (by positivity : 0 ≤ 2*q.H/(d:ℝ)) (w/d) hc.ne'
  have heq' : (∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else F w l) =
      ((bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (w/d)*((w/d).divisors.card:ℝ)*
        (w/d:ℕ)^(1/2:ℝ)*(2*q.A*(d.divisors.card:ℝ)*(1+q.M₁/(w:ℝ))))*
          (∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else
            ∑ k ∈ Finset.Icc 1 ⌊2*q.H/(d:ℝ)⌋₊, Real.sqrt (Nat.gcd (l.natAbs*k) (w/d))) := by
    rw [mul_sum]
    apply sum_congr rfl; intro l _
    by_cases hl : l = 0
    · simp only [hl,ite_true,mul_zero]
    · simp only [ite_eq_right hl,F]
      ring
  rw [heq']
  calc _ ≤ (w.divisors.card:ℝ)*
      (((bounds 0)^3*completionProfileConstant bounds K*twoAdicWeight (w/d)*((w/d).divisors.card:ℝ)*
        (w/d:ℕ)^(1/2:ℝ)*(2*q.A*(d.divisors.card:ℝ)*(1+q.M₁/(w:ℝ))))*
          (2*(2*poissonLength q ρ d)*(2*q.H/(d:ℝ))*((w/d).divisors.card:ℝ)^2)) := by
        gcongr
    _ = _ := by ring

theorem uniform_divisor_cost {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (Q : ℝ), 1 ≤ Q → ∀ n : ℕ,
      0 < n → (n:ℝ) ≤ 4*Q → (n.divisors.card:ℝ) ≤ T*Q^ρ := by
  obtain ⟨C,hC,hτ⟩ := divisor_count_subpower hρ
  refine ⟨C*4^ρ,by positivity,?_⟩
  intro Q hQ n hn hnQ
  calc _ ≤ C*(n:ℝ)^ρ := hτ n hn.ne'
    _ ≤ C*(4*Q)^ρ := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by linarith : 0 ≤ Q)]; ring

/-- Lemma 5.1, uniformly in every varying scale and weight. Its only
number-theoretic input is SALT's proved Estermann theorem, averaged over the modulus. -/
theorem Estermann.actual_pointwise_weil_bound
    {ρ K : ℝ} (hρ : 0 < ρ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), ScaleGeometry ρ K q →
      NormalizedWeightData bounds q α β W → ∀ (positive : Bool) (d : ℕ), 0 < d → ∀ x : ℝ,
        ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
          C*q.mass^(5*ρ)*q.A*poissonLength q ρ d*q.H*
            (q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ) := by
  obtain ⟨T,hT,hτ⟩ := uniform_divisor_cost hρ
  have hcomp := completionProfileConstant_nonneg hbounds (by linarith : 0 ≤ K)
  have hb0 := hbounds 0
  refine ⟨512*(bounds 0)^3*completionProfileConstant bounds K*T^5,by positivity,?_⟩
  intro q α β W h hw positive d hd x
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hL := poissonLength_pos q h.scales ρ hdr
  have hW : 0 < q.B*q.N₁ := mul_pos hB hN₁
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  have hWQ := (poisson_scale_bounds q h.scales).2.2.1
  by_cases hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)
  · have hraw := Estermann.actual_weil_divisor_sum h hK hw hd hx positive
    by_cases hset : (weilProductSet q d).Nonempty
    · let D := T*q.mass^ρ
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hupper (w : ℕ) (hw' : w ∈ weilProductSet q d) : (w:ℝ) ≤ 4*q.mass := by
        have hu := (Finset.mem_Icc.mp (mem_filter.mp hw').1).2
        have hr : (w:ℝ) ≤ 4*(q.B*q.N₁) :=
          (show (w:ℝ) ≤ (⌊4*(q.B*q.N₁)⌋₊:ℝ) by exact_mod_cast hu).trans
            (Nat.floor_le (by positivity))
        nlinarith
      have htau (w : ℕ) (hw' : w ∈ weilProductSet q d) :
          (w.divisors.card:ℝ) ≤ D ∧ ((w/d).divisors.card:ℝ) ≤ D := by
        have hwp := (Finset.mem_Icc.mp (mem_filter.mp hw').1).1
        have hdw := (mem_filter.mp hw').2.2
        have hcp : 0 < w/d := Nat.div_pos (Nat.le_of_dvd hwp hdw) hd
        exact ⟨hτ q.mass hQ₁ w hwp (hupper w hw'),hτ q.mass hQ₁ (w/d) hcp
          ((show (w/d:ℕ) ≤ (w:ℝ) by exact_mod_cast Nat.div_le_self w d).trans (hupper w hw'))⟩
      have htaud : (d.divisors.card:ℝ) ≤ D := by
        obtain ⟨w,hw'⟩ := hset
        have hwp := (Finset.mem_Icc.mp (mem_filter.mp hw').1).1
        have hdw := (mem_filter.mp hw').2.2
        exact hτ q.mass hQ₁ d hd
          ((show (d:ℝ) ≤ w by exact_mod_cast Nat.le_of_dvd hwp hdw).trans (hupper w hw'))
      have hsum : (∑ w ∈ weilProductSet q d,
          twoAdicWeight (w/d)*(w.divisors.card:ℝ)*((w/d).divisors.card:ℝ)^3*
            (w/d:ℕ)^(1/2:ℝ)*(1+q.M₁/(w:ℝ))) ≤
          (D^4/(d:ℝ)^(1/2:ℝ))*(32*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)/(d:ℝ)) := by
        have hterm : (∑ w ∈ weilProductSet q d,
            twoAdicWeight (w/d)*(w.divisors.card:ℝ)*((w/d).divisors.card:ℝ)^3*
              (w/d:ℕ)^(1/2:ℝ)*(1+q.M₁/(w:ℝ))) ≤
            (D^4/(d:ℝ)^(1/2:ℝ))*
              ∑ w ∈ weilProductSet q d, twoAdicWeight (w/d)*(w:ℝ)^(1/2:ℝ)*(1+q.M₁/(w:ℝ)) := by
          rw [mul_sum]
          apply sum_le_sum
          intro w hw'
          obtain ⟨ht₁,ht₂⟩ := htau w hw'
          have hdw := (mem_filter.mp hw').2.2
          rw [Nat.cast_div_charZero hdw,Real.div_rpow (Nat.cast_nonneg _) hdr.le]
          calc _ ≤ twoAdicWeight (w/d)*D*D^3*((w:ℝ)^(1/2:ℝ)/(d:ℝ)^(1/2:ℝ))*(1+q.M₁/(w:ℝ)) := by gcongr
            _ = _ := by ring
        exact hterm.trans (mul_le_mul_of_nonneg_left
          (estermann_product_multiple_sum_le hW hM₁.le hd) (by positivity))
      have hfirst : ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
          (16*(bounds 0)^3*completionProfileConstant bounds K*q.A*poissonLength q ρ d*q.H*
            D/(d:ℝ))*
              ((D^4/(d:ℝ)^(1/2:ℝ))*(32*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)/(d:ℝ))) := by
        apply hraw.trans
        have hfac : 16*(bounds 0)^3*completionProfileConstant bounds K*q.A*
            poissonLength q ρ d*q.H*(d.divisors.card:ℝ)/(d:ℝ) ≤
            16*(bounds 0)^3*completionProfileConstant bounds K*q.A*
              poissonLength q ρ d*q.H*D/(d:ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htaud (by positivity)) hdr.le
        exact mul_le_mul hfac hsum
          (sum_nonneg (fun w _ => by positivity)) (by positivity)
      have hdroot : (d:ℝ)^(1/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hdr _).ne'
      have hdexp : (d:ℝ)^(-5/2:ℝ) = ((d:ℝ)^2*(d:ℝ)^(1/2:ℝ))⁻¹ := by
        rw [show (-5/2:ℝ) = -(2+1/2) by norm_num,Real.rpow_neg hdr.le,
          Real.rpow_add hdr,Real.rpow_two]
      have hDpow : D^5 = T^5*q.mass^(5*ρ) := by
        dsimp [D]
        rw [mul_pow,← Real.rpow_mul_natCast hQ.le]
        congr 2
        ring
      apply hfirst.trans_eq
      rw [hdexp]
      calc _ = (512*(bounds 0)^3*completionProfileConstant bounds K*D^5)*q.A*
          poissonLength q ρ d*q.H*(q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*
            ((d:ℝ)^2*(d:ℝ)^(1/2:ℝ))⁻¹ := by field_simp; ring
        _ = _ := by rw [hDpow]; ring
    · have hempty : weilProductSet q d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hset
      simp only [hempty,sum_empty,mul_zero] at hraw
      exact hraw.trans (by positivity)
  · rw [gcdBlockIntegrand_eq_zero_off_support h.scales hw positive ρ d hx,norm_zero]
    positivity

end
end DivisorProof

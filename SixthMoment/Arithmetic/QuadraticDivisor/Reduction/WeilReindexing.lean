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
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.SourceBounds
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WattProfiles
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WeilBounds
import Std

namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem split_product_without_division (a d v : ℕ) :
    a*(splitRight a d*v) = d*(splitCoefficient a d*v) := by
  calc _ = (splitLeft a d*splitCoefficient a d)*(splitRight a d*v) := by
        rw [split_coefficient_mul]
    _ = (splitLeft a d*splitRight a d)*(splitCoefficient a d*v) := by ring
    _ = _ := by rw [split_factors_mul]

theorem gcd_split_inner_iff (a w : ℕ) {d : ℕ} (hd : 0 < d) (hdw : d ∣ w) (v : ℕ) :
    Nat.gcd (a*(splitRight a d*v)) w = d ↔
      (splitCoefficient a d*v).Coprime (w/d) := by
  have hw : w = d*(w/d) := (Nat.mul_div_cancel' hdw).symm
  rw [split_product_without_division,hw,Nat.gcd_mul_left]
  rw [Nat.mul_div_cancel_left _ hd]
  constructor
  · intro h
    change Nat.gcd _ _ = 1
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa using h)
  · intro h
    rw [h.gcd_eq_one,mul_one]

theorem finite_gcd_inner_reindex {E : Type*} [AddCommMonoid E]
    (a w : ℕ) {d : ℕ} (hd : 0 < d) (hdw : d ∣ w)
    {M : ℝ} (hM : 0 ≤ M) (f : ℕ → E) :
    (∑ m ∈ (Finset.Icc 1 ⌊2*M⌋₊).filter (fun m => Nat.gcd (a*m) w = d), f m) =
      ∑ v ∈ (Finset.Icc 1 ⌊2*M/(splitRight a d:ℝ)⌋₊).filter
        (fun v => (splitCoefficient a d*v).Coprime (w/d)), f (splitRight a d*v) := by
  have hd₂ := splitRight_pos a hd
  have hd₂r : (0:ℝ) < splitRight a d := by exact_mod_cast hd₂
  symm
  apply Finset.sum_bij (fun v _ => splitRight a d*v)
  · intro v hv
    obtain ⟨hvr,hcop⟩ := Finset.mem_filter.mp hv
    obtain ⟨hvp,hvhi⟩ := Finset.mem_Icc.mp hvr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd₂ hvp,?_⟩,
      (gcd_split_inner_iff a w hd hdw v).mpr hcop⟩
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*M)).mpr
    have hvhi' : (v:ℝ) ≤ 2*M/(splitRight a d:ℝ) :=
      (show (v:ℝ) ≤ (⌊2*M/(splitRight a d:ℝ)⌋₊:ℝ) by exact_mod_cast hvhi).trans
        (Nat.floor_le (by positivity))
    have ht := (le_div_iff₀ hd₂r).mp hvhi'
    push_cast
    nlinarith
  · intro v _ v' _ heq
    exact Nat.eq_of_mul_eq_mul_left hd₂ heq
  · intro m hm
    obtain ⟨hmr,hgcd⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmp,hmhi⟩ := Finset.mem_Icc.mp hmr
    have hdma : d ∣ a*m := by rw [← hgcd]; exact Nat.gcd_dvd_left _ _
    have hd₂m := splitRight_dvd_inner hd hdma
    have hrepr : splitRight a d*(m/splitRight a d) = m := Nat.mul_div_cancel' hd₂m
    refine ⟨m/splitRight a d,Finset.mem_filter.mpr ⟨?_,?_⟩,hrepr⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.div_pos (Nat.le_of_dvd hmp hd₂m) hd₂
      · apply (Nat.le_floor_iff (by positivity : 0 ≤ 2*M/(splitRight a d:ℝ))).mpr
        apply (le_div_iff₀ hd₂r).mpr
        have hmhi' : (m:ℝ) ≤ 2*M :=
          (show (m:ℝ) ≤ (⌊2*M⌋₊:ℝ) by exact_mod_cast hmhi).trans (Nat.floor_le (by positivity))
        have hr : (splitRight a d:ℝ)*(m/splitRight a d:ℕ) = (m:ℝ) := by exact_mod_cast hrepr
        nlinarith
    · apply (gcd_split_inner_iff a w hd hdw _).mp
      rwa [hrepr]
  · intro v _
    rfl

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def gcdWeilInnerSum (W₁ W₄ : ℝ → ℝ) (a w d : ℕ) (M₁ N₂ x : ℝ) (k : ℤ) : ℂ :=
  ∑ m ∈ (Finset.Icc 1 ⌊2*M₁⌋₊).filter (fun m => Nat.gcd (a*m) w = d),
    (W₁ ((m:ℝ)/M₁):ℂ)*(W₄ ((a:ℝ)*m*x/((d:ℝ)*N₂)):ℂ)*
      ePhase ((k:ℝ)*(inverseRepresentative (a*m/d) (w/d):ℝ)/(w/d:ℕ))

theorem gcdWeilInnerSum_eq_shortened {W₁ W₄ : ℝ → ℝ} (a w : ℕ) {d : ℕ}
    (hd : 0 < d) (hdw : d ∣ w) {M₁ N₂ x : ℝ} (hM : 0 < M₁) (hN : 0 < N₂) (k : ℤ) :
    gcdWeilInnerSum W₁ W₄ a w d M₁ N₂ x k =
      ∑ v ∈ Finset.Icc 1 ⌊2*M₁/(splitRight a d:ℝ)⌋₊,
        shortenedWeilTerm W₁ W₄ ((splitRight a d:ℝ)/M₁)
          ((splitCoefficient a d:ℝ)*x/N₂) (splitCoefficient a d) (w/d) k v := by
  have hd₂ := splitRight_pos a hd
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hd₂r : (0:ℝ) < splitRight a d := by exact_mod_cast hd₂
  unfold gcdWeilInnerSum
  rw [finite_gcd_inner_reindex a w hd hdw hM.le,Finset.sum_filter]
  apply sum_congr rfl
  intro v _
  unfold shortenedWeilTerm
  by_cases hv : (splitCoefficient a d*v).Coprime (w/d)
  · rw [ite_eq_left hv,ite_eq_left hv]
    have hp : a*(splitRight a d*v)/d = splitCoefficient a d*v := by
      rw [split_product_without_division,Nat.mul_div_cancel_left _ hd]
    rw [hp]
    unfold poissonProfile
    have hnat : a*splitRight a d = d*splitCoefficient a d := by
      simpa only [Nat.mul_one] using split_product_without_division a d 1
    have hprod : (a:ℝ)*(splitRight a d:ℝ) = (d:ℝ)*(splitCoefficient a d:ℝ) := by
      exact_mod_cast hnat
    have he₁ : ((splitRight a d*v:ℕ):ℝ)/M₁ = ((splitRight a d:ℝ)/M₁)*(v:ℝ) := by
      push_cast
      ring
    have he₄ : (a:ℝ)*(splitRight a d*v:ℕ)*x/((d:ℝ)*N₂) =
        ((splitCoefficient a d:ℝ)*x/N₂)*(v:ℝ) := by
      push_cast
      calc _ = ((a:ℝ)*(splitRight a d:ℝ))*(v:ℝ)*x/((d:ℝ)*N₂) := by ring
           _ = ((d:ℝ)*(splitCoefficient a d:ℝ))*(v:ℝ)*x/((d:ℝ)*N₂) := by rw [hprod]
           _ = _ := by field_simp
    rw [he₁,he₄]
  · rw [ite_eq_right hv,ite_eq_right hv]

theorem Estermann.original_gcd_inner_bound
    {W₁ W₄ : ℝ → ℝ} (h₁ : SmoothDyadicWeight W₁) (h₄ : SmoothDyadicWeight W₄)
    (a w : ℕ) (hw : 0 < w) {d : ℕ} (hd : 0 < d) (hdw : d ∣ w)
    {M₁ N₂ x K : ℝ} {bounds : ℕ → ℝ} (hM : 0 < M₁) (hN : 0 < N₂)
    (hK : 1 ≤ K)
    (hb : 0 ≤ ((splitCoefficient a d:ℝ)*x/N₂)*(M₁/(splitRight a d:ℝ)))
    (hbK : ((splitCoefficient a d:ℝ)*x/N₂)*(M₁/(splitRight a d:ℝ)) ≤ K)
    (hder₁ : ∀ j y, ‖iteratedDeriv j W₁ y‖ ≤ bounds j)
    (hder₄ : ∀ j y, ‖iteratedDeriv j W₄ y‖ ≤ bounds j) (k : ℤ) :
    ‖gcdWeilInnerSum W₁ W₄ a w d M₁ N₂ x k‖ ≤
      ((2+2*Real.pi)*profileFourierBound bounds K 2)*
        twoAdicWeight (w/d)*((w/d).divisors.card:ℝ)*(w/d:ℕ)^(1/2:ℝ)*
          (Nat.gcd k.natAbs (w/d):ℝ)^(1/2:ℝ)*
            (1+(M₁/(splitRight a d:ℝ))/(w/d:ℕ)) := by
  have hd₂ := splitRight_pos a hd
  have hd₂r : (0:ℝ) < splitRight a d := by exact_mod_cast hd₂
  have hc : 0 < w/d := Nat.div_pos (Nat.le_of_dvd hw hdw) hd
  have heq : ((splitRight a d:ℝ)/M₁)*(M₁/(splitRight a d:ℝ)) = 1 := by field_simp
  have hupper : 2/((splitRight a d:ℝ)/M₁) = 2*M₁/(splitRight a d:ℝ) := by field_simp
  rw [gcdWeilInnerSum_eq_shortened a w hd hdw hM hN k,← hupper]
  exact Estermann.shortened_inner_bound h₁ h₄ (div_pos hM hd₂r)
    (by rw [heq]) hb (by rw [heq]; exact hK) hbK hder₁ hder₄ hc k

end
end DivisorProof



namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000

theorem gcd_coefficient_fiber_card_le {A : ℝ} (hA : 0 ≤ A)
    (d : ℕ) {e : ℕ} (he : 0 < e) :
    (({a ∈ Finset.Icc 1 ⌊2*A⌋₊ | Nat.gcd a d = e}).card:ℝ) ≤ 2*A/(e:ℝ) := by
  have hsub : {a ∈ Finset.Icc 1 ⌊2*A⌋₊ | Nat.gcd a d = e} ⊆
      {a ∈ Finset.Icc 1 ⌊2*A⌋₊ | e ∣ a} := by
    intro a ha
    obtain ⟨ha,hgcd⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨ha,by rw [← hgcd]; exact Nat.gcd_dvd_left _ _⟩
  have hcard := (Finset.card_le_card hsub).trans (card_positive_multiples_le ⌊2*A⌋₊ e he)
  have hprod : ({a ∈ Finset.Icc 1 ⌊2*A⌋₊ | Nat.gcd a d = e}).card*e ≤ ⌊2*A⌋₊ :=
    (Nat.mul_le_mul_right e hcard).trans (Nat.div_mul_le_self _ _)
  have he' : (0:ℝ) < e := by exact_mod_cast he
  apply (le_div_iff₀ he').mpr
  exact (show (({a ∈ Finset.Icc 1 ⌊2*A⌋₊ | Nat.gcd a d = e}).card:ℝ)*e ≤ (⌊2*A⌋₊:ℝ)
    by exact_mod_cast hprod).trans (Nat.floor_le (by positivity))

theorem sum_gcd_coefficient_cost_le {A : ℝ} (hA : 0 ≤ A) {d : ℕ} (hd : 0 < d)
    (F : ℕ → ℝ) (hF : ∀ e ∈ d.divisors, 0 ≤ F e) :
    (∑ a ∈ Finset.Icc 1 ⌊2*A⌋₊, F (Nat.gcd a d)) ≤
      ∑ e ∈ d.divisors, (2*A/(e:ℝ))*F e := by
  have hmap : ∀ a ∈ Finset.Icc 1 ⌊2*A⌋₊, Nat.gcd a d ∈ d.divisors := by
    intro a _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hd.ne'⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmap F]
  apply sum_le_sum
  intro e he
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (gcd_coefficient_fiber_card_le hA d (Nat.pos_of_mem_divisors he)) (hF e he)

theorem sum_weil_coefficient_factor_le {A M w : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hw : 0 < w) {d : ℕ} (hd : 0 < d) :
    (∑ a ∈ Finset.Icc 1 ⌊2*A⌋₊, (1+(Nat.gcd a d:ℝ)*M/w)) ≤
      2*A*(d.divisors.card:ℝ)*(1+M/w) := by
  have hfirst := sum_gcd_coefficient_cost_le hA hd (fun e => 1+(e:ℝ)*M/w)
    (fun e _ => by positivity)
  apply hfirst.trans
  calc _ ≤ ∑ _e ∈ d.divisors, 2*A*(1+M/w) := by
        apply sum_le_sum
        intro e he
        have hep := Nat.pos_of_mem_divisors he
        have her : (1:ℝ) ≤ e := by exact_mod_cast hep
        have he' : (0:ℝ) < e := by exact_mod_cast hep
        have hid : (2*A/(e:ℝ))*(1+(e:ℝ)*M/w) = 2*A*((1:ℝ)/e+M/w) := by field_simp
        rw [hid]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) her) le_rfl
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end
end DivisorProof



namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem nonzero_frequency_abs_sum_le {L : ℝ} (hL : 0 ≤ L)
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ l ∈ frequencySet L, if l = 0 then 0 else F l.natAbs) ≤
      2*∑ n ∈ Finset.Icc 1 ⌊L⌋₊, F n := by
  let s := (frequencySet L).filter (fun l : ℤ => l ≠ 0)
  have hmap : ∀ l ∈ s, l.natAbs ∈ Finset.Icc 1 ⌊L⌋₊ := by
    intro l hl
    obtain ⟨hl,hl₀⟩ := mem_filter.mp hl
    refine Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hl₀,?_⟩
    apply (Nat.le_floor_iff hL).mpr
    simpa only [Nat.cast_natAbs,Int.cast_abs] using (mem_frequencySet L l).mp hl
  have hcard (n : ℕ) : ({l ∈ s | l.natAbs = n}).card ≤ 2 := by
    have hsub : {l ∈ s | l.natAbs = n} ⊆ ({(n:ℤ),-(n:ℤ)}:Finset ℤ) := by
      intro l hl
      rcases Int.natAbs_eq_iff.mp (mem_filter.mp hl).2 with h | h
      · simp [h]
      · simp [h]
    have hpair : ({(n:ℤ),-(n:ℤ)}:Finset ℤ).card ≤ 2 := by
      simpa using Finset.card_insert_le (n:ℤ) ({-(n:ℤ)}:Finset ℤ)
    exact (Finset.card_le_card hsub).trans hpair
  have heq : (∑ l ∈ frequencySet L, if l = 0 then 0 else F l.natAbs) =
      ∑ l ∈ s, F l.natAbs := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro l _
    by_cases hl : l = 0 <;> simp [hl]
  rw [heq,← Finset.sum_fiberwise_of_maps_to' hmap F,Finset.mul_sum]
  apply sum_le_sum
  intro n _
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n) (hF n)

theorem signed_frequency_sqrt_gcd_average {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U)
    (c : ℕ) (hc : c ≠ 0) :
    (∑ l ∈ frequencySet L, if l = 0 then 0 else
      ∑ k ∈ Finset.Icc 1 ⌊U⌋₊, Real.sqrt (Nat.gcd (l.natAbs*k) c)) ≤
      2*L*U*(c.divisors.card:ℝ)^2 := by
  have h := nonzero_frequency_abs_sum_le hL
    (fun n => ∑ k ∈ Finset.Icc 1 ⌊U⌋₊, Real.sqrt (Nat.gcd (n*k) c))
    (fun n => sum_nonneg (fun k _ => Real.sqrt_nonneg _))
  exact h.trans ((mul_le_mul_of_nonneg_left (averaged_sqrt_gcd_le hL hU c hc)
    (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def weilOuterCoefficient (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (a b n k d : ℕ) (x : ℝ) : ℂ :=
  α a*β b*(W 0 ((d:ℝ)*k/q.H):ℂ)*(W 3 ((n:ℝ)/q.N₁):ℂ)*
    (W 2 (((b*n:ℕ):ℝ)*x/((d:ℝ)*q.M₂)):ℂ)

theorem fixedGcdFourierSum_eq_weil_inner (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (l : ℤ) (x : ℝ) :
    fixedGcdFourierSum positive q α β W d l x =
      ∑ a ∈ Finset.Icc 1 ⌊2*q.A⌋₊, ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊, ∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊,
          weilOuterCoefficient q α β W a b n k d x*
            gcdWeilInnerSum (W 1) (W 4) a (b*n) d q.M₁ q.N₂ x
              (-l*signedShift positive k) := by
  unfold fixedGcdFourierSum
  rw [Finset.sum_filter,quadraticMainIndexSet_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  unfold gcdWeilInnerSum
  rw [Finset.sum_filter,mul_sum]
  apply sum_congr rfl
  intro m _
  have hgd : outerGCD (![a,b,m,n,k] : Fin 5 → ℕ) = Nat.gcd (a*m) (b*n) := by
    simp [outerGCD,outerLeft,outerRight]
  by_cases hg : Nat.gcd (a*m) (b*n) = d
  · rw [hgd,ite_eq_left hg,ite_eq_left hg]
    dsimp [poissonOuterWeight,outerPoissonProfile,outerPoissonPhase,poissonProfile,
      outerGCD,outerLeft,outerRight,weilOuterCoefficient]
    simp only [hg,Nat.cast_mul,div_mul_eq_mul_div,Int.cast_mul,Int.cast_neg]
    have he : -(l:ℝ)*((signedShift positive k:ℝ)*
        (inverseRepresentative (a*m/d) (b*n/d):ℝ)/(b*n/d:ℕ)) =
        (-(l:ℝ)*(signedShift positive k:ℝ))*
          (inverseRepresentative (a*m/d) (b*n/d):ℝ)/(b*n/d:ℕ) := by ring
    rw [he]
    ring
  · rw [hgd,ite_eq_right hg,ite_eq_right hg,mul_zero]

end
end DivisorProof



namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000

theorem positive_pair_product_fiber_card_le (B N : ℝ) {w : ℕ} (hw : 0 < w) :
    ((Finset.Icc 1 ⌊2*B⌋₊ ×ˢ Finset.Icc 1 ⌊2*N⌋₊).filter
      (fun p : ℕ × ℕ => p.1*p.2 = w)).card ≤ w.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p => p.1)
  · intro p hp
    obtain ⟨hp,hprod⟩ := mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨by rw [← hprod]; exact dvd_mul_right _ _,hw.ne'⟩
  · intro p hp q hq heq
    obtain ⟨hp,hp'⟩ := mem_filter.mp hp
    obtain ⟨_,hq'⟩ := mem_filter.mp hq
    have hpos : 0 < p.1 := (Finset.mem_Icc.mp (mem_product.mp hp).1).1
    change p.1 = q.1 at heq
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hp',heq,hq']

theorem positive_multiple_card_real_le {W : ℝ} (hW : 0 ≤ W)
    {d : ℕ} (hd : 0 < d) :
    (({w ∈ Finset.Icc 1 ⌊4*W⌋₊ | d ∣ w}).card:ℝ) ≤ 4*W/(d:ℝ) := by
  have hc := card_positive_multiples_le ⌊4*W⌋₊ d hd
  have hp : ({w ∈ Finset.Icc 1 ⌊4*W⌋₊ | d ∣ w}).card*d ≤ ⌊4*W⌋₊ :=
    (Nat.mul_le_mul_right d hc).trans (Nat.div_mul_le_self _ _)
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)).mpr
  exact (show (({w ∈ Finset.Icc 1 ⌊4*W⌋₊ | d ∣ w}).card:ℝ)*d ≤ (⌊4*W⌋₊:ℝ)
    by exact_mod_cast hp).trans (Nat.floor_le (by positivity))

theorem weil_product_multiple_sum_le {W M : ℝ} (hW : 0 < W) (hM : 0 ≤ M)
    {d : ℕ} (hd : 0 < d) :
    (∑ w ∈ (Finset.Icc 1 ⌊4*W⌋₊).filter (fun w : ℕ => W ≤ (w:ℝ) ∧ d ∣ w),
      (w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ))) ≤ 8*W^(1/2:ℝ)*(W+M)/(d:ℝ) := by
  let s := (Finset.Icc 1 ⌊4*W⌋₊).filter (fun w : ℕ => W ≤ (w:ℝ) ∧ d ∣ w)
  have hsub : s ⊆ {w ∈ Finset.Icc 1 ⌊4*W⌋₊ | d ∣ w} := by
    intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).1,(mem_filter.mp hw).2.2⟩
  have hccard : (s.card:ℝ) ≤ ({w ∈ Finset.Icc 1 ⌊4*W⌋₊ | d ∣ w}.card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hc : (s.card:ℝ) ≤ 4*W/(d:ℝ) := hccard.trans (positive_multiple_card_real_le hW.le hd)
  have hb (w : ℕ) (hw : w ∈ s) :
      (w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ)) ≤ 2*W^(1/2:ℝ)*(1+M/W) := by
    obtain ⟨hwr,hWw,_⟩ := mem_filter.mp hw
    have hwp : (0:ℝ) < w := hW.trans_le hWw
    have hwupper : (w:ℝ) ≤ 4*W :=
      (show (w:ℝ) ≤ (⌊4*W⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp hwr).2).trans
        (Nat.floor_le (by positivity))
    have hroot : (w:ℝ)^(1/2:ℝ) ≤ 2*W^(1/2:ℝ) := by
      apply (Real.rpow_le_rpow hwp.le hwupper (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hW.le]
      norm_num [← Real.sqrt_eq_rpow]
    have hratio : M/(w:ℝ) ≤ M/W := div_le_div_of_nonneg_left hM hW hWw
    exact mul_le_mul hroot (add_le_add le_rfl hratio) (by positivity) (by positivity)
  change ∑ w ∈ s, (w:ℝ)^(1/2:ℝ)*(1+M/(w:ℝ)) ≤ _
  calc _ ≤ ∑ _w ∈ s, 2*W^(1/2:ℝ)*(1+M/W) := sum_le_sum hb
    _ = (s.card:ℝ)*(2*W^(1/2:ℝ)*(1+M/W)) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (4*W/(d:ℝ))*(2*W^(1/2:ℝ)*(1+M/W)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by field_simp; norm_num

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def completionProfileConstant (bounds : ℕ → ℝ) (K : ℝ) : ℝ :=
  (2+2*Real.pi)*profileFourierBound bounds (4*K) 2

theorem completionProfileConstant_nonneg {bounds : ℕ → ℝ} {K : ℝ}
    (hb : ∀ j, 0 ≤ bounds j) (hK : 0 ≤ K) : 0 ≤ completionProfileConstant bounds K := by
  have hC := profileFourierBound_nonneg hb (by positivity : 0 ≤ 4*K) 2
  unfold completionProfileConstant
  positivity

theorem divisor_completion_factor {d e f w M : ℝ}
    (hd : 0 < d) (hf : 0 < f) (hw : 0 < w) (hef : e*f = d) :
    (M/f)/(w/d) = e*M/w := by
  have he : 0 < e := by nlinarith
  rw [← hef]
  field_simp

theorem Estermann.actual_inner_bound
    {ρ K : ℝ} {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (h : ScaleGeometry ρ K q) (hK : 1 ≤ K) (hw : NormalizedWeightData bounds q α β W)
    {a b n d : ℕ} (ha : a ∈ Finset.Icc 1 ⌊2*q.A⌋₊)
    (hb : b ∈ Finset.Icc 1 ⌊2*q.B⌋₊) (hn : n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊)
    (hd : 0 < d) (hdw : d ∣ b*n) {x : ℝ}
    (hx : x ∈ Icc (poissonRadius q d/4) (2*poissonRadius q d)) (k : ℤ) :
    ‖gcdWeilInnerSum (W 1) (W 4) a (b*n) d q.M₁ q.N₂ x k‖ ≤
      completionProfileConstant bounds K*twoAdicWeight (b*n/d)*((b*n/d).divisors.card:ℝ)*(b*n/d:ℕ)^(1/2:ℝ)*
        (Nat.gcd k.natAbs (b*n/d):ℝ)^(1/2:ℝ)*
          (1+(splitLeft a d:ℝ)*q.M₁/(b*n:ℕ)) := by
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have he₁ : (0:ℝ) < splitLeft a d := by exact_mod_cast splitLeft_pos a hd
  have he₂ : (0:ℝ) < splitRight a d := by exact_mod_cast splitRight_pos a hd
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hwp : 0 < b*n := Nat.mul_pos (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hn).1
  have hwpr : (0:ℝ) < (b*n:ℕ) := by exact_mod_cast hwp
  have hprod : (splitLeft a d:ℝ)*splitRight a d = (d:ℝ) := by
    exact_mod_cast split_factors_mul a d
  have ha₂ : (a:ℝ) ≤ 2*q.A :=
    (show (a:ℝ) ≤ (⌊2*q.A⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp ha).2).trans
      (Nat.floor_le (by positivity))
  have hb₂ : (b:ℝ) ≤ 2*q.B :=
    (show (b:ℝ) ≤ (⌊2*q.B⌋₊:ℝ) by exact_mod_cast (Finset.mem_Icc.mp hb).2).trans
      (Nat.floor_le (by positivity))
  have hrb : (splitCoefficient a d:ℝ) ≤ 2*q.A/(splitLeft a d:ℝ) := by
    apply (le_div_iff₀ he₁).mpr
    have he : (splitLeft a d:ℝ)*splitCoefficient a d = (a:ℝ) := by
      exact_mod_cast split_coefficient_mul a d
    nlinarith
  have hs := naturalWatt_profile_slopes h hK he₁ he₂ (by norm_num : (0:ℝ) < 1) hdr
    hprod (by ring : (1:ℝ)*(d:ℝ) = d) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hrb (by simpa using hb₂) hx
  have heq : (q.M₁/(splitRight a d:ℝ))/(b*n/d:ℕ) =
      (splitLeft a d:ℝ)*q.M₁/(b*n:ℕ) := by
    rw [Nat.cast_div_charZero hdw]
    exact divisor_completion_factor hdr he₂ hwpr hprod
  have he := Estermann.original_gcd_inner_bound (hw.smooth 1) (hw.smooth 4) a (b*n) hwp hd hdw
    hM₁ hN₂ (by linarith : 1 ≤ 4*K) hs.1 hs.2.1
    (fun j y => hw.derivatives j 1 y) (fun j y => hw.derivatives j 4 y) k
  simpa only [heq,completionProfileConstant] using he

end
end DivisorProof

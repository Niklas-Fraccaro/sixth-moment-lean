import SixthMoment.Arithmetic.Watt.FiniteSums
import SixthMoment.Arithmetic.Watt.GammaProfiles


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def coprimeTerm (g : ℝ → ℂ) (c : ℕ) (k : ℤ) (m : ℕ) : ℂ :=
  if m.Coprime c then g m*ePhase ((k : ℝ)*inverseRepresentative m c/(c : ℝ)) else 0

theorem weight_zero_of_nonpos {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V) {x : ℝ} (hx : x ≤ 0) :
    g x = 0 := by
  by_contra hn
  have h := hs (subset_tsupport _ hn)
  linarith [h.1]

theorem coprimeTerm_support {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V) (c : ℕ) (k : ℤ) :
    Function.support (coprimeTerm g c k) ⊆ (positiveRange V : Set ℕ) := by
  intro m hm
  have hg : g m ≠ 0 := by
    intro hz
    exact hm (by simp [coprimeTerm,hz])
  have hb := hs (subset_tsupport _ hg)
  apply Finset.mem_Icc.mpr
  refine ⟨?_,(Nat.le_floor_iff hV.le).mpr hb.2⟩
  by_contra hn
  have hm₀ : m = 0 := by omega
  simp only [hm₀,Nat.cast_zero] at hb
  linarith [hb.1]

theorem coprimeTerm_summable {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V) (c : ℕ) (k : ℤ) :
    Summable (coprimeTerm g c k) :=
  summable_of_hasFiniteSupport ((positiveRange V).finite_toSet.subset
    (coprimeTerm_support hs hV c k))

theorem lattice_nonnegative {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V)
    {c : ℕ} (hc : 0 < c) {a : ℕ} (ha : a < c) :
    (∑' j : ℤ, g ((a : ℝ)+(c : ℝ)*j)) =
      ∑' j : ℕ, g ((a : ℝ)+(c : ℝ)*j) := by
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := Int.ofNat_injective
  have hsupport : Function.support (fun j : ℤ => g ((a : ℝ)+(c : ℝ)*j)) ⊆
      Set.range (fun j : ℕ => (j : ℤ)) := by
    intro j hj
    have hjp : 0 ≤ j := by
      by_contra hn
      have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      have hc' : (0 : ℝ) < c := by exact_mod_cast hc
      have ha' : (a : ℝ) < c := by exact_mod_cast ha
      exact hj (weight_zero_of_nonpos hs hV (by nlinarith))
    exact ⟨j.toNat,Int.toNat_of_nonneg hjp⟩
  rw [← hinj.tsum_eq hsupport]
  simp only [Int.cast_natCast]

theorem completedSum_eq_natural_tsum {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedSum g c k = ∑' m : ℕ, coprimeTerm g c k m := by
  have : NeZero c := ⟨hc.ne'⟩
  have hsumm := coprimeTerm_summable hs hV c k
  let e := Nat.residueClassesEquiv c
  have hprod : Summable (fun z : ZMod c × ℕ => coprimeTerm g c k (e.symm z)) :=
    hsumm.comp_injective e.symm.injective
  have heq (z : ZMod c) (j : ℕ) :
      coprimeTerm g c k (e.symm (z,j)) =
        if z.val.Coprime c then
          ePhase ((k : ℝ)*inverseRepresentative z.val c/(c : ℝ))*
            g ((z.val : ℝ)+(c : ℝ)*j) else 0 := by
    change coprimeTerm g c k (z.val+c*j) = _
    unfold coprimeTerm
    simp only [Nat.coprime_add_mul_left_left,inverseRepresentative_add_modulus]
    split_ifs
    · push_cast
      ring
    · rfl
  symm
  calc _ = ∑' z : ZMod c × ℕ, coprimeTerm g c k (e.symm z) :=
      (e.symm.tsum_eq _).symm
    _ = ∑' z : ZMod c, ∑' j : ℕ, coprimeTerm g c k (e.symm (z,j)) := hprod.tsum_prod
    _ = ∑ z : ZMod c, if z.val.Coprime c then
        ePhase ((k : ℝ)*inverseRepresentative z.val c/(c : ℝ))*
          ∑' j : ℤ, g ((z.val : ℝ)+(c : ℝ)*j) else 0 := by
      rw [tsum_fintype]
      apply sum_congr rfl
      intro z _
      simp_rw [heq]
      by_cases hz : z.val.Coprime c
      · simp only [ite_eq_left hz,tsum_mul_left]
        exact (congrArg (fun w : ℂ =>
          ePhase ((k : ℝ)*inverseRepresentative z.val c/(c : ℝ))*w)
          (lattice_nonnegative hs hV hc (ZMod.val_lt z))).symm
      · simp [hz]
    _ = ∑ a ∈ range c, if a.Coprime c then
        ePhase ((k : ℝ)*inverseRepresentative a c/(c : ℝ))*
          ∑' j : ℤ, g ((a : ℝ)+(c : ℝ)*j) else 0 :=
      zmod_sum_vals (c := c) (fun a : ℕ => if a.Coprime c then
        ePhase ((k : ℝ)*inverseRepresentative a c/(c : ℝ))*
          ∑' j : ℤ, g ((a : ℝ)+(c : ℝ)*j) else 0)
    _ = _ := by rw [completedSum,Finset.sum_filter]

theorem completedSum_eq_finite_sum {g : ℝ → ℂ} {V : ℝ}
    (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedSum g c k = ∑ m ∈ positiveRange V, coprimeTerm g c k m := by
  rw [completedSum_eq_natural_tsum hs hV hc]
  apply tsum_eq_sum
  intro m hm
  by_contra hn
  exact hm (coprimeTerm_support hs hV c k hn)

theorem finite_sum_eq_fourier {g : ℝ → ℂ} {V : ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V)
    {c : ℕ} (hc : 0 < c) (k : ℤ) :
    (∑ m ∈ positiveRange V, coprimeTerm g c k m) =
      ∑' l : ℤ, fourierCoefficient g c l*classicalKloostermanSum k (-l) c := by
  rw [← completedSum_eq_finite_sum hs hV hc]
  exact completedSum_eq_classical hg
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hs) hc k

theorem finite_product_inverse_eq_fourier {g : ℝ → ℂ} {V : ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (V/2) V) (hV : 0 < V)
    {r c : ℕ} (hc : 0 < c) (k : ℤ) :
    (∑ v ∈ positiveRange V, if (r*v).Coprime c then
      g v*ePhase ((k : ℝ)*inverseRepresentative (r*v) c/(c : ℝ)) else 0) =
      if r.Coprime c then ∑' l : ℤ, fourierCoefficient g c l*
        classicalKloostermanSum (k*inverseRepresentative r c) (-l) c else 0 := by
  by_cases hr : r.Coprime c
  · rw [ite_eq_left hr,← finite_sum_eq_fourier hg hs hV hc]
    apply sum_congr rfl
    intro v _
    unfold coprimeTerm
    by_cases hv : v.Coprime c
    · rw [ite_eq_left (hr.mul_left hv),ite_eq_left hv,inverse_product_phase hc hr hv]
      push_cast
      rfl
    · have hrv : ¬ (r*v).Coprime c := fun h => hv h.coprime_mul_left
      rw [ite_eq_right hrv,ite_eq_right hv]
  · rw [ite_eq_right hr]
    apply sum_eq_zero
    intro v _
    exact ite_eq_right (fun h => hr h.coprime_mul_right)

def phaseSign (positive : Bool) : ℤ := if positive then 1 else -1

def completedTerm (_p : WattScales) (γ : ℕ → ℕ → ℝ → ℝ → ℂ)
    (positive : Bool) (h k r s t : ℕ) (l : ℤ) : ℂ :=
  fourierCoefficient (fun v => γ r s v t) (s*t) l*
    classicalKloostermanSum
      (phaseSign positive*(h : ℤ)*k*inverseRepresentative r (s*t)) (-l) (s*t)

theorem gamma_finite_completion {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) (h k r : ℕ) {s t : ℕ}
    (hs : 0 < s) (ht : 0 < t) :
    (∑ v ∈ positiveRange p.V, if (r*v).Coprime (s*t) then
      γ r s v t*ePhase ((if positive then (1 : ℝ) else -1)*(h : ℝ)*k*
        (inverseRepresentative (r*v) (s*t) : ℝ)/(s*t : ℕ)) else 0) =
      if r.Coprime (s*t) then ∑' l : ℤ, completedTerm p γ positive h k r s t l else 0 := by
  have heq := finite_product_inverse_eq_fourier (gamma_slice_smooth hw r s t)
    (gamma_slice_support hw r s t) hV (Nat.mul_pos hs ht) (phaseSign positive*(h : ℤ)*k)
    (r := r)
  simpa only [completedTerm,phaseSign,Int.cast_mul,Int.cast_natCast,
    Int.cast_ite,Int.cast_one,Int.cast_neg,mul_assoc] using heq

theorem weightedWattSum_eq_fourier_sums {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C,
      ∑ r ∈ positiveRange p.R, ∑ s ∈ positiveRange p.S,
      ∑ t ∈ positiveRange p.P, u₀ h*u₁ k*a r*bc s*
        (if r.Coprime (s*t) then ∑' l : ℤ, completedTerm p γ positive h k r s t l else 0) := by
  rw [weightedWattSum_eq_six_sums]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s hs
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  have hsp : 0 < s := (Finset.mem_Icc.mp hs).1
  have htp : 0 < t := (Finset.mem_Icc.mp ht).1
  rw [← gamma_finite_completion hw hV positive h k r hsp htp,mul_sum]
  apply sum_congr rfl
  intro v _
  split_ifs <;> ring

theorem classicalKloostermanSum_trivial (m n : ℤ) (c : ℕ) :
    ‖classicalKloostermanSum m n c‖ ≤ c := by
  unfold classicalKloostermanSum kloostermanSum
  apply (norm_sum_le _ _).trans
  simp only [norm_ePhase,sum_const,nsmul_eq_mul,mul_one]
  exact_mod_cast (card_filter_le (range c) (fun d => d.Coprime c)).trans_eq (card_range c)

theorem completedTerm_summable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) (h k r : ℕ) {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    Summable (completedTerm p γ positive h k r s t) := by
  have hc := Nat.mul_pos hs ht
  have hcoeff := fourierCoefficient_norm_summable (gamma_slice_smooth hw r s t)
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (gamma_slice_support hw r s t)) hc
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hcoeff.mul_right ((s*t : ℕ) : ℝ))
  intro l
  rw [completedTerm,norm_mul]
  exact mul_le_mul_of_nonneg_left (classicalKloostermanSum_trivial _ (-l) (s*t))
    (norm_nonneg _)

end
end Watt41
end DivisorProof

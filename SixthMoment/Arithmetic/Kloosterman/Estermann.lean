import Salt.Weil.EstermannGlobal
import SixthMoment.Arithmetic.Kloosterman.Definitions
import SixthMoment.Arithmetic.Kloosterman.TwoAdicMean

namespace DivisorProof
open Finset
open scoped BigOperators
noncomputable section

theorem stdAddChar_integer_phase {c : ℕ} [NeZero c] (u : ℤ) :
    ZMod.stdAddChar (u : ZMod c) = ePhase ((u : ℝ)/(c : ℝ)) := by
  rw [ZMod.stdAddChar_coe]
  unfold ePhase
  congr 1
  push_cast
  ring

theorem kloostermanSum_eq_salt {c : ℕ} (hc : 0 < c) (u v : ℤ) :
    kloostermanSum c u v = @Salt.Weil.kloosterman c ⟨hc.ne'⟩ (u : ZMod c) (v : ZMod c) := by
  let : NeZero c := ⟨hc.ne'⟩
  symm
  unfold Salt.Weil.kloosterman kloostermanSum
  apply Finset.sum_bij (fun (t : (ZMod c)ˣ) _ => (t : ZMod c).val)
  · intro t _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime t⟩
  · intro t _ s _ heq
    exact Units.ext (ZMod.val_injective c heq)
  · intro x hx
    obtain ⟨hx,hcop⟩ := mem_filter.mp hx
    refine ⟨ZMod.unitOfCoprime x hcop, mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (mem_range.mp hx)
  · intro t _
    have hinv : ((inverseRepresentative (t : ZMod c).val c : ℕ) : ZMod c) =
        ((t⁻¹ : (ZMod c)ˣ) : ZMod c) := by
      simp only [inverseRepresentative, ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
    have heq : (u : ZMod c)*(t : ZMod c)+(v : ZMod c)*((t⁻¹ : (ZMod c)ˣ) : ZMod c) =
        ((u*((t : ZMod c).val : ℤ)+v*(inverseRepresentative (t : ZMod c).val c : ℤ) : ℤ) : ZMod c) := by
      push_cast
      rw [ZMod.natCast_zmod_val, hinv]
    rw [heq, stdAddChar_integer_phase]
    congr 1
    push_cast
    rfl

theorem gcd_zmod_intCast_val {c : ℕ} [NeZero c] (u : ℤ) :
    Nat.gcd ((u : ZMod c).val) c = Nat.gcd u.natAbs c := by
  have hh := Int.gcd_emod u (c : ℤ)
  rw [← ZMod.val_intCast u] at hh
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hh

theorem gcd_zmod_parameters {c : ℕ} [NeZero c] (u v : ℤ) :
    Nat.gcd c (Nat.gcd (u : ZMod c).val (v : ZMod c).val) =
      Nat.gcd (Nat.gcd u.natAbs v.natAbs) c := by
  rw [Nat.gcd_comm c, ← Nat.gcd_gcd_gcd_right, gcd_zmod_intCast_val,
    gcd_zmod_intCast_val, Nat.gcd_gcd_gcd_right]

theorem kloostermanSum_estermann {c : ℕ} (hc : 0 < c) (u v : ℤ) :
    ‖kloostermanSum c u v‖ ≤ twoAdicWeight c*(c.divisors.card:ℝ)*(c:ℝ)^(1/2:ℝ)*
      (Nat.gcd (Nat.gcd u.natAbs v.natAbs) c:ℝ)^(1/2:ℝ) := by
  let : NeZero c := ⟨hc.ne'⟩
  rw [kloostermanSum_eq_salt hc]
  simpa only [twoAdicWeight, gcd_zmod_parameters, Real.sqrt_eq_rpow] using
    Salt.Weil.norm_kloosterman_estermann (u : ZMod c) (v : ZMod c)

end
end DivisorProof

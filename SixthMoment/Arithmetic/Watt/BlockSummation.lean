import SixthMoment.Arithmetic.Watt.GlobalMajorants
import SixthMoment.Arithmetic.Watt.Reassembly

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

theorem mass_identity {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) :
    p.V*Real.sqrt p.R*Real.sqrt p.H*Real.sqrt p.C*Real.sqrt (p.S*p.P/p.V) = p.H*p.C*p.X := by
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  apply (sq_eq_sq₀ (by positivity) (by positivity [X_nonneg p])).mp
  simp only [mul_pow,Real.sq_sqrt hR.le,Real.sq_sqrt hH.le,Real.sq_sqrt hC.le,
    Real.sq_sqrt (div_pos (mul_pos hS hP) hV).le,X_sq_eq hp]
  unfold WattScales.product
  field_simp

theorem sqrt_dualLength_le {p : WattScales} {E : ℝ}
    (hS : 0 < p.S) (hP : 0 < p.P) (hV : 0 < p.V) (hE : 1 ≤ E) :
    Real.sqrt (dualLength p E) ≤ E*Real.sqrt (p.S*p.P/p.V) := by
  unfold dualLength
  rw [Real.sqrt_mul (by positivity : 0 ≤ p.S*p.P/p.V)]
  have he := Real.sqrt_le_self_iff.mpr (Or.inr hE)
  nlinarith [mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (p.S*p.P/p.V))]

theorem blockEnvelope_nonneg {p : WattScales} {Δ E η : ℝ}
    (hp : ∀ n, 1 ≤ p.size n) (hΔ : 0 < Δ) (hE : 1 ≤ E) : 0 ≤ blockEnvelope p Δ E η := by
  have hR : 0 ≤ p.R := zero_le_one.trans (hp 2)
  have hP : 0 ≤ p.P := zero_le_one.trans (hp 5)
  have hshape : 0 ≤ shape p := zero_le_one.trans (shape_ge_one hp)
  have hM : 0 ≤ totalSize p := zero_le_one.trans (totalSize_ge_one hp)
  unfold blockEnvelope
  positivity

theorem envelope_mass_le {p : WattScales} {Δ E η : ℝ}
    (hp : ∀ n, 1 ≤ p.size n) (hΔ : 0 < Δ) (hE : 1 ≤ E) :
    (4*p.V/(p.S*p.P))*blockEnvelope p Δ E η*(8*Real.sqrt p.H)*(8*Real.sqrt p.C)*
      (8*Real.sqrt (dualLength p E)) ≤ 2048*core p Δ*E^6*(totalSize p)^(2*η) := by
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hM : 0 < totalSize p := lt_of_lt_of_le zero_lt_one (totalSize_ge_one hp)
  have hG := blockEnvelope_nonneg hp hΔ hE (η := η)
  have hshape : 0 ≤ shape p := zero_le_one.trans (shape_ge_one hp)
  calc
    _ ≤ (4*p.V/(p.S*p.P))*blockEnvelope p Δ E η*(8*Real.sqrt p.H)*(8*Real.sqrt p.C)*
        (8*(E*Real.sqrt (p.S*p.P/p.V))) := by
      gcongr
      exact sqrt_dualLength_le hS hP hV hE
    _ = 2048*Δ^(-7/2 : ℝ)*p.R*p.S*
        (p.V*Real.sqrt p.R*Real.sqrt p.H*Real.sqrt p.C*Real.sqrt (p.S*p.P/p.V))*
          E^6*(totalSize p)^(2*η)*shape p := by
      unfold blockEnvelope
      field_simp [hS.ne',hP.ne']
      ring
    _ = 2048*(Δ^(-7/2 : ℝ)*p.H*p.C*p.R*(p.S*p.X)*shape p)*E^6*(totalSize p)^(2*η) := by
      rw [mass_identity hp]
      ring
    _ ≤ _ := by
      unfold core
      gcongr
      exact le_add_of_nonneg_left hV.le

theorem sum_block_majorants_le {p : WattScales} {Δ E η : ℝ}
    (hp : ∀ n, 1 ≤ p.size n) (hΔ : 0 < Δ) (hE : 1 ≤ E) (hη : 0 ≤ η)
    {NH NK NA : ℕ} (hfH : 1 ≤ blockScale p.H NH) (hfK : 1 ≤ blockScale p.C NK)
    (hfA : 1 ≤ blockScale (dualLength p E) NA) :
    (∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ n ∈ range (NA+1),
      majorant (blockScales p (dualLength p E) i j n) (Δ/E) η*
        (4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P))) ≤
      2048*core p Δ*E^6*(totalSize p)^(2*η) := by
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hK : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hA := dualLength_pos hS hP hV hEp
  have hG := blockEnvelope_nonneg hp hΔ hE (η := η)
  have hw₀ : 0 ≤ 4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P) := by
    have he : 4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P) = 7*p.V/(2*p.S*p.P) := by ring
    rw [he]
    positivity
  have hw : 4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P) ≤ 4*p.V/(p.S*p.P) :=
    sub_le_self _ (by positivity)
  calc
    _ ≤ ∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ n ∈ range (NA+1),
        (4*p.V/(p.S*p.P))*blockEnvelope p Δ E η*Real.sqrt (blockScale p.H i)*
          Real.sqrt (blockScale p.C j)*Real.sqrt (blockScale (dualLength p E) n) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro n hn
      have hb := block_majorant_le hp hΔ hE hη
        (blockScale_ge_final hH.le hfH hi) (blockScale_ge_final hK.le hfK hj)
        (blockScale_ge_final hA.le hfA hn)
      have hineq := mul_le_mul hb hw hw₀ (by positivity)
      exact hineq.trans_eq (by ring)
    _ = (4*p.V/(p.S*p.P))*blockEnvelope p Δ E η*
        (∑ i ∈ range (NH+1), Real.sqrt (blockScale p.H i))*
        (∑ j ∈ range (NK+1), Real.sqrt (blockScale p.C j))*
        (∑ n ∈ range (NA+1), Real.sqrt (blockScale (dualLength p E) n)) := by
      simp only [mul_assoc,← mul_sum,← sum_mul]
    _ ≤ (4*p.V/(p.S*p.P))*blockEnvelope p Δ E η*(8*Real.sqrt p.H)*(8*Real.sqrt p.C)*
        (8*Real.sqrt (dualLength p E)) := by
      gcongr
      · exact sum_blockScale_sqrt_le hH.le (NH+1)
      · exact sum_blockScale_sqrt_le hK.le (NK+1)
      · exact sum_blockScale_sqrt_le hA.le (NA+1)
    _ ≤ _ := envelope_mass_le hp hΔ hE

end
end Watt41
end DivisorProof

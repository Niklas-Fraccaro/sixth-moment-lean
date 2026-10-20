import SixthMoment.Arithmetic.Watt.FrequencyBounds
import SixthMoment.Arithmetic.Watt.Majorants

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

def totalSize (p : WattScales) : ℝ := p.H*p.C*p.product

def shape (p : WattScales) : ℝ :=
  (1+p.H*p.C/(p.R*p.S))^(1/2 : ℝ)*(1+p.P/(p.R*p.V))^(1/2 : ℝ)*
    (1+p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V))^(1/4 : ℝ)

def core (p : WattScales) (Δ : ℝ) : ℝ :=
  Δ^(-7/2 : ℝ)*p.H*p.C*p.R*(p.V+p.S*p.X)*shape p

theorem wattMajorant_eq_core (p : WattScales) (Δ η : ℝ) :
    wattMajorant p Δ η = core p Δ*(totalSize p)^(20*η) := by
  unfold wattMajorant core shape totalSize WattScales.product
  have he : p.H*p.C*p.R*p.S*p.V*p.P = p.H*p.C*(p.R*p.S*p.V*p.P) := by ring
  rw [he]
  ring

theorem product_ge_one {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) : 1 ≤ p.product := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hp 2) (hp 3)) (hp 4)) (hp 5)

theorem totalSize_ge_one {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) : 1 ≤ totalSize p :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (hp 0) (hp 1)) (product_ge_one hp)

theorem product_le_totalSize {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) : p.product ≤ totalSize p := by
  have hHC : 1 ≤ p.H*p.C := one_le_mul_of_one_le_of_one_le (hp 0) (hp 1)
  unfold totalSize
  exact le_mul_of_one_le_left (by linarith [product_ge_one hp]) hHC

theorem X_sq_eq {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) :
    p.X^2 = p.product/(p.H*p.C) := by
  unfold WattScales.X
  apply Real.sq_sqrt
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  exact div_nonneg (by linarith [product_ge_one hp]) (mul_pos hH hC).le

theorem X_nonneg (p : WattScales) : 0 ≤ p.X := Real.sqrt_nonneg _

theorem shape_ge_one {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) : 1 ≤ shape p := by
  have hH : 0 ≤ p.H := zero_le_one.trans (hp 0)
  have hC : 0 ≤ p.C := zero_le_one.trans (hp 1)
  have hR : 0 ≤ p.R := zero_le_one.trans (hp 2)
  have hS : 0 ≤ p.S := zero_le_one.trans (hp 3)
  have hV : 0 ≤ p.V := zero_le_one.trans (hp 4)
  have hP : 0 ≤ p.P := zero_le_one.trans (hp 5)
  unfold shape
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) (by norm_num)
    · exact Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) (by norm_num)
  · exact Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) (by norm_num)

theorem core_ge_HCRV {p : WattScales} (hp : ∀ n, 1 ≤ p.size n)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1) : p.H*p.C*p.R*p.V ≤ core p Δ := by
  have hH : 0 ≤ p.H := zero_le_one.trans (hp 0)
  have hC : 0 ≤ p.C := zero_le_one.trans (hp 1)
  have hR : 0 ≤ p.R := zero_le_one.trans (hp 2)
  have hS : 0 ≤ p.S := zero_le_one.trans (hp 3)
  have hV : 0 ≤ p.V := zero_le_one.trans (hp 4)
  have hδ : 1 ≤ Δ^(-7/2 : ℝ) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos hΔ hΔ₁ (by norm_num : (-7/2 : ℝ) ≤ 0)
  have hX := X_nonneg p
  have hδ₀ : 0 ≤ Δ^(-7/2 : ℝ) := zero_le_one.trans hδ
  have hB : 0 ≤ p.H*p.C*p.R := by positivity
  have hx : p.V ≤ p.V+p.S*p.X := le_add_of_nonneg_right (mul_nonneg hS (X_nonneg p))
  unfold core
  calc
    _ ≤ Δ^(-7/2 : ℝ)*(p.H*p.C*p.R*p.V) := le_mul_of_one_le_left (by positivity) hδ
    _ ≤ Δ^(-7/2 : ℝ)*(p.H*p.C*p.R*(p.V+p.S*p.X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hB) hδ₀
    _ = Δ^(-7/2 : ℝ)*p.H*p.C*p.R*(p.V+p.S*p.X) := by ring
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (shape_ge_one hp)

theorem sqrt_prefactor (H K L R S P : ℝ) (hH : 0 < H) (hK : 0 < K) (hL : 0 < L)
    (hR : 0 ≤ R) :
    H*K*L*((R*S)*(Real.sqrt (R/(H*K*L))*S*P)) =
      R*S^2*P*Real.sqrt R*Real.sqrt H*Real.sqrt K*Real.sqrt L := by
  have hden : 0 < H*K*L := by positivity
  have hd : H*K*L*Real.sqrt (R/(H*K*L)) = Real.sqrt R*Real.sqrt (H*K*L) := by
    rw [Real.sqrt_div hR]
    field_simp [(Real.sqrt_pos.mpr hden).ne']
    linear_combination -(Real.sqrt R)*(Real.sq_sqrt hden.le)
  calc
    _ = R*S^2*P*(H*K*L*Real.sqrt (R/(H*K*L))) := by ring
    _ = _ := by rw [hd,Real.sqrt_mul (mul_pos hH hK).le,Real.sqrt_mul hH.le]; ring

theorem block_QX_le_product_sq {p : WattScales} {A : ℝ} {i j k : ℕ}
    (hp : ∀ n, 1 ≤ p.size n) (hi : 1 ≤ blockScale p.H i)
    (hj : 1 ≤ blockScale p.C j) (hk : 1 ≤ blockScale A k) :
    (blockScales p A i j k).Q*(blockScales p A i j k).X ≤ p.product^2 := by
  let p' : WattScales := ⟨blockScale p.H i,blockScale p.C j,p.R,p.S,p.V,p.P⟩
  exact Scales.QX_le_product_sq hi hj (hp 2) (hp 3) (hp 4) (hp 5) hk (p := p')

theorem last_ratio_eq {q : Scales} (hH : 0 < q.H) (hK : 0 < q.K) (hL : 0 < q.L)
    (hR : 0 < q.R) (hS : 0 < q.S) :
    q.H^2*q.K*q.L*q.X^2/q.Q^4 = q.H*q.P^2/(q.R^3*q.S^2) := by
  rw [Scales.X_sq hH hK hL hR.le]
  unfold Scales.Q
  field_simp [hH.ne',hK.ne',hL.ne',hR.ne',hS.ne']

theorem original_last_ratio_eq {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) :
    p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V) = p.H*p.P^2/(p.R^3*p.S^2) := by
  rw [X_sq_eq hp]
  unfold WattScales.product
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  field_simp [hH.ne',hC.ne',hR.ne',hS.ne',hV.ne']


theorem block_shape_le {p : WattScales} {E : ℝ} (hp : ∀ n, 1 ≤ p.size n) (hE : 1 ≤ E)
    (i j k : ℕ) :
    let q := blockScales p (dualLength p E) i j k
    ((1+q.H*q.K/q.Q)*(1+q.L/q.Q))^(1/2 : ℝ)*
      (1+q.H^2*q.K*q.L*q.X^2/q.Q^4)^(1/4 : ℝ) ≤ E*shape p := by
  dsimp only
  let q := blockScales p (dualLength p E) i j k
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hA := dualLength_pos hS hP hV hEp
  have hqH : 0 < q.H := blockScale_pos hH i
  have hqK : 0 < q.K := blockScale_pos hC j
  have hqL : 0 < q.L := blockScale_pos hA k
  have hqQ : 0 < q.Q := mul_pos hR hS
  have h₁ : 1+q.H*q.K/q.Q ≤ 1+p.H*p.C/(p.R*p.S) := by
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ hqQ.le
    exact mul_le_mul (blockScale_le hH.le i) (blockScale_le hC.le j) hqK.le hH.le
  have hAq : dualLength p E/(p.R*p.S) = E*(p.P/(p.R*p.V)) := by
    unfold dualLength
    field_simp
  have h₂ : 1+q.L/q.Q ≤ E*(1+p.P/(p.R*p.V)) := by
    have hl := div_le_div_of_nonneg_right (blockScale_le hA.le k) hqQ.le
    change q.L/q.Q ≤ dualLength p E/(p.R*p.S) at hl
    rw [hAq] at hl
    nlinarith
  have hlast : 1+q.H^2*q.K*q.L*q.X^2/q.Q^4 ≤
      1+p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V) := by
    rw [last_ratio_eq hqH hqK hqL hR hS,original_last_ratio_eq hp]
    apply add_le_add le_rfl
    change (blockScale p.H i)*p.P^2/(p.R^3*p.S^2) ≤ p.H*p.P^2/(p.R^3*p.S^2)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (blockScale_le hH.le i) (sq_nonneg p.P)) (by positivity)
  have h₁' : (1+q.H*q.K/q.Q)^(1/2 : ℝ) ≤ (1+p.H*p.C/(p.R*p.S))^(1/2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h₁ (by norm_num)
  have h₂' : (1+q.L/q.Q)^(1/2 : ℝ) ≤ E*(1+p.P/(p.R*p.V))^(1/2 : ℝ) := by
    calc
      _ ≤ (E*(1+p.P/(p.R*p.V)))^(1/2 : ℝ) := Real.rpow_le_rpow (by positivity) h₂ (by norm_num)
      _ = E^(1/2 : ℝ)*(1+p.P/(p.R*p.V))^(1/2 : ℝ) := Real.mul_rpow hEp.le (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hE (by norm_num : (1/2 : ℝ) ≤ 1))
        (by positivity)
  have h₃' : (1+q.H^2*q.K*q.L*q.X^2/q.Q^4)^(1/4 : ℝ) ≤
      (1+p.H^2*p.C*p.P*p.X^2/(p.R^4*p.S^3*p.V))^(1/4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hlast (by norm_num)
  rw [Real.mul_rpow (by positivity : 0 ≤ 1+q.H*q.K/q.Q) (by positivity : 0 ≤ 1+q.L/q.Q)]
  have hprod := mul_le_mul
    (mul_le_mul h₁' h₂' (by positivity) (by positivity)) h₃' (by positivity) (by positivity)
  exact hprod.trans_eq (by unfold shape; ring)

def blockEnvelope (p : WattScales) (Δ E η : ℝ) : ℝ :=
  Δ^(-7/2 : ℝ)*p.R*p.S^2*p.P*Real.sqrt p.R*E^5*(totalSize p)^(2*η)*shape p

theorem block_majorant_le {p : WattScales} {Δ E η : ℝ}
    (hp : ∀ n, 1 ≤ p.size n) (hΔ : 0 < Δ) (hE : 1 ≤ E) (hη : 0 ≤ η)
    {i j k : ℕ} (hi : 1 ≤ blockScale p.H i) (hj : 1 ≤ blockScale p.C j)
    (hk : 1 ≤ blockScale (dualLength p E) k) :
    majorant (blockScales p (dualLength p E) i j k) (Δ/E) η ≤
      blockEnvelope p Δ E η*Real.sqrt (blockScale p.H i)*Real.sqrt (blockScale p.C j)*
        Real.sqrt (blockScale (dualLength p E) k) := by
  let q := blockScales p (dualLength p E) i j k
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hqH : 0 < q.H := by exact lt_of_lt_of_le zero_lt_one hi
  have hqK : 0 < q.K := by exact lt_of_lt_of_le zero_lt_one hj
  have hqL : 0 < q.L := by exact lt_of_lt_of_le zero_lt_one hk
  have hqQ : 0 < q.Q := mul_pos hR hS
  have hqX : 0 < q.X := by unfold Scales.X; positivity
  have hZ : 0 < q.Q*q.X := mul_pos hqQ hqX
  have hM : 0 < totalSize p := lt_of_lt_of_le zero_lt_one (totalSize_ge_one hp)
  have hδ : (Δ/E)^(-7/2 : ℝ) ≤ Δ^(-7/2 : ℝ)*E^4 := by
    have he : (Δ/E)^(-7/2 : ℝ) = Δ^(-7/2 : ℝ)*E^(7/2 : ℝ) := by
      rw [Real.div_rpow hΔ.le hEp.le,show (-7/2 : ℝ) = -(7/2 : ℝ) by ring,
        Real.rpow_neg hEp.le,div_inv_eq_mul]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ E^(4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
      _ = E^4 := by exact_mod_cast Real.rpow_natCast E 4
  have hpow : (q.Q*q.X)^η ≤ (totalSize p)^(2*η) := by
    have hle : q.Q*q.X ≤ (totalSize p)^2 :=
      (block_QX_le_product_sq hp hi hj hk).trans
        (pow_le_pow_left₀ (by linarith [product_ge_one hp]) (product_le_totalSize hp) 2)
    have hh := Real.rpow_le_rpow hZ.le hle hη
    simpa only [← Real.rpow_natCast_mul hM.le, Nat.cast_ofNat] using hh
  have hshape := block_shape_le hp hE i j k
  have hpref := sqrt_prefactor q.H q.K q.L p.R p.S p.P hqH hqK hqL hR.le
  change q.H*q.K*q.L*(q.Q*q.X) = _ at hpref
  have heq : majorant q (Δ/E) η = (Δ/E)^(-7/2 : ℝ)*(q.H*q.K*q.L*(q.Q*q.X))*
      (q.Q*q.X)^η*(((1+q.H*q.K/q.Q)*(1+q.L/q.Q))^(1/2 : ℝ)*
        (1+q.H^2*q.K*q.L*q.X^2/q.Q^4)^(1/4 : ℝ)) := by
    unfold majorant
    rw [Real.rpow_add hZ,Real.rpow_one]
    ring
  rw [heq]
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_right hδ (by positivity : 0 ≤ q.H*q.K*q.L*(q.Q*q.X)))
      hpow (by positivity) (by positivity)) hshape (by positivity) (by positivity)
  apply hprod.trans_eq
  rw [hpref]
  change _ = blockEnvelope p Δ E η*Real.sqrt q.H*Real.sqrt q.K*Real.sqrt q.L
  unfold blockEnvelope
  rw [pow_succ E 4]
  ring

end
end Watt41
end DivisorProof

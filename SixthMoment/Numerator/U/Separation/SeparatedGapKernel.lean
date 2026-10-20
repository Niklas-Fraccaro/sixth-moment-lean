import SixthMoment.Numerator.U.Separation.BinomialPhase
import SixthMoment.Numerator.U.Separation.FiveProductWeights

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phaseQuadScale (q : QuadraticScales) : Fin 4 → ℝ := ![q.M₁,q.M₂,q.N₁,q.N₂]
def phaseQuadVariable (n : Fin 7 → ℕ) : Fin 4 → ℝ := ![n 2,n 3,n 4,n 5]

def phaseBaseSmoothFactor (q : QuadraticScales) (α : MomentShifts) (z : ℂ)
    (n : Fin 7 → ℕ) : ℂ :=
  (rectangularSmoothBlockWeight ((n 6:ℝ)/q.H):ℂ)*
    ∏ j : Fin 4, rectangularActualMellinBlockWeight α z j (phaseQuadVariable n j/phaseQuadScale q j)

def phaseAdjustedBeta (q : QuadraticScales) (β : ℕ → ℂ) (k : ℕ) (b : ℕ) : ℂ :=
  β b*(((b:ℝ)/q.B):ℂ)^(-(k:ℂ))

def phaseSeparationScalar (q : QuadraticScales) (sign t : ℝ) (k : ℕ) : ℂ :=
  phaseBinomialCoefficient (-(t:ℂ)*I) k*((sign*2*q.H/(q.B*q.N₁*q.N₂):ℝ):ℂ)^k

private theorem weight_sub_nat {x : ℝ} (hx : 0<x) (s : ℂ) (k : ℕ) :
    rectangularMellinBlockWeight (s-(k:ℂ)) x=
      rectangularMellinBlockWeight s x*(x:ℂ)^(-(k:ℂ)) := by
  unfold rectangularMellinBlockWeight
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),Complex.cpow_neg]
  ring

private theorem scale_power_identity {B H N₁ N₂ b h n₁ n₂ : ℝ}
    (hB : 0<B) (hH : 0<H) (hN₁ : 0<N₁) (hN₂ : 0<N₂)
    (hb : 0<b) (hn₁ : 0<n₁) (hn₂ : 0<n₂) (sign : ℝ) (k : ℕ) :
    ((sign*2*H/(B*N₁*N₂):ℝ):ℂ)^k*(((b/B:ℝ):ℂ)^(-(k:ℂ)))*
      ((h/H/2:ℝ):ℂ)^k*(((n₁/N₁:ℝ):ℂ)^(-(k:ℂ)))*(((n₂/N₂:ℝ):ℂ)^(-(k:ℂ)))=
        ((sign*h/(b*n₁*n₂):ℝ):ℂ)^k := by
  simp only [Complex.cpow_neg,Complex.cpow_natCast,← inv_pow,← mul_pow]
  congr 1
  have hr : (sign*2*H/(B*N₁*N₂))*(b/B)⁻¹*(h/H/2)*(n₁/N₁)⁻¹*(n₂/N₂)⁻¹=
      sign*h/(b*n₁*n₂) := by
    field_simp [hB.ne',hH.ne',hN₁.ne',hN₂.ne',hb.ne',hn₁.ne',hn₂.ne']
  exact_mod_cast hr

theorem phase_five_product_summand_identity (q : QuadraticScales)
    (hB : 0<q.B) (hH : 0<q.H) (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ) (sign t : ℝ)
    (n : Fin 7 → ℕ) (hb : 0<n 1) (hn₁ : 0<n 4) (hn₂ : 0<n 5) (k : ℕ) :
    phaseSeparationScalar q sign t k*(A (n 0)*phaseAdjustedBeta q β k (n 1)*
      ∏ i : Fin 5, phaseFiveWeights α z k i (rectangularWeightArguments q n i))=
      (A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
        (phaseBinomialCoefficient (-(t:ℂ)*I) k*((sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ)^k) := by
  have hp := scale_power_identity (b := (n 1:ℝ)) (h := (n 6:ℝ))
    (n₁ := (n 4:ℝ)) (n₂ := (n 5:ℝ)) hB hH hN₁ hN₂
    (by exact_mod_cast hb) (by exact_mod_cast hn₁) (by exact_mod_cast hn₂) sign k
  push_cast at hp
  have hs₁ : 0<(n 4:ℝ)/q.N₁ := div_pos (by exact_mod_cast hn₁) hN₁
  have hs₂ : 0<(n 5:ℝ)/q.N₂ := div_pos (by exact_mod_cast hn₂) hN₂
  unfold phaseSeparationScalar phaseAdjustedBeta phaseBaseSmoothFactor
  rw [Fin.prod_univ_five,Fin.prod_univ_four]
  dsimp only [phaseFiveWeights,rectangularWeightArguments,phaseQuadScale,phaseQuadVariable]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  rw [phaseGapWeight_eq,weight_sub_nat hs₁,weight_sub_nat hs₂]
  unfold rectangularActualMellinBlockWeight
  calc
    _ = (A (n 0)*β (n 1)*
      ((rectangularSmoothBlockWeight ((n 6:ℝ)/q.H):ℂ)*
        rectangularMellinBlockWeight (-(1/2+α 0+z)) ((n 2:ℝ)/q.M₁)*
        rectangularMellinBlockWeight (-(1/2+α 1+z)) ((n 3:ℝ)/q.M₂)*
        rectangularMellinBlockWeight (-(1/2+α 2+z)) ((n 4:ℝ)/q.N₁)*
        rectangularMellinBlockWeight (-(1/2+α 3+z)) ((n 5:ℝ)/q.N₂)))*
      phaseBinomialCoefficient (-(t:ℂ)*I) k*
      ((((sign*2*q.H/(q.B*q.N₁*q.N₂):ℝ):ℂ)^k)*
        (((n 1:ℝ)/q.B):ℂ)^(-(k:ℂ))*(((n 6:ℝ)/q.H/2):ℂ)^k*
        (((n 4:ℝ)/q.N₁):ℂ)^(-(k:ℂ))*(((n 5:ℝ)/q.N₂):ℂ)^(-(k:ℂ))) := by push_cast; ring
    _ = _ := by push_cast; rw [hp]; ring

theorem phase_five_product_summand_hasSum (q : QuadraticScales)
    (hB : 0<q.B) (hH : 0<q.H) (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ) (sign t : ℝ)
    (n : Fin 7 → ℕ) (hb : 0<n 1) (hn₁ : 0<n 4) (hn₂ : 0<n 5)
    (hr : |sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|<1) :
    HasSum (fun k : ℕ => phaseSeparationScalar q sign t k*(A (n 0)*phaseAdjustedBeta q β k (n 1)*
      ∏ i : Fin 5, phaseFiveWeights α z k i (rectangularWeightArguments q n i)))
      ((A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
        (1+((sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ))^(-(t:ℂ)*I)) := by
  have hs := (phaseBinomial_hasSum (-(t:ℂ)*I) ((sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hr)).mul_left
      (A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)
  exact hs.congr_fun (fun k =>
    phase_five_product_summand_identity q hB hH hN₁ hN₂ α z A β sign t n hb hn₁ hn₂ k)

end
end SixthMoment

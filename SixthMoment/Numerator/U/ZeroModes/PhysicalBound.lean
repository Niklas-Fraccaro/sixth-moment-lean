import SixthMoment.Numerator.U.Sources.GlobalMellin
import SixthMoment.Numerator.U.ZeroModes.Mass.Summed

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ZeroModePermutedPhysicalQuad (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) : Fin 4→ℝ :=
  let y := a03ZeroModePhysicalQuad q v x
  ![if m then y 1 else y 0,if m then y 0 else y 1,
    if n then y 3 else y 2,if n then y 2 else y 3]

theorem a03ZeroModePermutedPhysicalQuad_product (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) :
    (∏ i : Fin 4,a03ZeroModePermutedPhysicalQuad m n q v x i)=
      ∏ i : Fin 4,a03ZeroModePhysicalQuad q v x i := by
  cases m <;> cases n <;> simp [a03ZeroModePermutedPhysicalQuad,Fin.prod_univ_four,
    mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroModePermutedPhysicalQuad_normalized (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) (i : Fin 4) :
    a03SixZeroSourceArguments m n q v x i.succ.succ=
      a03ZeroModePermutedPhysicalQuad m n q v x i/
        a03ZeroModeQuadScales (phasePairSwapScales m n q) i := by
  cases m <;> cases n <;> fin_cases i <;>
    simp [a03SixZeroSourceArguments,a03SixZeroPairArguments,a03ZeroModePermutedPhysicalQuad,
      a03ZeroModePhysicalQuad,a03ZeroModeQuadScales,phasePairSwapScales,rectangularZeroArguments,
      div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc]

theorem a03SixZeroSource_mask_norm (m n : Bool) (q : QuadraticScales) (v : Fin 5→ℕ) (x : ℝ) :
    ‖∏ i : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x i.succ):ℂ)‖=
      a03ZeroModeSmoothProduct q v x := by
  rw [norm_prod]
  simp only [Complex.norm_real]
  simp_rw [Real.norm_of_nonneg (rectangularSmoothBlockWeight_nonneg _)]
  cases m <;> cases n <;> simp [a03ZeroModeSmoothProduct,a03SixZeroSourceArguments,
    a03SixZeroPairArguments,Fin.prod_univ_five,mul_comm,mul_left_comm,mul_assoc]

theorem a03ZeroMode_density_sqrt_product (q : QuadraticScales) (v : Fin 5→ℕ)
    (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    1/(Real.sqrt (v 0:ℝ)*Real.sqrt (v 1:ℝ)*Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad q v x i))=
      a03ZeroModeSixDensity (v 0) (v 1) (v 2) (v 3) (Nat.gcd (v 0*v 2) (v 1*v 3)) x := by
  rw [←Real.sqrt_mul (Nat.cast_nonneg (v 0)),
    ←Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg (v 0)) (Nat.cast_nonneg (v 1))),
    a03ZeroModePhysicalQuad_six_density q v hv hx]
  exact (a03ZeroModeSixDensity_gcd_eq (by have := hv 0; omega) (by have := hv 1; omega)
    (by have := hv 2; omega) (by have := hv 3; omega) hx).symm

theorem a03SixTensorPhysicalZeroMode_norm_le_literal_mass
    (F : A03SixTensorSpace→ℂ) (S : ℂ) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (α β : ℕ→ℂ) {C D K : ℝ} (hC : 0≤C) (hD : 0≤D) (_hK : 0≤K)
    (hα : ∀ a : ℕ,0<a → ‖α a‖≤C/Real.sqrt (a:ℝ))
    (hβ : ∀ b : ℕ,0<b → ‖β b‖≤D/Real.sqrt (b:ℝ))
    (hF : ∀ v∈quadraticMainIndexSet q,∀ x : ℝ,0<x → a03ZeroModeSmoothProduct q v x≠0 →
      ‖S*F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))‖≤
        K/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad q v x i)) :
    ‖S*a03SixTensorPhysicalZeroMode F m n q α β‖≤C*D*K*a03ZeroModeLiteralMass q := by
  unfold a03SixTensorPhysicalZeroMode
  rw [Finset.mul_sum]
  calc
    _≤∑ v∈quadraticMainIndexSet q,‖S*(α (v 0)*β (v 1)*∫ x : ℝ in Ioi 0,
      (∏ i : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x i.succ):ℂ))*
        F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))‖ := norm_sum_le _ _
    _≤∑ v∈quadraticMainIndexSet q,C*D*K*∫ x : ℝ in Ioi 0,a03ZeroModeSmoothProduct q v x*
      a03ZeroModeSixDensity (v 0) (v 1) (v 2) (v 3) (Nat.gcd (v 0*v 2) (v 1*v 3)) x := by
      apply Finset.sum_le_sum
      intro v hv
      have hv1 (j : Fin 5) : 1≤v j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)).1
      have hvp (j : Fin 5) : 0<v j := by have := hv1 j; omega
      let g : ℝ→ℝ := fun x => a03ZeroModeSmoothProduct q v x*
        a03ZeroModeSixDensity (v 0) (v 1) (v 2) (v 3) (Nat.gcd (v 0*v 2) (v 1*v 3)) x
      have hgi : IntegrableOn g (Ioi 0) := by
        have hi := (a03ZeroModeContinuousSmoothMass_integrable (a:=(v 0:ℝ)) (b:=(v 1:ℝ))
          (m:=(v 2:ℝ)) (n:=(v 3:ℝ)) (N₂:=q.N₂) (by exact_mod_cast hvp 0)
          (by exact_mod_cast hvp 1) (by exact_mod_cast hvp 2) (by exact_mod_cast hvp 3)
          (a03ZeroMode_gcd_pos (hvp 0) (hvp 1) (hvp 2) (hvp 3)) hM₂).const_mul
          (rectangularSmoothBlockWeight ((Nat.gcd (v 0*v 2) (v 1*v 3):ℝ)*(v 4:ℝ)/q.H)*
            rectangularSmoothBlockWeight ((v 2:ℝ)/q.M₁)*rectangularSmoothBlockWeight ((v 3:ℝ)/q.N₁))
        apply hi.congr
        exact ae_of_all _ (fun x => by dsimp only [g]; rw [a03ZeroModeSmoothProduct_factor]; ring)
      have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
          ‖(α (v 0)*β (v 1))*(∏ i : Fin 5,(rectangularSmoothBlockWeight
            (a03SixZeroSourceArguments m n q v x i.succ):ℂ))*
              (S*F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))‖≤C*D*K*g x := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        by_cases hw : a03ZeroModeSmoothProduct q v x=0
        · have hz : (∏ i : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x i.succ):ℂ))=0 :=
            norm_eq_zero.mp (by rw [a03SixZeroSource_mask_norm,hw])
          simp [hz,g,hw]
        · rw [norm_mul,norm_mul,norm_mul,a03SixZeroSource_mask_norm]
          have hω : 0≤a03ZeroModeSmoothProduct q v x := Finset.prod_nonneg (fun _ _ => rectangularSmoothBlockWeight_nonneg _)
          calc
            _≤((C/Real.sqrt (v 0:ℝ))*(D/Real.sqrt (v 1:ℝ))*a03ZeroModeSmoothProduct q v x)*
                (K/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad q v x i)) := by
              gcongr
              · exact hα _ (hvp 0)
              · exact hβ _ (hvp 1)
              · exact hF v hv x hx hw
            _=C*D*K*g x := by
              dsimp only [g]
              rw [←a03ZeroMode_density_sqrt_product q v hv1 hx]
              ring
      have he : S*(α (v 0)*β (v 1)*∫ x : ℝ in Ioi 0,
          (∏ i : Fin 5,(rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q v x i.succ):ℂ))*
            F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))=
          ∫ x : ℝ in Ioi 0,(α (v 0)*β (v 1))*(∏ i : Fin 5,(rectangularSmoothBlockWeight
            (a03SixZeroSourceArguments m n q v x i.succ):ℂ))*(S*F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) := by
        rw [←integral_const_mul,←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      rw [he]
      exact (norm_integral_le_of_norm_le (hgi.const_mul (C*D*K)) hbound).trans_eq (by rw [integral_const_mul])
    _=C*D*K*a03ZeroModeLiteralMass q := by rw [←Finset.mul_sum]; rfl


theorem a03SixZeroSourceArguments_positive (m n : Bool) (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    ∀ j,0<a03SixZeroSourceArguments m n q v x j := by
  have hp (j : Fin 5) : 0<(v j:ℝ) := by exact_mod_cast (show 0<v j by have := hv j; omega)
  have hd : 0<(Nat.gcd (v 0*v 2) (v 1*v 3):ℝ) :=
    a03ZeroMode_gcd_pos (by have := hv 0; omega) (by have := hv 1; omega)
      (by have := hv 2; omega) (by have := hv 3; omega)
  have hB : 0<q.B := by simpa [QuadraticScales.size] using hq 1
  have hH : 0<q.H := by simpa [QuadraticScales.size] using hq 6
  have hM₁ : 0<q.M₁ := by simpa [QuadraticScales.size] using hq 2
  have hM₂ : 0<q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have hN₁ : 0<q.N₁ := by simpa [QuadraticScales.size] using hq 4
  have hN₂ : 0<q.N₂ := by simpa [QuadraticScales.size] using hq 5
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  intro j
  cases m <;> cases n <;> fin_cases j <;>
    simp [a03SixZeroSourceArguments,a03SixZeroPairArguments,rectangularZeroArguments] <;> positivity

def a03ZeroModeMellinScaleFactor (q : QuadraticScales) (α : MomentShifts) (z : ℂ) : ℂ :=
  ∏ i : Fin 4,(a03ZeroModeQuadScales q i:ℂ)^(-(1/2+α i+z))

theorem a03ZeroMode_scale_mellin_eq_denominator (m n : Bool) (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (α : MomentShifts) (z : ℂ) (v : Fin 5→ℕ)
    (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α z*
      a03TensorMellinFactor α z (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))=
        (a03ZeroModeRealQuadDenominator α z (a03ZeroModePermutedPhysicalQuad m n q v x))⁻¹ := by
  have hy := a03SixZeroSourceArguments_positive m n q hq v hv hx
  have hs (i : Fin 4) : 0<a03ZeroModeQuadScales (phasePairSwapScales m n q) i := by
    cases m <;> cases n <;> fin_cases i <;>
      simp [a03ZeroModeQuadScales,phasePairSwapScales] <;>
      first | simpa [QuadraticScales.size] using hq 2 | simpa [QuadraticScales.size] using hq 3 |
        simpa [QuadraticScales.size] using hq 4 | simpa [QuadraticScales.size] using hq 5
  rw [a03TensorMellinFactor_logPoint α z _ hy]
  unfold a03ZeroModeMellinScaleFactor a03ZeroModeRealQuadDenominator
  rw [←Finset.prod_mul_distrib,←Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [←Complex.mul_cpow_ofReal_nonneg (hs i).le (hy i.succ.succ).le,
    a03ZeroModePermutedPhysicalQuad_normalized]
  have he : (a03ZeroModeQuadScales (phasePairSwapScales m n q) i:ℂ)*
      (a03ZeroModePermutedPhysicalQuad m n q v x i/a03ZeroModeQuadScales (phasePairSwapScales m n q) i:ℝ)=
        (a03ZeroModePermutedPhysicalQuad m n q v x i:ℂ) := by
    push_cast
    field_simp [(Complex.ofReal_ne_zero.mpr (hs i).ne')]
  rw [he,Complex.cpow_neg]

theorem a03ZeroModeMellinScaleFactor_pair_actual (m n : Bool) (A B H c v : ℝ)
    (α : MomentShifts) (k : Fin 4→ℕ) :
    a03ZeroModeMellinScaleFactor (phasePairSwapScales m n (phasePairSwapScales m n (phaseActualScales A B H k)))
      α ((c:ℂ)+(v:ℂ)*I)=a03SourceMellinScaleFactor c v α k := by
  cases m <;> cases n <;> simp [a03ZeroModeMellinScaleFactor,a03SourceMellinScaleFactor,
    a03ZeroModeQuadScales,phasePairSwapScales,phaseActualScales,Fin.prod_univ_four]

end
end SixthMoment

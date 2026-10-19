import Sechstmoment.Numerator.U.ZeroModes.LeadingFubini
import Sechstmoment.Numerator.U.ZeroModes.PhysicalBound

/-! The literal native smooth GCD density controls physical kernels which
depend on the actual integer tuple as well as its continuous x-coordinate. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03NativePhysicalZeroFamily_mass_bound
    (F : (Fin 5→ℕ)→ℝ→ℂ) (m n : Bool) (q : QuadraticScales)
    (hM₂ : 0<q.M₂) (α β : ℕ→ℂ) {C D K : ℝ} (hC : 0≤C) (hD : 0≤D) (_hK : 0≤K)
    (hα : ∀ a : ℕ,0<a → ‖α a‖≤C/Real.sqrt (a:ℝ))
    (hβ : ∀ b : ℕ,0<b → ‖β b‖≤D/Real.sqrt (b:ℝ))
    (hF : ∀ v∈quadraticMainIndexSet q,∀ x : ℝ,0<x → a03ZeroModeSmoothProduct q v x≠0 →
      ‖F v x‖≤K/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad q v x i)) :
    ‖∑v∈quadraticMainIndexSet q,α (v 0)*β (v 1)*∫x : ℝ in Ioi 0,
        a03PhysicalZeroSmoothMask m n q v x*F v x‖≤C*D*K*a03ZeroModeLiteralMass q := by
  calc
    _≤∑v∈quadraticMainIndexSet q,‖α (v 0)*β (v 1)*∫x : ℝ in Ioi 0,
        a03PhysicalZeroSmoothMask m n q v x*F v x‖ := norm_sum_le _ _
    _≤∑v∈quadraticMainIndexSet q,C*D*K*∫x : ℝ in Ioi 0,a03ZeroModeSmoothProduct q v x*
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
          ‖(α (v 0)*β (v 1))*a03PhysicalZeroSmoothMask m n q v x*F v x‖≤C*D*K*g x := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        by_cases hw : a03ZeroModeSmoothProduct q v x=0
        · have hz : a03PhysicalZeroSmoothMask m n q v x=0 := norm_eq_zero.mp
            (by rw [a03PhysicalZeroSmoothMask,a03SixZeroSource_mask_norm,hw])
          simp [hz,g,hw]
        · rw [norm_mul,norm_mul,norm_mul,a03PhysicalZeroSmoothMask,a03SixZeroSource_mask_norm]
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
      rw [←integral_const_mul]
      have he : (fun x : ℝ => (α (v 0)*β (v 1))*(a03PhysicalZeroSmoothMask m n q v x*F v x))=
          (fun x : ℝ => (α (v 0)*β (v 1))*a03PhysicalZeroSmoothMask m n q v x*F v x) := by
        funext x; ring
      rw [he]
      exact (norm_integral_le_of_norm_le (hgi.const_mul (C*D*K)) hbound).trans_eq (by rw [integral_const_mul])
    _=C*D*K*a03ZeroModeLiteralMass q := by rw [←Finset.mul_sum]; rfl

end
end Sechstmoment

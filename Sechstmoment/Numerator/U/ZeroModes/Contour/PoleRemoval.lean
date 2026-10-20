import Sechstmoment.Numerator.Polar.PureRemoval
import Sechstmoment.Numerator.U.ZeroModes.Contour.MainReflection


namespace Sechstmoment
open Complex Source
open scoped BigOperators
open Classical
noncomputable section

def a03ZeroModeMainPoleIndex (j : Fin 2) : PurePolarIndex :=
  if j=0 then (0,(0,0)) else (0,(1,1))

theorem a03ZeroModeMainPoleIndex_ne :
    a03ZeroModeMainPoleIndex 1 ≠ a03ZeroModeMainPoleIndex 0 := by
  norm_num [a03ZeroModeMainPoleIndex]

def a03ZeroModeMainPoleRoot (T : ℝ) (σ : MomentShifts) (j : Fin 2) : ℂ :=
  purePolarRoot T σ (a03ZeroModeMainPoleIndex j)

theorem a03ZeroModeMainPoleRoot_zero (T : ℝ) (σ : MomentShifts) :
    a03ZeroModeMainPoleRoot T σ 0 =
      -(rawMomentShifts T σ 0+rawMomentShifts T σ 2)/2 := by
  simp [a03ZeroModeMainPoleRoot,a03ZeroModeMainPoleIndex,purePolarRoot,
    purePolarLeft,purePolarRight,bblrSixShifts]

theorem a03ZeroModeMainPoleRoot_one (T : ℝ) (σ : MomentShifts) :
    a03ZeroModeMainPoleRoot T σ 1 =
      -(rawMomentShifts T σ 1+rawMomentShifts T σ 3)/2 := by
  simp [a03ZeroModeMainPoleRoot,a03ZeroModeMainPoleIndex,purePolarRoot,
    purePolarLeft,purePolarRight,bblrSixShifts]

def a03ZeroModeMainOtherKiller (T : ℝ) (σ : MomentShifts) (z : ℂ) : ℂ :=
  ∏ k ∈ (Finset.univ.erase (a03ZeroModeMainPoleIndex 0)).erase
    (a03ZeroModeMainPoleIndex 1), polarPoleKillingFactor (purePolarRoot T σ k) z

theorem a03ZeroModeMainKiller_split (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T σ z = exp (z^2)*
      polarPoleKillingFactor (a03ZeroModeMainPoleRoot T σ 0) z*
      polarPoleKillingFactor (a03ZeroModeMainPoleRoot T σ 1) z*
      a03ZeroModeMainOtherKiller T σ z := by
  unfold polarPoleKiller a03ZeroModeMainOtherKiller a03ZeroModeMainPoleRoot
  rw [←Finset.mul_prod_erase Finset.univ
    (fun k => polarPoleKillingFactor (purePolarRoot T σ k) z)
    (Finset.mem_univ (a03ZeroModeMainPoleIndex 0))]
  rw [←Finset.mul_prod_erase (Finset.univ.erase (a03ZeroModeMainPoleIndex 0))
    (fun k => polarPoleKillingFactor (purePolarRoot T σ k) z)
    (Finset.mem_erase.mpr ⟨a03ZeroModeMainPoleIndex_ne,Finset.mem_univ _⟩)]
  ring

theorem a03ZeroModeMainOtherKiller_differentiable (T : ℝ) (σ : MomentShifts) :
    Differentiable ℂ (a03ZeroModeMainOtherKiller T σ) := by
  unfold a03ZeroModeMainOtherKiller
  apply Differentiable.fun_finsetProd
  intro k hk
  change Differentiable ℂ (fun z : ℂ => if purePolarRoot T σ k=0 then 1
    else 1-z^2/(purePolarRoot T σ k)^2)
  split_ifs <;> fun_prop

def a03ZeroModeMainRemovedZeta (T : ℝ) (σ : MomentShifts) (z : ℂ) : ℂ :=
  exp (z^2)*a03ZeroModeMainOtherKiller T σ z*
    (-(z+a03ZeroModeMainPoleRoot T σ 0)/(2*(a03ZeroModeMainPoleRoot T σ 0)^2))*
    ((z+a03ZeroModeMainPoleRoot T σ 1)/(2*(a03ZeroModeMainPoleRoot T σ 1)^2))*
    polarRegularizedZeta (1+2*(z-a03ZeroModeMainPoleRoot T σ 0))*
    polarRegularizedZeta (1-2*(z-a03ZeroModeMainPoleRoot T σ 1))

theorem a03ZeroModeMainRemovedZeta_differentiable (T : ℝ) (σ : MomentShifts) :
    Differentiable ℂ (a03ZeroModeMainRemovedZeta T σ) := by
  unfold a03ZeroModeMainRemovedZeta
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact (((by fun_prop : Differentiable ℂ (fun z : ℂ => exp (z^2))).mul
        (a03ZeroModeMainOtherKiller_differentiable T σ)).mul
        (by fun_prop)).mul (by fun_prop)
    · exact polarRegularizedZeta_differentiable.comp (by fun_prop)
  · exact polarRegularizedZeta_differentiable.comp (by fun_prop)

theorem a03ZeroModeMainRemovedZeta_eq (T : ℝ) (σ : MomentShifts)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0)
    {z : ℂ} (hz : ∀ j : Fin 2, z≠a03ZeroModeMainPoleRoot T σ j) :
    a03ZeroModeMainRemovedZeta T σ z =
      polarPoleKiller T σ z*
        (riemannZeta (1+rawMomentShifts T σ 0+rawMomentShifts T σ 2+2*z)*
          riemannZeta (1-rawMomentShifts T σ 1-rawMomentShifts T σ 3-2*z)) := by
  have harg₀ : 1+2*(z-a03ZeroModeMainPoleRoot T σ 0)≠1 := by
    have hn := mul_ne_zero (by norm_num : (2:ℂ)≠0) (sub_ne_zero.mpr (hz 0))
    simpa using hn
  have harg₁ : 1-2*(z-a03ZeroModeMainPoleRoot T σ 1)≠1 := by
    have hn := mul_ne_zero (by norm_num : (2:ℂ)≠0) (sub_ne_zero.mpr (hz 1))
    intro he
    exact hn (by linear_combination -he)
  have he₀ : 1+2*(z-a03ZeroModeMainPoleRoot T σ 0)=
      1+rawMomentShifts T σ 0+rawMomentShifts T σ 2+2*z := by
    rw [a03ZeroModeMainPoleRoot_zero]
    ring
  have he₁ : 1-2*(z-a03ZeroModeMainPoleRoot T σ 1)=
      1-rawMomentShifts T σ 1-rawMomentShifts T σ 3-2*z := by
    rw [a03ZeroModeMainPoleRoot_one]
    ring
  unfold a03ZeroModeMainRemovedZeta
  rw [polarRegularizedZeta_of_ne_one harg₀,polarRegularizedZeta_of_ne_one harg₁,
    a03ZeroModeMainKiller_split,polarPoleKillingFactor_factorization (hρ 0),
    polarPoleKillingFactor_factorization (hρ 1)]
  rw [←he₀,←he₁]
  ring

end
end Sechstmoment

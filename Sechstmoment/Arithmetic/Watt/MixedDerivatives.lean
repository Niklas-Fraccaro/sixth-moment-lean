import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Sechstmoment.Arithmetic.Watt.GammaProfiles

/-! Mixed derivatives along a linear ray.  Constants are constructed solely
from the fixed mixed derivative sequence, independently of the ray slope. -/

namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def directional (v : ℝ × ℝ) (F : (ℝ × ℝ) → ℂ) (z : ℝ × ℝ) : ℂ :=
  fderiv ℝ F z v

theorem directional_smooth {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (directional v F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem directional_commute {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (v w : ℝ × ℝ) : directional v (directional w F) = directional w (directional v F) := by
  have hd := (hF.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ F))
  funext z
  change (fderiv ℝ (fun x => fderiv ℝ F x w) z) v =
    (fderiv ℝ (fun x => fderiv ℝ F x v) z) w
  rw [fderiv_clm_apply (hd.differentiable (by simp)).differentiableAt (differentiableAt_const w),
    fderiv_clm_apply (hd.differentiable (by simp)).differentiableAt (differentiableAt_const v)]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact hF.contDiffAt.isSymmSndFDerivAt (by simp) v w

theorem directional_fst {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (z : ℝ × ℝ) :
    directional (1,0) F z = deriv (fun x => F (x,z.2)) z.1 := by
  have hd := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact hd.deriv.symm

theorem directional_snd {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (z : ℝ × ℝ) :
    directional (0,1) F z = deriv (fun y => F (z.1,y)) z.2 := by
  have hd := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hd.deriv.symm

theorem directional_iterate_smooth {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (v : ℝ × ℝ) (n : ℕ) : ContDiff ℝ ∞ ((directional v)^[n] F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact directional_smooth ih v

theorem directional_iterate_commute {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (v w : ℝ × ℝ) (n : ℕ) :
    directional v ((directional w)^[n] F) = (directional w)^[n] (directional v F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',directional_commute (directional_iterate_smooth hF w n),
      ih,Function.iterate_succ_apply']

def mixedPartial (F : (ℝ × ℝ) → ℂ) (i j : ℕ) : (ℝ × ℝ) → ℂ :=
  (directional (0,1))^[j] ((directional (1,0))^[i] F)

theorem mixedPartial_smooth {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (i j : ℕ) :
    ContDiff ℝ ∞ (mixedPartial F i j) :=
  directional_iterate_smooth (directional_iterate_smooth hF (1,0) i) (0,1) j

theorem directional_mixedPartial_fst {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (i j : ℕ) :
    directional (1,0) (mixedPartial F i j) = mixedPartial F (i+1) j := by
  unfold mixedPartial
  rw [directional_iterate_commute (directional_iterate_smooth hF (1,0) i),
    Function.iterate_succ_apply' (directional (1,0)) i F]

theorem directional_mixedPartial_snd (F : (ℝ × ℝ) → ℂ) (i j : ℕ) :
    directional (0,1) (mixedPartial F i j) = mixedPartial F i (j+1) := by
  unfold mixedPartial
  rw [Function.iterate_succ_apply']

theorem directional_iterate_fst {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (i : ℕ) (z : ℝ × ℝ) :
    ((directional (1,0))^[i] F) z = iteratedDeriv i (fun x => F (x,z.2)) z.1 := by
  induction i generalizing z with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',directional_fst (directional_iterate_smooth hF (1,0) i)]
    simp_rw [ih]
    rw [iteratedDeriv_succ]

theorem mixedPartial_eq {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (i j : ℕ) (z : ℝ × ℝ) :
    mixedPartial F i j z =
      iteratedDeriv j (fun y => iteratedDeriv i (fun x => F (x,y)) z.1) z.2 := by
  induction j generalizing z with
  | zero => exact directional_iterate_fst hF i z
  | succ j ih =>
    rw [← directional_mixedPartial_snd,directional_snd (mixedPartial_smooth hF i j)]
    simp_rw [ih]
    rw [iteratedDeriv_succ]

theorem mixedPartial_ray_deriv {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (a : ℝ) (i j : ℕ) :
    deriv (fun t => mixedPartial F i j (a*t,t)) =
      fun t => (a : ℂ)*mixedPartial F (i+1) j (a*t,t)+mixedPartial F i (j+1) (a*t,t) := by
  funext t
  have hM := mixedPartial_smooth hF i j
  have hd := (hM.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).const_mul a).prodMk (hasDerivAt_id t))
  have hder : deriv (fun t => mixedPartial F i j (a*t,t)) t =
      fderiv ℝ (mixedPartial F i j) (a*t,t) (a,1) := by
    simpa only [Function.comp_def,id_eq,mul_one] using hd.deriv
  rw [hder]
  have hsplit : (a,1) = a • ((1,0) : ℝ × ℝ)+(0,1) := by ext <;> simp
  rw [hsplit,map_add,map_smul]
  change a • directional (1,0) (mixedPartial F i j) (a*t,t)+
    directional (0,1) (mixedPartial F i j) (a*t,t) = _
  rw [directional_mixedPartial_fst hF,directional_mixedPartial_snd]
  simp only [Complex.real_smul]

def normalizedMixedRay (F : (ℝ × ℝ) → ℂ) (a : ℝ) (i j : ℕ) (t : ℝ) : ℂ :=
  (a : ℂ)^i*mixedPartial F i j (a*t,t)

theorem normalizedMixedRay_smooth {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (a : ℝ) (i j : ℕ) : ContDiff ℝ ∞ (normalizedMixedRay F a i j) :=
  contDiff_const.mul ((mixedPartial_smooth hF i j).comp
    ((contDiff_const.mul contDiff_id).prodMk contDiff_id))

theorem normalizedMixedRay_deriv {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (a : ℝ) (i j : ℕ) :
    deriv (normalizedMixedRay F a i j) =
      fun t => normalizedMixedRay F a (i+1) j t+normalizedMixedRay F a i (j+1) t := by
  unfold normalizedMixedRay
  rw [deriv_const_mul_field',mixedPartial_ray_deriv hF]
  funext t
  simp only [pow_succ]
  ring

/-- Recursively summed mixed derivative constants.  No slope or scale occurs. -/
def rayDerivativeBound (g : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, i, j => g i j
  | n+1, i, j => rayDerivativeBound g n (i+1) j+rayDerivativeBound g n i (j+1)

theorem rayDerivativeBound_nonneg {g : ℕ → ℕ → ℝ} (hg : ∀ i j, 0 ≤ g i j)
    (n i j : ℕ) : 0 ≤ rayDerivativeBound g n i j := by
  induction n generalizing i j with
  | zero => exact hg i j
  | succ n ih => exact add_nonneg (ih (i+1) j) (ih i (j+1))

theorem normalizedMixedRay_derivative_bound {F : (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) {g : ℕ → ℕ → ℝ}
    (hd : ∀ i j x y, 0 < x → 0 < y →
      ‖mixedPartial F i j (x,y)‖ ≤ g i j*x^(-(i : ℝ))*y^(-(j : ℝ)))
    {a : ℝ} (ha : 0 < a) (n i j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv n (normalizedMixedRay F a i j) t‖ ≤
      rayDerivativeBound g n i j*t^(-((i+j+n : ℕ) : ℝ)) := by
  induction n generalizing i j with
  | zero =>
    rw [iteratedDeriv_zero]
    simp only [normalizedMixedRay,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_of_nonneg ha.le]
    have hp : a^i*((a*t)^(-(i : ℝ))*t^(-(j : ℝ))) =
        t^(-((i+j : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (mul_pos ha ht).le,Real.rpow_natCast,mul_pow,
        Real.rpow_neg ht.le,Real.rpow_natCast,Real.rpow_neg ht.le,Real.rpow_natCast,pow_add]
      field_simp [ha.ne',ht.ne']
    calc
      _ ≤ a^i*(g i j*(a*t)^(-(i : ℝ))*t^(-(j : ℝ))) :=
        mul_le_mul_of_nonneg_left (hd i j (a*t) t (mul_pos ha ht) ht) (pow_nonneg ha.le i)
      _ = g i j*(a^i*((a*t)^(-(i : ℝ))*t^(-(j : ℝ)))) := by ring
      _ = _ := by rw [hp]; rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',normalizedMixedRay_deriv hF,
      iteratedDeriv_fun_add
        ((normalizedMixedRay_smooth hF a (i+1) j).of_le (by exact_mod_cast le_top)).contDiffAt
        ((normalizedMixedRay_smooth hF a i (j+1)).of_le (by exact_mod_cast le_top)).contDiffAt]
    apply (norm_add_le _ _).trans
    have h₁ := ih (i+1) j
    have h₂ := ih i (j+1)
    have he₁ : i+1+j+n = i+j+(n+1) := by omega
    have he₂ : i+(j+1)+n = i+j+(n+1) := by omega
    simpa only [he₁,he₂,rayDerivativeBound,add_mul] using add_le_add h₁ h₂

/-- Uniform multiplicative derivative bounds for the new p-weight.
The bound is independent of the positive ray slope. -/
theorem gamma_ray_derivative_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (r s : ℕ) {A : ℝ} (hA : 0 < A) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv j (fun t => γ r s (A*t) t) t‖ ≤
      rayDerivativeBound g j 0 0*t^(-(j : ℝ)) := by
  have hF := hw.gamma_smooth r s
  have hd : ∀ i j x y, 0 < x → 0 < y →
      ‖mixedPartial (fun z : ℝ × ℝ => γ r s z.1 z.2) i j (x,y)‖ ≤
        g i j*x^(-(i : ℝ))*y^(-(j : ℝ)) := by
    intro i j x y hx hy
    rw [mixedPartial_eq hF]
    exact hw.gamma_derivatives r s i j x y hx hy
  have heq : normalizedMixedRay (fun z : ℝ × ℝ => γ r s z.1 z.2) A 0 0 =
      fun t => γ r s (A*t) t := by
    funext t
    simp only [normalizedMixedRay,mixedPartial,pow_zero,Function.iterate_zero,one_mul,id_eq]
  have hbound := normalizedMixedRay_derivative_bound hF hd hA j 0 0 ht
  rw [heq] at hbound
  simpa only [Nat.zero_add] using hbound

end
end Watt41
end DivisorProof

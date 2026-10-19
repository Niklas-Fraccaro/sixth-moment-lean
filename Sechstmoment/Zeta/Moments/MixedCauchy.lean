import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Sechstmoment.Analysis.Complex.CauchyBounds
import Sechstmoment.Analysis.Complex.Polydisc
import Sechstmoment.Zeta.Moments.Shifts

/-!
# Own Cauchy transfer for genuine mixed shift derivatives

The derivatives below are the actual complex Frechet derivatives applied to
coordinate basis vectors. A disk estimate is applied repeatedly, on shrinking
cubes. The constants depend on derivative order and never on `T`.
-/
namespace Sechstmoment
open Complex Metric Filter Set
open scoped BigOperators Topology
noncomputable section

/-- An open cube in the four actual normalized complex shifts. -/
def momentOpenCube (r : ℝ) : Set MomentShifts := {σ | ∀ j, ‖σ j‖ < r}

theorem momentOpenCube_isOpen (r : ℝ) : IsOpen (momentOpenCube r) := by
  unfold momentOpenCube
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const

/-- The actual derivative in the indicated shift coordinate. -/
def coordinateShiftDeriv (i : Fin 4) (f : MomentShifts → ℂ) (σ : MomentShifts) : ℂ :=
  fderiv ℂ f σ (Pi.single i 1)

/-- Arbitrary ordered mixed derivatives, including repeated coordinates. -/
def orderedShiftDeriv : List (Fin 4) → (MomentShifts → ℂ) → MomentShifts → ℂ
  | [],f => f
  | i :: is,f => coordinateShiftDeriv i (orderedShiftDeriv is f)

/-- Actual coordinate derivatives remain jointly holomorphic. -/
theorem coordinateShiftDeriv_analyticOnNhd (i : Fin 4) {f : MomentShifts → ℂ}
    {s : Set MomentShifts} (hf : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ (coordinateShiftDeriv i f) s :=
  by
    unfold coordinateShiftDeriv
    exact (ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : MomentShifts)).comp_analyticOnNhd hf.fderiv

theorem orderedShiftDeriv_analyticOnNhd (is : List (Fin 4)) {f : MomentShifts → ℂ}
    {s : Set MomentShifts} (hf : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ (orderedShiftDeriv is f) s := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact coordinateShiftDeriv_analyticOnNhd i ih

/-- Identification with the ordinary derivative on the actual coordinate line. -/
theorem coordinateShiftDeriv_eq_deriv (i : Fin 4) (f : MomentShifts → ℂ)
    (σ : MomentShifts) (hf : DifferentiableAt ℂ f σ) :
    coordinateShiftDeriv i f σ = deriv (fun z : ℂ => f (Function.update σ i z)) (σ i) := by
  have hu : HasDerivAt (Function.update σ i) (Pi.single i (1 : ℂ)) (σ i) := by
    have hh := (hasFDerivAt_update (i := i) σ (σ i)).hasDerivAt
    convert hh using 1
    funext j
    by_cases hji : j=i <;> simp [hji]
  have hf' : HasFDerivAt f (fderiv ℂ f σ) (Function.update σ i (σ i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt (σ i) hu
  simpa only [Function.update_eq_self, coordinateShiftDeriv, Function.comp_def] using hh.deriv.symm

def mixedCauchyRadius (n : ℕ) : ℝ := 1/(2:ℝ)^(n+1)

def mixedCauchyConstant : ℕ → ℝ
  | 0 => 1
  | n+1 => mixedCauchyConstant n/mixedCauchyRadius (n+1)

theorem mixedCauchyRadius_pos (n : ℕ) : 0 < mixedCauchyRadius n := by
  unfold mixedCauchyRadius
  positivity

theorem mixedCauchyRadius_le_half (n : ℕ) : mixedCauchyRadius n ≤ 1/2 := by
  unfold mixedCauchyRadius
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  calc
    2 = (2 : ℝ)^1 := by norm_num
    _ ≤ (2 : ℝ)^(n+1) := pow_le_pow_right₀ (by norm_num) (by omega)

theorem mixedCauchyRadius_succ (n : ℕ) :
    2*mixedCauchyRadius (n+1)=mixedCauchyRadius n := by
  unfold mixedCauchyRadius
  rw [pow_succ]
  field_simp

theorem mixedCauchyConstant_nonneg (n : ℕ) : 0 ≤ mixedCauchyConstant n := by
  induction n with
  | zero => norm_num [mixedCauchyConstant]
  | succ n ih => exact div_nonneg ih (mixedCauchyRadius_pos _).le

private theorem coordinate_update_cube {r : ℝ} (i : Fin 4) (σ : MomentShifts)
    (hσ : σ ∈ rectangularClosedPolydisc (fun _ => r)) {z : ℂ}
    (hz : ‖z-σ i‖ ≤ r) :
    Function.update σ i z ∈ rectangularClosedPolydisc (fun _ => 2*r) := by
  intro j
  by_cases hji : j=i
  · subst j
    rw [Function.update_self]
    have hh : ‖z‖ ≤ ‖z-σ i‖+‖σ i‖ := by
      convert norm_add_le (z-σ i) (σ i) using 1; simp
    linarith [hσ i]
  · rw [Function.update_of_ne hji]
    have hr : 0 ≤ r := (norm_nonneg (σ j)).trans (hσ j)
    linarith [hσ j]

/-- Repeated Cauchy differentiation bounds all ordered mixed shift derivatives
on a smaller cube by a fixed order-dependent constant. -/
theorem orderedShiftDeriv_cauchy_bound (is : List (Fin 4)) {f : MomentShifts → ℂ}
    (hf : AnalyticOnNhd ℂ f (momentOpenCube 1)) {M : ℝ}
    (hM : ∀ σ ∈ rectangularClosedPolydisc (fun _ => mixedCauchyRadius 0), ‖f σ‖ ≤ M) :
    ∀ σ ∈ rectangularClosedPolydisc (fun _ => mixedCauchyRadius is.length),
      ‖orderedShiftDeriv is f σ‖ ≤ mixedCauchyConstant is.length*M := by
  induction is with
  | nil => simpa [orderedShiftDeriv,mixedCauchyConstant] using hM
  | cons i is ih =>
    intro σ hσ
    change σ ∈ rectangularClosedPolydisc (fun _ => mixedCauchyRadius (is.length+1)) at hσ
    let r := mixedCauchyRadius (is.length+1)
    let g := orderedShiftDeriv is f
    have hr : 0 < r := mixedCauchyRadius_pos _
    have hprev : 2*r=mixedCauchyRadius is.length := mixedCauchyRadius_succ _
    have hg := orderedShiftDeriv_analyticOnNhd is hf
    have hupd (z : ℂ) (hz : z ∈ closedBall (σ i) r) :
        Function.update σ i z ∈ rectangularClosedPolydisc (fun _ => mixedCauchyRadius is.length) := by
      have hh := coordinate_update_cube i σ hσ (by simpa only [mem_closedBall,dist_eq_norm] using hz)
      simpa only [← hprev] using hh
    have hopen (z : ℂ) (hz : z ∈ closedBall (σ i) r) :
        Function.update σ i z ∈ momentOpenCube 1 := by
      intro j
      exact (hupd z hz j).trans_lt (lt_of_le_of_lt (mixedCauchyRadius_le_half _) (by norm_num))
    have ha : AnalyticOnNhd ℂ (fun z => g (Function.update σ i z)) (closedBall (σ i) r) := by
      intro z hz
      have hdu : Differentiable ℂ (Function.update σ i) :=
        fun w => (hasFDerivAt_update (i := i) σ w).differentiableAt
      have hu : AnalyticAt ℂ (Function.update σ i) z := hdu.analyticAt z
      exact (hg _ (hopen z hz)).comp (f := Function.update σ i) hu
    have hline : DiffContOnCl ℂ (fun z => g (Function.update σ i z)) (ball (σ i) r) :=
      (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    have hsopen : σ ∈ momentOpenCube 1 := by
      intro j
      exact (hσ j).trans_lt (lt_of_le_of_lt (mixedCauchyRadius_le_half _) (by norm_num))
    change ‖coordinateShiftDeriv i g σ‖ ≤ _
    rw [coordinateShiftDeriv_eq_deriv i g σ (hg _ hsopen).differentiableAt]
    have hb := cauchy_iteratedDeriv_bound 1 hr hline (fun z hz => ih _
      (hupd z (sphere_subset_closedBall hz)))
    simp only [iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,pow_one,List.length_cons,
      mixedCauchyConstant] at hb ⊢
    convert hb using 1; ring


/-- A genuine bound on a separated product of circles therefore controls all
mixed derivatives at the coincident-shift point. -/
theorem orderedShiftDeriv_polydisc_bound (is : List (Fin 4))
    (R : Fin 4 → ℝ) (hR : ∀ j, 1 ≤ R j) (f : MomentShifts → ℂ)
    (hf : DifferentiableOn ℂ f (rectangularClosedPolydisc R))
    (ha : AnalyticOnNhd ℂ f (momentOpenCube 1)) {M : ℝ}
    (hboundary : ∀ σ ∈ rectangularDistinguishedBoundary R, ‖f σ‖ ≤ M) :
    ‖orderedShiftDeriv is f 0‖ ≤ mixedCauchyConstant is.length*M := by
  have hb := rectangular_polydisc_norm_le R (fun j => zero_lt_one.trans_le (hR j)) f hf hboundary
  have hhalf : rectangularClosedPolydisc (fun _ => mixedCauchyRadius 0) ⊆
      rectangularClosedPolydisc R := by
    intro σ hσ j
    exact (hσ j).trans ((mixedCauchyRadius_le_half 0).trans (by linarith [hR j]))
  have hzero : (0 : MomentShifts) ∈ rectangularClosedPolydisc
      (fun _ => mixedCauchyRadius is.length) := by
    intro j
    simpa using (mixedCauchyRadius_pos is.length).le
  exact orderedShiftDeriv_cauchy_bound is ha (fun σ hσ => hb σ (hhalf hσ)) 0 hzero

/-- The same fixed constant works for an entire actual moment-error family;
there is no logarithmic loss from mixed complex shift differentiation. -/
theorem orderedShiftDeriv_uniform_polydisc_bound (is : List (Fin 4))
    (R : Fin 4 → ℝ) (hR : ∀ j, 1 ≤ R j)
    (f : ℝ → MomentShifts → ℂ) (B : ℝ → ℝ)
    (hf : ∀ᶠ T : ℝ in atTop, DifferentiableOn ℂ (f T) (rectangularClosedPolydisc R))
    (ha : ∀ᶠ T : ℝ in atTop, AnalyticOnNhd ℂ (f T) (momentOpenCube 1))
    (hboundary : ∀ᶠ T : ℝ in atTop, ∀ σ ∈ rectangularDistinguishedBoundary R,
      ‖f T σ‖ ≤ B T) :
    ∀ᶠ T : ℝ in atTop, ‖orderedShiftDeriv is (f T) 0‖ ≤
      mixedCauchyConstant is.length*B T := by
  filter_upwards [hf,ha,hboundary] with T hTf hTa hTb
  exact orderedShiftDeriv_polydisc_bound is R hR (f T) hTf hTa hTb

end
end Sechstmoment

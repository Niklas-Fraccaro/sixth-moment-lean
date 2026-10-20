import SixthMoment.Numerator.U.ZeroModes.Ratio.ExponentialWeights


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioWeightedKernel_primary_horizontal_tendsto_zero
    (L M : ℝ) {ε δ d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hdabs : |d|≤1) (hdsep : ε≤|d|) (z : ℝ) :
    Tendsto (fun y : ℝ => ∫ c in (a03ZeroModeRatioPrimaryLine ε)..ε,
      a03ZeroModeRatioWeightedKernel L M α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s)
        (cocompact ℝ) (𝓝 0) := by
  have hbnd := a03ZeroModeRatioArithmeticKernel_primary_horizontal_majorant
    hε hε1 hδ α hα hρ ha hb hs hd hdabs hdsep z
  have hedge := a03RatioExponential_horizontal_tendsto_zero L
    (a03ZeroModeRatioPrimaryLine ε) ε
    (fun u => a03ZeroModeRatioArithmeticKernel α a b u ((d:ℂ)+(z:ℂ)*I) s)
    (by unfold a03ZeroModeRatioPrimaryLine; linarith)
    (by
      intro c hc
      apply abs_le.mpr
      unfold a03ZeroModeRatioPrimaryLine at hc
      constructor <;> linarith [hc.1,hc.2]) hbnd
  have h := hedge.const_mul (exp ((M:ℂ)*((d:ℂ)+(z:ℂ)*I)))
  simp only [mul_zero] at h
  apply h.congr'
  exact Eventually.of_forall (fun y => by
    simp_rw [a03ZeroModeRatioWeightedKernel_split]
    rw [intervalIntegral.integral_const_mul])

theorem a03ZeroModeRatioWeightedKernel_primary_left_shift
    (L M : ℝ) {ε δ d : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hd : a03ZeroModeRatioPrimaryLine ε≤d)
    (hdabs : |d|≤1) (hdsep : ε≤|d|) (z : ℝ) :
    verticalIntegral ε (fun u => a03ZeroModeRatioWeightedKernel L M α a b
      u ((d:ℂ)+(z:ℂ)*I) s)=
        verticalIntegral (a03ZeroModeRatioPrimaryLine ε)
          (fun u => a03ZeroModeRatioWeightedKernel L M α a b u ((d:ℂ)+(z:ℂ)*I) s)+
            a03ZeroModeRatioWeightedLeftResidue L M α a b s ((d:ℂ)+(z:ℂ)*I) := by
  let v : ℂ := (d:ℂ)+(z:ℂ)*I
  let H : ℂ→ℂ := fun u => a03ZeroModeRatioWeightedNumerator L M α a b u v s/v
  let U : Set ℂ := {u | 1<(a03ZeroModeRatioEulerArgument α u v).re}
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    unfold a03ZeroModeRatioEulerArgument
    fun_prop
  have hH : DifferentiableOn ℂ H U := by
    intro u hu
    exact ((a03ZeroModeRatioWeightedNumerator_differentiableAt_comp L M α ha hb
      (by linarith : 1≤s.re) (U := id) (V := fun _ : ℂ => v)
        (by fun_prop) (by fun_prop) hu).div_const v).differentiableWithinAt
  have hstrip : ∀ u : ℂ,a03ZeroModeRatioPrimaryLine ε≤u.re → u.re≤ε → u∈U := by
    intro u hu _
    have hreg : A03ZeroModeRatioContourRegion ε u v :=
      a03ZeroModeRatio_primary_rectangle_region hε (by linarith) hu (by simpa [v] using hd)
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact lt_of_lt_of_le (by linarith : 1<1+ε) hA
  have he (u : ℂ) : H u/u=a03ZeroModeRatioWeightedKernel L M α a b u ((d:ℂ)+(z:ℂ)*I) s := by
    dsimp [H,v]
    rw [div_div,mul_comm ((d:ℂ)+(z:ℂ)*I) u,a03ZeroModeRatioWeightedNumerator_div_eq]
  have hsecD : a03ZeroModeRatioSecondaryLine ε≤d := by
    unfold a03ZeroModeRatioPrimaryLine at hd
    unfold a03ZeroModeRatioSecondaryLine
    linarith
  have hregLines (c : ℝ) (hc : a03ZeroModeRatioPrimaryLine ε≤c) :
      a03ZeroModeRatioSecondaryLine ε≤c ∧ a03ZeroModeRatioSecondaryLine ε≤c+d := by
    unfold a03ZeroModeRatioPrimaryLine at hc hd
    unfold a03ZeroModeRatioSecondaryLine
    constructor <;> linarith
  have hleft0 := a03ZeroModeRatioArithmeticKernel_boundary_left_integrable hε hδ α hα hρ
    ha hb hs (hregLines _ le_rfl).1 hsecD (hregLines _ le_rfl).2
    (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 hdabs
    (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1 hdsep z
  have hright0 := a03ZeroModeRatioArithmeticKernel_boundary_left_integrable hε hδ α hα hρ
    ha hb hs (hregLines ε (by unfold a03ZeroModeRatioPrimaryLine; linarith)).1 hsecD
    (hregLines ε (by unfold a03ZeroModeRatioPrimaryLine; linarith)).2
    (by rw [abs_of_pos hε]; linarith) hdabs (by rw [abs_of_pos hε]) hdsep z
  have hleft := a03RatioExponentialPair_line_integrable L M (a03ZeroModeRatioPrimaryLine ε) v
    (fun u => a03ZeroModeRatioArithmeticKernel α a b u v s) hleft0
  have hright := a03RatioExponentialPair_line_integrable L M ε v
    (fun u => a03ZeroModeRatioArithmeticKernel α a b u v s) hright0
  change Integrable (fun y : ℝ => a03ZeroModeRatioWeightedKernel L M α a b
    ((a03ZeroModeRatioPrimaryLine ε:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s) at hleft
  change Integrable (fun y : ℝ => a03ZeroModeRatioWeightedKernel L M α a b
    ((ε:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s) at hright
  have hedge := a03ZeroModeRatioWeightedKernel_primary_horizontal_tendsto_zero
    L M hε hε1 hδ α hα hρ ha hb hs hd hdabs hdsep z
  simp_rw [←he] at hleft hright hedge
  have hrect := SixthMoment.mellinRectangle_simplePole_shift H hU hH
    (by unfold a03ZeroModeRatioPrimaryLine; linarith) hε hstrip hleft hright hedge
  unfold verticalIntegral
  simp_rw [he] at hrect
  rw [hrect,mul_add]
  have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
  rw [←mul_assoc,one_div,inv_mul_cancel₀ hπ,one_mul]
  change _+a03ZeroModeRatioWeightedNumerator L M α a b 0 ((d:ℂ)+(z:ℂ)*I) s/
    ((d:ℂ)+(z:ℂ)*I)=_
  rw [a03ZeroModeRatioWeightedNumerator_left_residue]

theorem a03ZeroModeRatioWeightedKernel_primary_right_shift
    (L M : ℝ) {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioPrimaryLine ε≤c)
    (hcabs : |c|≤1) (hcsep : ε≤|c|) (y : ℝ) :
    verticalIntegral ε (fun v => a03ZeroModeRatioWeightedKernel L M α a b
      ((c:ℂ)+(y:ℂ)*I) v s)=
        verticalIntegral (a03ZeroModeRatioPrimaryLine ε)
          (fun v => a03ZeroModeRatioWeightedKernel L M α a b ((c:ℂ)+(y:ℂ)*I) v s)+
            a03ZeroModeRatioWeightedRightResidue L M α a b s ((c:ℂ)+(y:ℂ)*I) := by
  simpa only [a03ZeroModeRatioWeightedKernel_sideSwap,a03ZeroModeRatioWeightedLeftResidue_sideSwap] using
    a03ZeroModeRatioWeightedKernel_primary_left_shift M L hε hε1 hδ
      (a03ZeroModeRatioSideSwap α) (a03ZeroModeRatioSideSwap_small hα)
        (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs hc hcabs hcsep y

end
end SixthMoment.Source

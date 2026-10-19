import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.DenselyOrdered

/-! Four independent compactly supported probability profiles concentrate jointly.
The proof uses only the one-coordinate continuous-test limits: the expected sum
of four absolute coordinate errors tends to zero, and controls every continuous
test on the compact box. In particular no joint convergence is postulated. -/

namespace Sechstmoment
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

abbrev P02ProfilePoint := (ℝ × ℝ) × (ℝ × ℝ)

def p02ProfileBox (L : ℝ) : Set P02ProfilePoint :=
  (Icc 0 L ×ˢ Icc 0 L) ×ˢ (Icc 0 L ×ˢ Icc 0 L)

def p02ProfilePoint (a : Fin 4 → ℝ) : P02ProfilePoint := ((a 0,a 1),(a 2,a 3))

def p02ProfileDensity (ρ : Fin 4 → ℝ → ℝ) (z : P02ProfilePoint) : ℝ :=
  (ρ 0 z.1.1 * ρ 1 z.1.2) * (ρ 2 z.2.1 * ρ 3 z.2.2)

def profileProductAverage4 (ρ : ℕ → Fin 4 → ℝ → ℝ) (n : ℕ)
    (F : P02ProfilePoint → ℝ) : ℝ :=
  ∫ z : P02ProfilePoint, p02ProfileDensity (ρ n) z * F z
    ∂((volume.prod volume).prod (volume.prod volume))

private def p02DistanceSum (z a : P02ProfilePoint) : ℝ :=
  (|z.1.1-a.1.1|+|z.1.2-a.1.2|)+(|z.2.1-a.2.1|+|z.2.2-a.2.2|)

private theorem p02DistanceSum_nonneg (z a : P02ProfilePoint) :
    0 ≤ p02DistanceSum z a := by unfold p02DistanceSum; positivity

private theorem p02DistanceSum_dist (z a : P02ProfilePoint) :
    dist z a ≤ p02DistanceSum z a := by
  simp only [Prod.dist_eq,Real.dist_eq,p02DistanceSum]
  apply max_le <;> apply max_le <;>
    linarith [abs_nonneg (z.1.1-a.1.1),abs_nonneg (z.1.2-a.1.2),
      abs_nonneg (z.2.1-a.2.1),abs_nonneg (z.2.2-a.2.2)]

theorem p02ProfileDensity_integrable (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, Integrable (ρ i)) :
    Integrable (p02ProfileDensity ρ)
      ((volume.prod volume).prod (volume.prod volume)) :=
  ((hρ 0).mul_prod (hρ 1)).mul_prod ((hρ 2).mul_prod (hρ 3))

theorem p02ProfileDensity_nonneg (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i x, 0 ≤ ρ i x) (z : P02ProfilePoint) :
    0 ≤ p02ProfileDensity ρ z :=
  mul_nonneg (mul_nonneg (hρ 0 _) (hρ 1 _)) (mul_nonneg (hρ 2 _) (hρ 3 _))

private theorem p02_four_integral (f0 f1 f2 f3 : ℝ → ℝ) :
    (∫ z : P02ProfilePoint, (f0 z.1.1*f1 z.1.2)*(f2 z.2.1*f3 z.2.2)
      ∂((volume.prod volume).prod (volume.prod volume))) =
      ((∫ x : ℝ, f0 x)*(∫ x : ℝ, f1 x))*((∫ x : ℝ, f2 x)*(∫ x : ℝ, f3 x)) := by
  calc
    _ = (∫ u : ℝ×ℝ, f0 u.1*f1 u.2 ∂volume.prod volume)*
        (∫ v : ℝ×ℝ, f2 v.1*f3 v.2 ∂volume.prod volume) :=
      integral_prod_mul (fun u : ℝ×ℝ => f0 u.1*f1 u.2)
        (fun v : ℝ×ℝ => f2 v.1*f3 v.2)
    _ = _ := by rw [integral_prod_mul f0 f1,integral_prod_mul f2 f3]

theorem p02ProfileDensity_mass (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, (∫ x : ℝ, ρ i x) = 1) :
    (∫ z : P02ProfilePoint, p02ProfileDensity ρ z
      ∂((volume.prod volume).prod (volume.prod volume))) = 1 := by
  unfold p02ProfileDensity
  rw [p02_four_integral,hρ 0,hρ 1,hρ 2,hρ 3]
  norm_num

private theorem p02ProfileDensity_distance (ρ : Fin 4 → ℝ → ℝ)
    (a : Fin 4 → ℝ) (hρ : ∀ i, Integrable (ρ i))
    (hd : ∀ i, Integrable (fun x : ℝ => ρ i x*|x-a i|))
    (hm : ∀ i, (∫ x : ℝ, ρ i x) = 1) :
    Integrable (fun z : P02ProfilePoint => p02ProfileDensity ρ z *
      p02DistanceSum z (p02ProfilePoint a))
      ((volume.prod volume).prod (volume.prod volume)) ∧
    (∫ z : P02ProfilePoint, p02ProfileDensity ρ z *
      p02DistanceSum z (p02ProfilePoint a)
      ∂((volume.prod volume).prod (volume.prod volume))) =
      ((∫ x : ℝ, ρ 0 x*|x-a 0|)+(∫ x : ℝ, ρ 1 x*|x-a 1|))+
      ((∫ x : ℝ, ρ 2 x*|x-a 2|)+(∫ x : ℝ, ρ 3 x*|x-a 3|)) := by
  let f0 : P02ProfilePoint → ℝ := fun z =>
    ((ρ 0 z.1.1*|z.1.1-a 0|)*ρ 1 z.1.2)*(ρ 2 z.2.1*ρ 3 z.2.2)
  let f1 : P02ProfilePoint → ℝ := fun z =>
    (ρ 0 z.1.1*(ρ 1 z.1.2*|z.1.2-a 1|))*(ρ 2 z.2.1*ρ 3 z.2.2)
  let f2 : P02ProfilePoint → ℝ := fun z =>
    (ρ 0 z.1.1*ρ 1 z.1.2)*((ρ 2 z.2.1*|z.2.1-a 2|)*ρ 3 z.2.2)
  let f3 : P02ProfilePoint → ℝ := fun z =>
    (ρ 0 z.1.1*ρ 1 z.1.2)*(ρ 2 z.2.1*(ρ 3 z.2.2*|z.2.2-a 3|))
  have h0 : Integrable f0 ((volume.prod volume).prod (volume.prod volume)) :=
    ((hd 0).mul_prod (hρ 1)).mul_prod ((hρ 2).mul_prod (hρ 3))
  have h1 : Integrable f1 ((volume.prod volume).prod (volume.prod volume)) :=
    ((hρ 0).mul_prod (hd 1)).mul_prod ((hρ 2).mul_prod (hρ 3))
  have h2 : Integrable f2 ((volume.prod volume).prod (volume.prod volume)) :=
    ((hρ 0).mul_prod (hρ 1)).mul_prod ((hd 2).mul_prod (hρ 3))
  have h3 : Integrable f3 ((volume.prod volume).prod (volume.prod volume)) :=
    ((hρ 0).mul_prod (hρ 1)).mul_prod ((hρ 2).mul_prod (hd 3))
  have he : (fun z : P02ProfilePoint => p02ProfileDensity ρ z *
      p02DistanceSum z (p02ProfilePoint a)) = (f0+f1)+(f2+f3) := by
    funext z
    simp only [p02ProfileDensity,p02DistanceSum,p02ProfilePoint,
      Pi.add_apply,f0,f1,f2,f3]
    ring
  rw [he]
  constructor
  · exact (h0.add h1).add (h2.add h3)
  · change (∫ z, (f0 z+f1 z)+(f2 z+f3 z)
      ∂((volume.prod volume).prod (volume.prod volume))) = _
    have hadd : (∫ z, (f0 z+f1 z)+(f2 z+f3 z)
        ∂((volume.prod volume).prod (volume.prod volume))) =
        (∫ z, f0 z+f1 z ∂((volume.prod volume).prod (volume.prod volume)))+
        (∫ z, f2 z+f3 z ∂((volume.prod volume).prod (volume.prod volume))) :=
      integral_add (h0.add h1) (h2.add h3)
    rw [hadd,integral_add h0 h1,integral_add h2 h3]
    simp only [f0,f1,f2,f3]
    rw [p02_four_integral (fun x => ρ 0 x*|x-a 0|) (ρ 1) (ρ 2) (ρ 3),
      p02_four_integral (ρ 0) (fun x => ρ 1 x*|x-a 1|) (ρ 2) (ρ 3),
      p02_four_integral (ρ 0) (ρ 1) (fun x => ρ 2 x*|x-a 2|) (ρ 3),
      p02_four_integral (ρ 0) (ρ 1) (ρ 2) (fun x => ρ 3 x*|x-a 3|)]
    simp only [hm,mul_one,one_mul]

private theorem p02_global_bounded_test_tendsto
    (ρ : ℕ → Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hi : ∀ n i, Integrable (ρ n i)) (hn : ∀ n i x, 0 ≤ ρ n i x)
    (hm : ∀ n i, (∫ x : ℝ, ρ n i x) = 1)
    (hd : ∀ n i, Integrable (fun x : ℝ => ρ n i x*|x-a i|))
    (ht : ∀ i, Tendsto (fun n => ∫ x : ℝ, ρ n i x*|x-a i|) atTop (𝓝 0))
    (F : P02ProfilePoint → ℝ) (hF : Continuous F)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ z, ‖F z‖ ≤ M) :
    Tendsto (fun n => profileProductAverage4 ρ n F) atTop
      (𝓝 (F (p02ProfilePoint a))) := by
  let D (n : ℕ) := p02ProfileDensity (ρ n)
  let S := fun z => p02DistanceSum z (p02ProfilePoint a)
  let m (n : ℕ) := ((∫ x : ℝ, ρ n 0 x*|x-a 0|)+(∫ x : ℝ, ρ n 1 x*|x-a 1|))+
    ((∫ x : ℝ, ρ n 2 x*|x-a 2|)+(∫ x : ℝ, ρ n 3 x*|x-a 3|))
  have hmt : Tendsto m atTop (𝓝 0) := by
    simpa only [add_zero] using ((ht 0).add (ht 1)).add ((ht 2).add (ht 3))
  have hD (n : ℕ) : Integrable (D n) ((volume.prod volume).prod (volume.prod volume)) :=
    p02ProfileDensity_integrable _ (hi n)
  have hDF (n : ℕ) : Integrable (fun z => D n z*F z)
      ((volume.prod volume).prod (volume.prod volume)) :=
    (hD n).mul_bdd hF.aestronglyMeasurable (ae_of_all _ hbound)
  have hDS (n : ℕ) : Integrable (fun z => D n z*S z)
      ((volume.prod volume).prod (volume.prod volume)) :=
    (p02ProfileDensity_distance (ρ n) a (hi n) (hd n) (hm n)).1
  have hDSm (n : ℕ) : (∫ z, D n z*S z
      ∂((volume.prod volume).prod (volume.prod volume))) = m n :=
    (p02ProfileDensity_distance (ρ n) a (hi n) (hd n) (hm n)).2
  have hmass (n : ℕ) : (∫ z, D n z
      ∂((volume.prod volume).prod (volume.prod volume))) = 1 :=
    p02ProfileDensity_mass _ (hm n)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousAt_iff.mp
    (hF.continuousAt : ContinuousAt F (p02ProfilePoint a)) (ε/2) (half_pos hε)
  let C : ℝ := (2*M)/δ
  have hC : 0 ≤ C := div_nonneg (by positivity) hδ.le
  have hpoint (z : P02ProfilePoint) :
      |F z-F (p02ProfilePoint a)| ≤ ε/2+C*S z := by
    by_cases hs : S z < δ
    · have hb := hnear ((p02DistanceSum_dist z (p02ProfilePoint a)).trans_lt hs)
      have hb' : |F z-F (p02ProfilePoint a)| < ε/2 := by
        simpa only [Real.dist_eq] using hb
      exact hb'.le.trans (le_add_of_nonneg_right (mul_nonneg hC (p02DistanceSum_nonneg _ _)))
    · have hs' : δ ≤ S z := le_of_not_gt hs
      have hab : |F z-F (p02ProfilePoint a)| ≤ 2*M := by
        calc
          _ ≤ |F z|+|F (p02ProfilePoint a)| := by simpa using abs_sub_le (F z) 0 (F (p02ProfilePoint a))
          _ ≤ M+M := add_le_add (hbound z) (hbound _)
          _ = _ := by ring
      have hcδ : C*δ = 2*M := by dsimp [C]; field_simp
      have hb := mul_le_mul_of_nonneg_left hs' hC
      rw [hcδ] at hb
      exact (hab.trans hb).trans (le_add_of_nonneg_left (half_pos hε).le)
  have hev : ∀ᶠ n : ℕ in atTop, C*m n < ε/2 := by
    have ht' : Tendsto (fun n => C*m n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hmt.const_mul C
    exact (tendsto_order.mp ht').2 _ (half_pos hε)
  filter_upwards [hev] with n hn'
  have hid : profileProductAverage4 ρ n F-F (p02ProfilePoint a) =
      ∫ z, D n z*(F z-F (p02ProfilePoint a))
      ∂((volume.prod volume).prod (volume.prod volume)) := by
    simp_rw [mul_sub]
    rw [integral_sub (hDF n) ((hD n).mul_const _),integral_mul_const,hmass]
    simp [profileProductAverage4,D]
  have hdom : Integrable (fun z => ε/2*D n z+C*(D n z*S z))
      ((volume.prod volume).prod (volume.prod volume)) :=
    ((hD n).const_mul _).add ((hDS n).const_mul C)
  have he := norm_integral_le_of_norm_le
    (f := fun z : P02ProfilePoint => D n z*(F z-F (p02ProfilePoint a)))
    hdom (ae_of_all _ (fun z => by
    have hp := p02ProfileDensity_nonneg (ρ n) (hn n) z
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ D n z*(ε/2+C*S z) := mul_le_mul_of_nonneg_left (hpoint z) hp
      _ = _ := by ring))
  rw [integral_add ((hD n).const_mul _) ((hDS n).const_mul C),
    integral_const_mul,integral_const_mul,hmass,hDSm,mul_one] at he
  rw [Real.dist_eq,hid]
  have he' : |∫ z, D n z*(F z-F (p02ProfilePoint a))
      ∂((volume.prod volume).prod (volume.prod volume))| ≤ ε/2+C*m n := by
    simpa only [Real.norm_eq_abs] using he
  exact he'.trans_lt (by linarith)

private def p02Clamp (L : ℝ) (z : P02ProfilePoint) : P02ProfilePoint :=
  ((min (max z.1.1 0) L,min (max z.1.2 0) L),
   (min (max z.2.1 0) L,min (max z.2.2 0) L))

private theorem p02Clamp_continuous (L : ℝ) : Continuous (p02Clamp L) := by
  unfold p02Clamp
  fun_prop

private theorem p02Clamp_mem {L : ℝ} (hL : 0 ≤ L) (z : P02ProfilePoint) :
    p02Clamp L z ∈ p02ProfileBox L := by
  have h (x : ℝ) : min (max x 0) L ∈ Icc 0 L :=
    ⟨le_min (le_max_right _ _) hL,min_le_right _ _⟩
  exact ⟨⟨h _,h _⟩,⟨h _,h _⟩⟩

private theorem p02Clamp_eq {L : ℝ} {z : P02ProfilePoint}
    (hz : z ∈ p02ProfileBox L) : p02Clamp L z = z := by
  rcases hz with ⟨⟨hx,hy⟩,⟨hv,hw⟩⟩
  simp only [p02Clamp,max_eq_left hx.1,min_eq_left hx.2,
    max_eq_left hy.1,min_eq_left hy.2,max_eq_left hv.1,min_eq_left hv.2,
    max_eq_left hw.1,min_eq_left hw.2,Prod.mk.eta]

private theorem p02ProfileDensity_support (L : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hs : ∀ i, Function.support (ρ i) ⊆ Icc 0 L) {z : P02ProfilePoint}
    (hz : p02ProfileDensity ρ z ≠ 0) : z ∈ p02ProfileBox L := by
  rcases mul_ne_zero_iff.mp hz with ⟨h01,h23⟩
  rcases mul_ne_zero_iff.mp h01 with ⟨h0,h1⟩
  rcases mul_ne_zero_iff.mp h23 with ⟨h2,h3⟩
  exact ⟨⟨hs 0 h0,hs 1 h1⟩,⟨hs 2 h2,hs 3 h3⟩⟩

/-- Multiplication by any continuous test on the common compact interval
preserves integrability of a supported scalar profile. -/
theorem p02_supported_test_integrable {L : ℝ} (hL : 0 ≤ L)
    (f g : ℝ → ℝ) (hf : Integrable f)
    (hs : Function.support f ⊆ Icc 0 L) (hg : ContinuousOn g (Icc 0 L)) :
    Integrable (fun x : ℝ => f x*g x) := by
  let G : ℝ → ℝ := fun x => g (min (max x 0) L)
  have hG : Continuous G := hg.comp_continuous
    ((continuous_id.max continuous_const).min continuous_const)
    (fun x => ⟨le_min (le_max_right _ _) hL,min_le_right _ _⟩)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hb (x : ℝ) : ‖G x‖ ≤ C :=
    hC _ ⟨le_min (le_max_right _ _) hL,min_le_right _ _⟩
  apply (hf.mul_bdd hG.aestronglyMeasurable (ae_of_all _ hb)).congr
  filter_upwards [] with x
  by_cases hx : f x=0
  · simp [hx]
  · have hm := hs hx
    simp [G,max_eq_left hm.1,min_eq_left hm.2]

/-- The actual four-profile weighted kernel is globally Lebesgue integrable,
even if its test function is only continuous on the common compact box. -/
theorem profileProductAverage4_integrable {L : ℝ} (hL : 0 ≤ L)
    (ρ : Fin 4 → ℝ → ℝ) (hi : ∀ i, Integrable (ρ i))
    (hs : ∀ i, Function.support (ρ i) ⊆ Icc 0 L)
    (F : P02ProfilePoint → ℝ) (hF : ContinuousOn F (p02ProfileBox L)) :
    Integrable (fun z => p02ProfileDensity ρ z*F z)
      ((volume.prod volume).prod (volume.prod volume)) := by
  let G : P02ProfilePoint → ℝ := fun z => F (p02Clamp L z)
  have hG : Continuous G := hF.comp_continuous (p02Clamp_continuous L) (p02Clamp_mem hL)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).prod
    (isCompact_Icc.prod isCompact_Icc) |>.exists_bound_of_continuousOn hF
  have hb (z : P02ProfilePoint) : ‖G z‖ ≤ C := hC _ (p02Clamp_mem hL z)
  apply ((p02ProfileDensity_integrable ρ hi).mul_bdd hG.aestronglyMeasurable
    (ae_of_all _ hb)).congr
  filter_upwards [] with z
  by_cases hz : p02ProfileDensity ρ z=0
  · simp [hz]
  · simp only [G,p02Clamp_eq (p02ProfileDensity_support L ρ hs hz)]

/-- Four independent compactly supported unit-mass profiles converge jointly
against every continuous test on their common compact box. The hypotheses
require only the four one-dimensional weak-convergence statements. -/
theorem profileProductAverage4_tendsto (L : ℝ)
    (ρ : ℕ → Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (ha : ∀ i, a i ∈ Icc 0 L)
    (hi : ∀ n i, Integrable (ρ n i))
    (hn : ∀ n i x, 0 ≤ ρ n i x)
    (hm : ∀ n i, (∫ x : ℝ, ρ n i x) = 1)
    (hs : ∀ n i, Function.support (ρ n i) ⊆ Icc 0 L)
    (hw : ∀ i (g : ℝ → ℝ), ContinuousOn g (Icc 0 L) →
      Tendsto (fun n => ∫ x : ℝ, g x*ρ n i x) atTop (𝓝 (g (a i))))
    (F : P02ProfilePoint → ℝ) (hF : ContinuousOn F (p02ProfileBox L)) :
    Tendsto (fun n => profileProductAverage4 ρ n F) atTop
      (𝓝 (F (p02ProfilePoint a))) := by
  have hL : 0 ≤ L := (ha 0).1.trans (ha 0).2
  let G : P02ProfilePoint → ℝ := fun z => F (p02Clamp L z)
  have hG : Continuous G := hF.comp_continuous (p02Clamp_continuous L) (p02Clamp_mem hL)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).prod
    (isCompact_Icc.prod isCompact_Icc) |>.exists_bound_of_continuousOn hF
  have hb (z : P02ProfilePoint) : ‖G z‖ ≤ max C 0 :=
    (hC _ (p02Clamp_mem hL z)).trans (le_max_left _ _)
  have hd (n : ℕ) (i : Fin 4) : Integrable (fun x : ℝ => ρ n i x*|x-a i|) :=
    p02_supported_test_integrable hL _ _ (hi n i) (hs n i)
      (by fun_prop)
  have ht (i : Fin 4) :
      Tendsto (fun n => ∫ x : ℝ, ρ n i x*|x-a i|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_comm] using
      hw i (fun x : ℝ => |x-a i|) (by fun_prop)
  have he (n : ℕ) : profileProductAverage4 ρ n G=profileProductAverage4 ρ n F := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : p02ProfileDensity (ρ n) z=0
    · simp [hz]
    · simp only [G,p02Clamp_eq (p02ProfileDensity_support L (ρ n) (hs n) hz)]
  have ham : p02ProfilePoint a ∈ p02ProfileBox L := ⟨⟨ha 0,ha 1⟩,⟨ha 2,ha 3⟩⟩
  have hea : G (p02ProfilePoint a)=F (p02ProfilePoint a) := by
    simp only [G,p02Clamp_eq ham]
  simpa only [he,hea] using p02_global_bounded_test_tendsto ρ a hi hn hm hd ht
    G hG (max C 0) (le_max_right _ _) hb

/-- Fubini expands the genuinely integrable four-profile product-space
integral into its four ordinary one-dimensional Lebesgue integrals. -/
theorem profileProductAverage4_fubini {L : ℝ} (hL : 0 ≤ L)
    (ρ : ℕ → Fin 4 → ℝ → ℝ) (n : ℕ)
    (hi : ∀ i, Integrable (ρ n i))
    (hs : ∀ i, Function.support (ρ n i) ⊆ Icc 0 L)
    (F : P02ProfilePoint → ℝ) (hF : ContinuousOn F (p02ProfileBox L)) :
    profileProductAverage4 ρ n F =
      ∫ x : ℝ, ∫ y : ℝ, ∫ v : ℝ, ∫ w : ℝ,
        (ρ n 0 x*ρ n 1 y)*(ρ n 2 v*ρ n 3 w)*F ((x,y),(v,w)) := by
  let f : P02ProfilePoint → ℝ := fun z => p02ProfileDensity (ρ n) z*F z
  have hf : Integrable f ((volume.prod volume).prod (volume.prod volume)) :=
    profileProductAverage4_integrable hL (ρ n) hi hs F hF
  let G : ℝ×ℝ → ℝ := fun u => ∫ v : ℝ, ∫ w : ℝ, f (u,(v,w))
  have he : (fun u : ℝ×ℝ => ∫ z : ℝ×ℝ, f (u,z) ∂volume.prod volume) =ᵐ[
      volume.prod volume] G := by
    filter_upwards [hf.prod_right_ae] with u hu
    exact integral_prod _ hu
  have hG : Integrable G (volume.prod volume) := hf.integral_prod_left.congr he
  calc
    profileProductAverage4 ρ n F = ∫ u : ℝ×ℝ,
        ∫ z : ℝ×ℝ, f (u,z) ∂volume.prod volume ∂volume.prod volume :=
      integral_prod f hf
    _ = ∫ u : ℝ×ℝ, G u ∂volume.prod volume := integral_congr_ae he
    _ = ∫ x : ℝ, ∫ y : ℝ, G (x,y) := integral_prod G hG
    _ = _ := rfl

/-- The same joint limit for the literal four iterated scalar integrals. -/
theorem profileProductIntegral4_tendsto (L : ℝ)
    (ρ : ℕ → Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (ha : ∀ i, a i ∈ Icc 0 L)
    (hi : ∀ n i, Integrable (ρ n i))
    (hn : ∀ n i x, 0 ≤ ρ n i x)
    (hm : ∀ n i, (∫ x : ℝ, ρ n i x) = 1)
    (hs : ∀ n i, Function.support (ρ n i) ⊆ Icc 0 L)
    (hw : ∀ i (g : ℝ → ℝ), ContinuousOn g (Icc 0 L) →
      Tendsto (fun n => ∫ x : ℝ, g x*ρ n i x) atTop (𝓝 (g (a i))))
    (F : P02ProfilePoint → ℝ) (hF : ContinuousOn F (p02ProfileBox L)) :
    Tendsto (fun n => ∫ x : ℝ, ∫ y : ℝ, ∫ v : ℝ, ∫ w : ℝ,
        (ρ n 0 x*ρ n 1 y)*(ρ n 2 v*ρ n 3 w)*F ((x,y),(v,w))) atTop
      (𝓝 (F (p02ProfilePoint a))) := by
  have hL : 0 ≤ L := (ha 0).1.trans (ha 0).2
  have he (n : ℕ) := profileProductAverage4_fubini hL ρ n (hi n) (hs n) F hF
  simpa only [he] using profileProductAverage4_tendsto L ρ a ha hi hn hm hs hw F hF

end
end Sechstmoment

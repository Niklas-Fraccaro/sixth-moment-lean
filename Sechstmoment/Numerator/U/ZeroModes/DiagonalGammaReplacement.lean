import Sechstmoment.Numerator.U.Sources.FiniteGammaDiagonalSplit
import Sechstmoment.Numerator.U.ZeroModes.Transforms.DiagonalSmallLineMass

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03DiagonalReplacementKernel (dual : Bool) (T : ℝ) (σ α : MomentShifts)
    (t : ℝ) (n : Fin 4→ℕ) (z : ℂ) : ℂ :=
  if dual then rectangularDualReplacementMellinKernel T σ (polarPoleKiller T σ) α t n z
  else rectangularWeightReplacementMellinKernel (polarPoleKiller T σ) α t n z

def a03ActualFiniteDiagonalStarMellinGrid (dual : Bool) (c T a b u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if diagonalQuadRelation (p+1) (q+1) n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          (if dual then bblrDualLeadingMultiplier T σ (t/T) else 1)*
          rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0

def a03ActualFiniteDiagonalStarMoment (dual : Bool) (c T a b u θ : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualFiniteDiagonalStarMellinGrid dual c T a b u v f g Φ σ (a03SourceShifts dual T σ)

def a03ActualFiniteDiagonalReplacementMellinGrid (dual : Bool) (c T a b u v : ℝ)
    (f g Φ : ℝ→ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
      if diagonalQuadRelation (p+1) (q+1) n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ p q t*
          a03DiagonalReplacementKernel dual T σ α t n ((c:ℂ)+(v:ℂ)*I)) else 0

theorem a03DiagonalReplacementKernel_continuousOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (n : Fin 4→ℕ) (R : ℝ) :
    ContinuousOn (fun p : ℝ×ℝ => a03DiagonalReplacementKernel dual T σ α p.2 n
      ((c:ℂ)+(p.1:ℂ)*I)) (Icc (-R) R ×ˢ Icc T (2*T)) := by
  cases dual
  · exact rectangular_weight_replacement_Mellin_kernel_continuousOn hc hT σ α hα n R
  · exact rectangular_dual_replacement_Mellin_kernel_continuousOn hc hT σ σ α hσ hα n R

theorem a03DiagonalReplacementKernel_weighted_eq {T : ℝ} (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℕ) (n : Fin 4→ℕ) (z : ℂ) (t : ℝ) :
    rectangularMomentPairWeight T f g Φ p q t*a03DiagonalReplacementKernel dual T σ α t n z=
      rectangularMomentPairWeight T f g Φ p q t*(if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n z-
      rectangularMomentPairWeight T f g Φ p q t*(if dual then bblrDualLeadingMultiplier T σ (t/T) else 1)*
        rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α t n z := by
  by_cases ht : t∈Icc T (2*T)
  · have htp := hT.trans_le ht.1
    cases dual
    · simp only [a03DiagonalReplacementKernel,Bool.false_eq_true,ite_false,mul_one]
      rw [rectangularWeightReplacementMellinKernel_eq_actual_sub_star _ _ htp]
      ring
    · simp only [a03DiagonalReplacementKernel,ite_true]
      rw [rectangularDualReplacementMellinKernel_eq_actual_sub_leading_star _ _ _ _ htp,
        bblrDualLeadingMultiplier_time_eq hT.ne']
      ring
  · rw [a03_pair_weight_zero_outside hT f g Φ hΦ p q t ht]
    simp

theorem a03PairWeighted_time_integrable {T : ℝ} (hT : 0<T)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) (p q : ℕ)
    (K : ℝ→ℂ) (hK : ContinuousOn K (Icc T (2*T))) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ p q t*K t) := by
  have hi : IntegrableOn (fun t : ℝ => rectangularMomentPairWeight T f g Φ p q t*K t)
      (Icc T (2*T)) :=
    ((rectangular_moment_pair_weight_continuous T f g Φ hΦ p q).continuousOn.mul hK).integrableOn_compact isCompact_Icc
  exact hi.integrable_of_forall_notMem_eq_zero (by
    intro t ht
    simp [a03_pair_weight_zero_outside hT f g Φ hΦ p q t ht])

theorem a03DiagonalReplacementKernel_time_integrable {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℕ) (n : Fin 4→ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ p q t*
      a03DiagonalReplacementKernel dual T σ α t n ((c:ℂ)+(v:ℂ)*I)) := by
  let K : ℝ×ℝ→ℂ := fun w => a03DiagonalReplacementKernel dual T σ α w.2 n ((c:ℂ)+(w.1:ℂ)*I)
  have hk : ContinuousOn K (Icc (-|v|) |v| ×ˢ Icc T (2*T)) :=
    a03DiagonalReplacementKernel_continuousOn hc hT dual σ α hσ hα n (|v|)
  have hcomp : ContinuousOn (fun t : ℝ => K (v,t)) (Icc T (2*T)) :=
    hk.comp (f:=fun t : ℝ => (v,t)) (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨⟨neg_abs_le v,le_abs_self v⟩,ht⟩)
  exact a03PairWeighted_time_integrable hT f g Φ hΦ p q (fun t => K (v,t)) hcomp

theorem a03DiagonalReplacementMellinGrid_integrableOn {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (a b u R : ℝ) (σ α : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j,‖α j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    IntegrableOn (fun v : ℝ => a03ActualFiniteDiagonalReplacementMellinGrid dual c T a b u v f g Φ σ α)
      (Icc (-R) R) := by
  unfold a03ActualFiniteDiagonalReplacementMellinGrid
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro n _
  by_cases hn : diagonalQuadRelation (p+1) (q+1) n
  · simp only [hn,ite_true]
    exact (a03_pair_compact_time_contour_integrable hT f g Φ hΦ p q R
      (fun w => a03DiagonalReplacementKernel dual T σ α w.2 n ((c:ℂ)+(w.1:ℂ)*I))
      (a03DiagonalReplacementKernel_continuousOn hc hT dual σ α hσ hα n R)).integral_prod_left.const_mul _
  · simp only [hn,ite_false]
    exact integrable_zero _ _ _

theorem a03DiagonalGammaKernel_time_integrable {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℕ) (n : Fin 4→ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ p q t*
      (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  have hK := (a03FiniteGammaWeightedKernel_continuous hc dual σ α hσ hα n).comp
    (f:=fun t : ℝ => (v,t)) (continuous_const.prodMk continuous_id)
  convert a03PairWeighted_time_integrable hT f g Φ hΦ p q _ hK.continuousOn using 1
  funext t
  simp only [mul_assoc,Function.comp_apply]

theorem a03DiagonalStarKernel_time_integrable {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (σ α : MomentShifts) (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4)
    (hα : ∀ j,‖α j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℕ) (n : Fin 4→ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ p q t*
      (if dual then bblrDualLeadingMultiplier T σ (t/T) else 1)*
      rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) := by
  apply ((a03DiagonalGammaKernel_time_integrable hc hT dual σ α hσ hα f g Φ hΦ p q n v).sub
    (a03DiagonalReplacementKernel_time_integrable hc hT dual σ α hσ hα f g Φ hΦ p q n v)).congr
  apply ae_of_all
  intro t
  dsimp only [Pi.sub_apply]
  rw [a03DiagonalReplacementKernel_weighted_eq hT dual σ α f g Φ hΦ]
  ring

theorem a03DiagonalGammaMellinGrid_sub_Star_eq_replacement {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (a b u v : ℝ) (σ α : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (hα : ∀ j,‖α j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    a03ActualFiniteDiagonalMellinGrid dual c T a b u v f g Φ σ α-
      a03ActualFiniteDiagonalStarMellinGrid dual c T a b u v f g Φ σ α=
      a03ActualFiniteDiagonalReplacementMellinGrid dual c T a b u v f g Φ σ α := by
  unfold a03ActualFiniteDiagonalMellinGrid a03ActualFiniteDiagonalStarMellinGrid
    a03ActualFiniteDiagonalReplacementMellinGrid
  simp_rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : diagonalQuadRelation (p+1) (q+1) n
  · simp only [hn,ite_true]
    rw [←mul_sub,←integral_sub
      (a03DiagonalGammaKernel_time_integrable hc hT dual σ α hσ hα f g Φ hΦ p q n v)
      (a03DiagonalStarKernel_time_integrable hc hT dual σ α hσ hα f g Φ hΦ p q n v)]
    congr 1
    exact integral_congr_ae (ae_of_all _ (fun t =>
      (a03DiagonalReplacementKernel_weighted_eq hT dual σ α f g Φ hΦ p q n _ t).symm))
  · simp only [hn,ite_false,sub_self]

theorem a03DiagonalGammaMoment_sub_Star_eq_replacement {c T : ℝ} (hc : 0<c) (hT : 0<T)
    (dual : Bool) (a b u θ : ℝ) (σ : MomentShifts)
    (hσ : ∀ j,‖rawMomentShifts T σ j‖≤1/4) (f g Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
      a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ=
      (1/(2*Real.pi):ℂ)*∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
        a03ActualFiniteDiagonalReplacementMellinGrid dual c T a b u v f g Φ σ (a03SourceShifts dual T σ) := by
  have hα : ∀ j,‖a03SourceShifts dual T σ j‖≤1/4 := by
    cases dual
    · exact hσ
    · exact bblrSixShifts_norm_le _ hσ 1
  have he (v : ℝ) := a03DiagonalGammaMellinGrid_sub_Star_eq_replacement hc hT dual a b u v
    σ _ hσ hα f g Φ hΦ
  have hg := a03ActualFiniteDiagonalMellinGrid_integrableOn hc hT dual a b u (θ*Real.log T)
    σ _ hσ hα f g Φ hΦ
  have hr := a03DiagonalReplacementMellinGrid_integrableOn hc hT dual a b u (θ*Real.log T)
    σ _ hσ hα f g Φ hΦ
  have hs : IntegrableOn (fun v : ℝ => a03ActualFiniteDiagonalStarMellinGrid dual c T a b u v f g Φ σ
      (a03SourceShifts dual T σ)) (Icc (-(θ*Real.log T)) (θ*Real.log T)) := by
    apply (hg.sub hr).congr
    apply ae_of_all
    intro v
    dsimp only [Pi.sub_apply]
    rw [←he v]
    ring
  unfold a03ActualFiniteDiagonalGammaMoment a03ActualFiniteDiagonalStarMoment
  simp only [neg_mul]
  rw [←mul_sub,←integral_sub hg hs]
  congr 1
  exact integral_congr_ae (ae_of_all _ he)

theorem a03DiagonalReplacementKernel_uniform_smallLine_bound
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) → (∀ j,‖α j‖≤c/4) →
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ F G : ℝ,0≤F → 0≤G → ∀ f g : ℝ→ℝ,
      (∀ x,‖f x‖≤F) → (∀ x,‖g x‖≤G) → ∀ dual : Bool,∀ p q : ℕ,∀ n : Fin 4→ℕ,
      ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
          a03DiagonalReplacementKernel dual T σ α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        F*G*C*T^ε*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ))*a03DiagonalQuadSmallMajorant c n := by
  obtain ⟨B,hB,hb⟩ := rectangular_weight_replacement_actual_time_uniform_schwartz_bound hΦ hc hc1 hε hκ hθ
  obtain ⟨D,hD,hd⟩ := rectangular_dual_replacement_actual_time_uniform_schwartz_bound hΦ hc hc1 hε hκ hθ hR
  refine ⟨B 0+D 0,add_nonneg (hB 0) (hD 0),?_⟩
  filter_upwards [hb,hd,eventually_ge_atTop (0:ℝ)] with T hb hd hT
  intro σ α hσ hα hαc hroot v hv F G hF hG f g hf hg dual p q n
  have hBD : 0≤B 0+D 0 := add_nonneg (hB 0) (hD 0)
  have hpair : ‖phaseActualAmplifierPairConstant T f g p q‖≤
      F*G*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ)) := by
    unfold phaseActualAmplifierPairConstant
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      show (p+1:ℂ)=((p+1:ℝ):ℂ) by push_cast; rfl,
      show (q+1:ℂ)=((q+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num only [Complex.neg_re,Complex.div_ofNat_re,Complex.one_re]
    gcongr
    · exact hf _
    · exact hg _
  have hstatic : ‖phaseActualAmplifierPairConstant T f g p q/
      ∏ j : Fin 4,(n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖≤
      (F*G*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ)))*a03DiagonalQuadSmallMajorant c n := by
    rw [div_eq_mul_inv,norm_mul]
    exact mul_le_mul hpair (by simpa only [one_div] using a03DiagonalSmallLine_denominator_norm_bound hc α hαc v n)
      (norm_nonneg _) (by positivity)
  have hk : ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
      a03DiagonalReplacementKernel dual T σ α t n ((c:ℂ)+(v:ℂ)*I)‖≤
      ‖phaseActualAmplifierPairConstant T f g p q/
        ∏ j : Fin 4,(n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖*(B 0+D 0)*T^ε := by
    cases dual
    · have h0 := hb σ α hα hroot v hv f g p q n 0
      simp only [pow_zero,one_mul] at h0
      exact h0.trans (by gcongr; exact le_add_of_nonneg_right (hD 0))
    · have h0 := hd σ σ α hσ hα hroot v hv f g p q n 0
      simp only [pow_zero,one_mul] at h0
      exact h0.trans (by gcongr; exact le_add_of_nonneg_left (hB 0))
  calc
    _≤((F*G*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ)))*a03DiagonalQuadSmallMajorant c n)*(B 0+D 0)*T^ε := by
      exact hk.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hstatic hBD) (Real.rpow_nonneg hT ε))
    _=_ := by ring

private theorem a03InvSqrt_range_sum {T : ℝ} (hT : 0<T) (a : ℝ) :
    (∑ p∈Finset.range ⌊T^a⌋₊,(p+1:ℝ)^(-(1/2:ℝ)))≤2*T^(a/2) := by
  have he (N : ℕ) : (∑ p∈Finset.range N,(p+1:ℝ)^(-(1/2:ℝ)))=
      ∑ n∈Finset.Icc 1 N,(n:ℝ)^(-(1/2:ℝ)) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]; push_cast; rfl
  rw [he]
  exact a03PositiveInteger_invSqrt_sum_floor_le hT a

theorem a03DiagonalReplacementMellinGrid_uniform_power_bound
    {a b c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual : Bool,
      ‖a03ActualFiniteDiagonalReplacementMellinGrid dual c T a b u v f g Φ σ
        (a03SourceShifts dual T σ)‖≤C*T^(ε+(a+b)/2) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨B,hB,hkernel⟩ := a03DiagonalReplacementKernel_uniform_smallLine_bound hc hc1 hε hκ hθ hR Φ hΦ
  obtain ⟨D,hD,hmass⟩ := a03DiagonalSmallLine_smooth_grid_mass_bound hc
  refine ⟨4*F*G*B*D,by positivity,?_⟩
  filter_upwards [hkernel,rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    rawMomentShifts_uniform_eventually_small hR (show 0<c/4 by linarith),eventually_gt_atTop (0:ℝ)]
    with T hk hs hcS hT
  intro σ hσ hroot v hv dual
  let α := a03SourceShifts dual T σ
  have hα : ∀ j,‖α j‖≤1/4 := by
    cases dual
    · exact hs σ hσ
    · exact bblrSixShifts_norm_le _ (hs σ hσ) 1
  have hαc : ∀ j,‖α j‖≤c/4 := by
    cases dual
    · exact hcS σ hσ
    · exact bblrSixShifts_norm_le _ (hcS σ hσ) 1
  let L : ℝ := F*G*B*T^ε
  have hL : 0≤L := by dsimp [L]; positivity
  have hpq (p q : ℕ) :
      ‖∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
        if diagonalQuadRelation (p+1) (q+1) n then
          (rectangularAFESmoothWeight k n:ℂ)*(∫t:ℝ,rectangularMomentPairWeight T f g Φ p q t*
            a03DiagonalReplacementKernel dual T σ α t n ((c:ℂ)+(v:ℂ)*I)) else 0‖≤
      L*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ))*D := by
    let Q : ℝ := L*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ))
    have hQ : 0≤Q := by dsimp [Q]; positivity
    calc
      _≤∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
        Q*(rectangularAFESmoothWeight k n*(if diagonalQuadRelation (p+1) (q+1) n then
          a03DiagonalQuadSmallMajorant c n else 0)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : diagonalQuadRelation (p+1) (q+1) n
        · simp only [hn,ite_true,norm_mul,Complex.norm_real,
            Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
          calc
            _≤rectangularAFESmoothWeight k n*(Q*a03DiagonalQuadSmallMajorant c n) :=
              mul_le_mul_of_nonneg_left (hk σ α hσ hα hαc hroot v hv F G hF hG f g hfb hgb dual p q n)
                (rectangular_AFE_smooth_weight_nonneg k n)
            _=_ := by ring
        · simp only [hn,ite_false,norm_zero,mul_zero]
          exact le_rfl
      _=Q*(∑ k∈rectangularAFEProductScaleGrid (T^(2+u)),∑ n∈rectangularAFESmoothBox k,
        rectangularAFESmoothWeight k n*(if diagonalQuadRelation (p+1) (q+1) n then
          a03DiagonalQuadSmallMajorant c n else 0)) := by simp only [Finset.mul_sum]
      _≤Q*D := mul_le_mul_of_nonneg_left (hmass (p+1) (q+1) (by omega) (by omega) _) hQ
  unfold a03ActualFiniteDiagonalReplacementMellinGrid
  calc
    _≤∑ p∈Finset.range ⌊T^a⌋₊,∑ q∈Finset.range ⌊T^b⌋₊,
      L*(p+1:ℝ)^(-(1/2:ℝ))*(q+1:ℝ)^(-(1/2:ℝ))*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => hpq p q))
    _=(L*D)*(∑p∈Finset.range ⌊T^a⌋₊,(p+1:ℝ)^(-(1/2:ℝ)))*
        (∑q∈Finset.range ⌊T^b⌋₊,(q+1:ℝ)^(-(1/2:ℝ))) := by
      simp only [←Finset.sum_mul,←Finset.mul_sum]
      ring
    _≤(L*D)*(2*T^(a/2))*(2*T^(b/2)) := by
      gcongr
      · exact a03InvSqrt_range_sum hT a
      · exact a03InvSqrt_range_sum hT b
    _=_ := by
      dsimp [L]
      rw [show ε+(a+b)/2=ε+a/2+b/2 by ring,Real.rpow_add hT,Real.rpow_add hT]
      ring

theorem a03DiagonalGammaMoment_sub_Star_uniform_polylog_bound
    {a b c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) → ∀ dual : Bool,
      ‖a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ‖≤
        C*Real.log T*T^(ε+(a+b)/2) := by
  obtain ⟨B,hB,hgrid⟩ := a03DiagonalReplacementMellinGrid_uniform_power_bound hc hc1 hε hκ hθ hR f g Φ hf hg hΦ
  refine ⟨(1/(2*Real.pi))*B*(2*θ),by positivity,?_⟩
  filter_upwards [hgrid,eventually_gt_atTop (1:ℝ),rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)]
    with T hgrid hT hraw
  intro σ hσ hroot dual
  have hTp : 0<T := zero_lt_one.trans hT
  have hlog : 0≤Real.log T := (Real.log_pos hT).le
  rw [a03DiagonalGammaMoment_sub_Star_eq_replacement hc hTp dual a b u θ σ (hraw σ hσ) f g Φ hΦ,norm_mul]
  have hp : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    rw [norm_div,norm_one,norm_mul]
    norm_num only [Complex.norm_ofNat]
    rw [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hp]
  have hi := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ:=volume) (a:= -θ*Real.log T) (b:=θ*Real.log T))
    (fun v hv => hgrid σ hσ hroot v (by
      rw [abs_le]
      exact ⟨by simpa only [neg_mul] using hv.1,hv.2⟩) dual)
  have hv : volume.real (Icc (-θ*Real.log T) (θ*Real.log T))=2*θ*Real.log T := by
    rw [Real.volume_real_Icc]
    rw [show θ*Real.log T-(-θ*Real.log T)=2*θ*Real.log T by ring,max_eq_left (by positivity : 0≤2*θ*Real.log T)]
  rw [hv] at hi
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

theorem a03DiagonalGammaMoment_sub_Star_uniform_oT
    {a b c ε κ θ R u : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hbudget : ε+(a+b)/2<1)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ η : ℝ,0<η → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) → ∀ dual : Bool,
      ‖a03ActualFiniteDiagonalGammaMoment dual c T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual c T a b u θ σ f g Φ‖≤η*T := by
  obtain ⟨C,hC,hbound⟩ := a03DiagonalGammaMoment_sub_Star_uniform_polylog_bound hc hc1 hε hκ hθ hR f g Φ hf hg hΦ
  have ho := (polylog_mul_rpow_isLittleO_id 1 hbudget).const_mul_left C
  intro η hη
  filter_upwards [hbound,ho.bound hη,eventually_gt_atTop (1:ℝ)] with T hbound ho hT
  intro σ hσ hroot dual
  apply (hbound σ hσ hroot dual).trans
  have hL : 0≤Real.log T := (Real.log_pos hT).le
  have hn : 0≤C*(Real.log T*T^(ε+(a+b)/2)) := by positivity
  simpa only [pow_one,mul_assoc,Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos (zero_lt_one.trans hT)] using ho

theorem a03DiagonalGammaMoment_sub_Star_uniform_oT_of_source
    {a b κ θ R u : ℝ} (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    ∀ η : ℝ,0<η → ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) → ∀ dual : Bool,
      ‖a03ActualFiniteDiagonalGammaMoment dual (rectangularSlack a b/128) T a b u θ σ f g Φ-
        a03ActualFiniteDiagonalStarMoment dual (rectangularSlack a b/128) T a b u θ σ f g Φ‖≤η*T := by
  have hd := (rectangular_slack_bounds hab hrect).1
  apply a03DiagonalGammaMoment_sub_Star_uniform_oT (ε:=rectangularSlack a b/16)
    (by positivity) (by dsimp [rectangularSlack]; linarith)
    (by linarith) hκ hθ hR
  · dsimp [rectangularSlack]
    linarith
  · exact hf
  · exact hg
  · exact hΦ

end
end Sechstmoment

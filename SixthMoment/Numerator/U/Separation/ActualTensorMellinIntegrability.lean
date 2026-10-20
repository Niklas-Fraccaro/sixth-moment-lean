import SixthMoment.Numerator.U.Separation.ActualTensorMellinMeasurability

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_mellin_integrableOn_Icc_of_bound (F : ℝ→ℂ)
    (hF : StronglyMeasurable F) {C l u : ℝ} (hC : 0≤C)
    (hbound : ∀ v∈Icc l u, ‖F v‖≤C) : IntegrableOn F (Icc l u) := by
  have hc : IntegrableOn (fun _ : ℝ => C) (Icc l u) := integrableOn_const measure_Icc_lt_top.ne
  apply Integrable.mono hc hF.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  rw [Real.norm_of_nonneg hC]
  exact hbound v hv

private theorem a03SixZeroSmoothProduct_eq (m n : Bool) (q : QuadraticScales)
    (w : Fin 5→ℕ) (x : ℝ) :
    (∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))=
      ∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularZeroArguments q w x j):ℂ) := by
  cases m <;> cases n <;>
    simp [a03SixZeroSourceArguments,a03SixZeroPairArguments,Fin.prod_univ_five,
      mul_comm,mul_left_comm,mul_assoc]

theorem a03SixTensorPhysicalZeroMode_mellin_integrableOn_of_cutoff_bound
    (F : ℝ→A03SixTensorSpace→ℂ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2))
    {C l u : ℝ} (hC : 0≤C)
    (hbound : ∀ v∈Icc l u, ∀ y, ‖a03TensorLogCutoff y*F v y‖≤C)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (hM₂ : 0<q.M₂) (α β : ℕ→ℂ)
    (hβ : ∀ b : ℕ,(b:ℝ)∉Icc q.B (2*q.B) → β b=0) :
    IntegrableOn (fun v : ℝ => a03SixTensorPhysicalZeroMode (F v) m n q α β) (Icc l u) := by
  let G := fun v y => a03TensorLogCutoff y*F v y
  have hG : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => G p.1 p.2) :=
    (a03TensorLogCutoff_contDiff.continuous.comp continuous_snd).stronglyMeasurable.mul hF
  have hterm (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) :
      Integrable (fun v : ℝ => ∫ x : ℝ in Ioi 0,
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))*
          G v (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)))
        (volume.restrict (Icc l u)) := by
    let d : ℝ := Nat.gcd (w 0*w 2) (w 1*w 3)
    let P : ℝ := (w 1:ℝ)*(w 3:ℝ)
    let L : ℝ := 2*d*q.M₂/P
    have hwpos (j : Fin 5) : 0<(w j:ℝ) := by
      have hj := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
      exact_mod_cast (show 0<w j by omega)
    have hd : 0<d := by
      dsimp [d]
      exact_mod_cast Nat.gcd_pos_of_pos_left (w 1*w 3)
        (mul_pos (show 0<w 0 by exact_mod_cast hwpos 0) (show 0<w 2 by exact_mod_cast hwpos 2))
    have hP : 0<P := mul_pos (hwpos 1) (hwpos 3)
    have hden : 0<d*q.M₂ := mul_pos hd hM₂
    have hzero (x : ℝ) (hx : x∉Icc 0 L) :
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))=0 := by
      rw [a03SixZeroSmoothProduct_eq]
      apply Finset.prod_eq_zero (Finset.mem_univ (2:Fin 5))
      apply Complex.ofReal_eq_zero.mpr
      by_contra hn
      have hs := rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hn)
      have harg : rectangularZeroArguments q w x 2=P*x/(d*q.M₂) := by
        simp [rectangularZeroArguments,P,d]
      rw [harg] at hs
      have hlo := (le_div_iff₀ hden).mp hs.1
      have hhi := (div_le_iff₀ hden).mp hs.2
      apply hx
      constructor
      · by_contra hxneg
        have hneg : P*x<0 := mul_neg_of_pos_of_neg hP (lt_of_not_ge hxneg)
        linarith
      · dsimp [L]
        apply (le_div_iff₀ hP).mpr
        nlinarith only [hhi]
    have hpbound (x : ℝ) :
        ‖∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ)‖≤1 := by
      rw [norm_prod]
      calc
        _≤∏ _j : Fin 5, (1:ℝ) := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro j _
          simpa only [Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (rectangularSmoothBlockWeight_nonneg _)] using
            rectangularSmoothBlockWeight_le_one (a03SixZeroSourceArguments m n q w x j.succ)
        _=1 := by simp
    have hargs := a03SixZeroSourceArguments_continuous m n q w
    have hy : Measurable (fun x : ℝ => a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)) :=
      a03SixTensorLogPoint_measurable.comp hargs.measurable
    have hGm := hG.comp_measurable (measurable_fst.prodMk (hy.comp measurable_snd))
    have hweight : Continuous (fun p : ℝ×ℝ => ∏ j : Fin 5,
        (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w p.2 j.succ):ℂ)) := by
      apply continuous_finsetProd
      intro j _
      exact Complex.continuous_ofReal.comp ((rectangularSmoothBlockWeight_contDiff.continuous).comp
        ((continuous_apply j.succ).comp (hargs.comp continuous_snd)))
    have hmeas : AEStronglyMeasurable (fun p : ℝ×ℝ =>
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w p.2 j.succ):ℂ))*
          G p.1 (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w p.2)))
        ((volume.restrict (Icc l u)).prod (volume.restrict (Ioi 0))) :=
      (hweight.stronglyMeasurable.mul hGm).aestronglyMeasurable
    have hc : Integrable (fun _v : ℝ => C) (volume.restrict (Icc l u)) :=
      integrableOn_const measure_Icc_lt_top.ne
    have hind : Integrable ((Icc 0 L).indicator (fun _x : ℝ => (1:ℝ)))
        (volume.restrict (Ioi 0)) := by
      apply Integrable.restrict
      exact (integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const measure_Icc_lt_top.ne)
    have hmajor := hc.mul_prod hind
    have hJ : Integrable (fun p : ℝ×ℝ =>
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w p.2 j.succ):ℂ))*
          G p.1 (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w p.2)))
        ((volume.restrict (Icc l u)).prod (volume.restrict (Ioi 0))) := by
      apply hmajor.mono hmeas
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
      by_cases hx : p.2∈Icc 0 L
      · simp only [indicator_of_mem hx,mul_one]
        rw [Real.norm_of_nonneg hC,norm_mul]
        exact (mul_le_mul (hpbound p.2) (hbound p.1 hp.1 _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
      · simp only [indicator_of_notMem hx,hzero p.2 hx,zero_mul,mul_zero,norm_zero]
        exact le_rfl
    exact hJ.integral_prod_left
  have hi : IntegrableOn (fun v : ℝ => a03SixTensorPhysicalZeroMode (G v) m n q α β) (Icc l u) := by
    unfold a03SixTensorPhysicalZeroMode
    exact integrable_finsetSum _ (fun w hw => (hterm w hw).const_mul _)
  apply hi.congr
  apply ae_of_all
  intro v
  exact a03SixTensorPhysicalZeroMode_congr_on_dyadic_box (G v) (F v) m n q hB α β hβ
    (fun x hx => by dsimp [G]; rw [a03TensorLogCutoff_logPoint_one hx,one_mul])

theorem a03EndpointPhysicalSortedZeroMode_mellin_integrableOn_of_cutoff_bound
    (F : ℝ→A03SixTensorSpace→ℂ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace => F p.1 p.2))
    {C l u : ℝ} (hC : 0≤C)
    (hbound : ∀ v∈Icc l u, ∀ y, ‖a03TensorLogCutoff y*F v y‖≤C)
    (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode (F v) T A B H f g k) (Icc l u) := by
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  have hq := boundaryActual_scales_pos A B H k hA hB hH
  have hM₁ : 0<q.M₁ := by simpa [q,QuadraticScales.size] using hq 2
  have hM₂ : 0<q.M₂ := by simpa [q,QuadraticScales.size] using hq 3
  have hsortedM : 0<(phasePairSwapScales m n q).M₂ := by
    dsimp [phasePairSwapScales]
    split_ifs
    · exact hM₁
    · exact hM₂
  exact a03SixTensorPhysicalZeroMode_mellin_integrableOn_of_cutoff_bound F hF hC hbound
    m n (phasePairSwapScales m n q) hB hsortedM
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (phaseActualAmplifierCoefficient_support T g hB)

theorem a03EndpointPhysicalTensorSum_mellin_integrableOn_of_cutoff_bound
    (F : A03NearTensorData→A03SixTensorSpace→ℂ)
    (positive : Bool) (T A B H : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hF : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      F (phaseActualNearTensorData T σ α p.1 A B H k positive) p.2))
    {C l u : ℝ} (hC : 0≤C)
    (hbound : ∀ v∈Icc l u, ∀ y,
      ‖a03TensorLogCutoff y*F (phaseActualNearTensorData T σ α v A B H k positive) y‖≤C) :
    IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum F positive T A B H σ α v f g k) (Icc l u) := by
  let q := phaseActualScales A B H k
  let W := fun n : Fin 7→ℕ => phaseActualAmplifierCoefficient T f A (n 0)*
    phaseActualAmplifierCoefficient T g B (n 1)*
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j):ℂ))
  have hβ : ∀ b, phaseActualAmplifierCoefficient T g B b≠0 →
      rectangularSmoothBlockWeight ((b:ℝ)/q.B)≠0 := by
    intro b hb hz
    apply hb
    change rectangularSmoothBlockWeight ((b:ℝ)/B)=0 at hz
    simp only [phaseActualAmplifierCoefficient,hz,Complex.ofReal_zero,zero_mul]
  have hi : IntegrableOn (fun v : ℝ => ∑ n∈quadraticIndexSet q,
      if signedQuadraticRelation positive n then W n*
        F (phaseActualNearTensorData T σ α v A B H k positive)
          (a03SixTensorLogPoint (a03SixSourceArguments q n)) else 0) (Icc l u) := by
    apply integrable_finsetSum
    intro n _
    by_cases hr : signedQuadraticRelation positive n
    · simp only [hr,ite_true]
      have hn : StronglyMeasurable (fun v : ℝ => W n*
          F (phaseActualNearTensorData T σ α v A B H k positive)
            (a03SixTensorLogPoint (a03SixSourceArguments q n))) :=
        (hF.comp_measurable (measurable_id.prodMk measurable_const)).const_mul (W n)
      apply a03_mellin_integrableOn_Icc_of_bound _ hn (mul_nonneg (norm_nonneg (W n)) hC)
      intro v hv
      have he := a03_tensor_cutoff_source_summand q n
        (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
        (F (phaseActualNearTensorData T σ α v A B H k positive)) hβ
      change W n*(a03TensorLogCutoff _*F _ _)=W n*F _ _ at he
      rw [←he,norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound v hv _) (norm_nonneg _)
    · simp only [hr,ite_false]
      exact integrableOn_zero
  convert hi using 1
  funext v
  simp only [a03EndpointPhysicalTensorSum,W,q]
theorem a03_actual_main_tensor_mellin_integrableOn
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 4*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c ε)
        positive T A B H σ (rawMomentShifts T σ) v f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode
        (a03ActualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  obtain ⟨T0,kernels,hgraph,hseminorm⟩ := a03_actual_tensor_bounded_schwartz_family hΦ hΦs hc hc1 hε hκ hθ
  obtain ⟨C,hC,hCb⟩ := hseminorm 0 0
  filter_upwards [phase_actual_near_main_tensor_parameters_valid hs hR T0 θ κ f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_ge_atTop (1:ℝ)] with T hvalid hraw hT
  intro A B H hA hB hH k hactive σ hσ hroot positive
  have hrawσ := hraw σ hσ
  have hv0 : |(0:ℝ)|≤θ*Real.log T := by
    simpa using mul_nonneg hθ (Real.log_nonneg hT)
  obtain ⟨_hT,_hT0,hα,_hroot,_hv,_hr,_hr1,_hsign⟩ := hvalid A B H hA hB hH k hactive σ hσ hroot 0 hv0 positive
  have hm : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ActualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (rawMomentShifts T σ) p.1 A B H k positive) p.2) := by
    simpa only [phaseActualNearTensorData] using
      a03_actual_main_tensor_kernel_mellin_joint_stronglyMeasurable hc T ε
        (H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))))
        (rectangularGapSign positive) σ (rawMomentShifts T σ) hα Φ hΦ.continuous
  have hb : ∀ v∈Icc (-θ*Real.log T) (θ*Real.log T), ∀ y,
      ‖a03TensorLogCutoff y*a03ActualTensorNormalizedKernel Φ c ε
        (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive) y‖≤C := by
    intro v hv y
    have hvabs : |v|≤θ*Real.log T := abs_le.mpr (by simpa only [Set.mem_Icc,neg_mul] using hv)
    let p : {p : A03NearTensorData // A03NearTensorValid T0 θ κ p} :=
      ⟨phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive,
      hvalid A B H hA hB hH k hactive σ hσ hroot v hvabs positive⟩
    rw [←hgraph p y]
    exact (SchwartzMap.norm_le_seminorm ℂ (kernels p) y).trans (hCb p)
  exact ⟨a03EndpointPhysicalTensorSum_mellin_integrableOn_of_cutoff_bound
      (a03ActualTensorNormalizedKernel Φ c ε) positive T A B H σ (rawMomentShifts T σ) f g k hm hC hb,
    a03EndpointPhysicalSortedZeroMode_mellin_integrableOn_of_cutoff_bound _ hm hC hb
      T A B H f g k hA hB hH⟩

theorem a03_actual_dual_tensor_mellin_integrableOn
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 4*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c ε)
        positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode
        (a03ActualDualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  obtain ⟨T0,kernels,hgraph,hseminorm⟩ := a03_actual_dual_tensor_bounded_schwartz_family hΦ hΦs hc hc1 hε hκ hθ hR
  obtain ⟨C,hC,hCb⟩ := hseminorm 0 0
  filter_upwards [phase_actual_near_dual_tensor_parameters_valid hs hR T0 θ κ f g,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_ge_atTop (1:ℝ)] with T hvalid hraw hT
  intro A B H hA hB hH k hactive σ hσ hroot positive
  have hrawσ := hraw σ hσ
  have hv0 : |(0:ℝ)|≤θ*Real.log T := by
    simpa using mul_nonneg hθ (Real.log_nonneg hT)
  obtain ⟨⟨_hT,_hT0,hα,_hroot,_hv,_hr,_hr1,_hsign⟩,_hσ⟩ := hvalid A B H hA hB hH k hactive σ hσ hroot 0 hv0 positive
  have hm : StronglyMeasurable (fun p : ℝ×A03SixTensorSpace =>
      a03ActualDualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) p.1 A B H k positive) p.2) := by
    simpa only [phaseActualNearTensorData] using
      a03_actual_dual_tensor_kernel_mellin_joint_stronglyMeasurable hc T ε
        (H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))))
        (rectangularGapSign positive) σ (bblrSixShifts (rawMomentShifts T σ) 1) hα hrawσ Φ hΦ.continuous
  have hb : ∀ v∈Icc (-θ*Real.log T) (θ*Real.log T), ∀ y,
      ‖a03TensorLogCutoff y*a03ActualDualTensorNormalizedKernel Φ c ε
        (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive) y‖≤C := by
    intro v hv y
    have hvabs : |v|≤θ*Real.log T := abs_le.mpr (by simpa only [Set.mem_Icc,neg_mul] using hv)
    let p : {p : A03NearTensorData // A03DualNearTensorValid T0 θ κ R p} :=
      ⟨phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive,
      hvalid A B H hA hB hH k hactive σ hσ hroot v hvabs positive⟩
    rw [←hgraph p y]
    exact (SchwartzMap.norm_le_seminorm ℂ (kernels p) y).trans (hCb p)
  exact ⟨a03EndpointPhysicalTensorSum_mellin_integrableOn_of_cutoff_bound
      (a03ActualDualTensorNormalizedKernel Φ c ε) positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) f g k hm hC hb,
    a03EndpointPhysicalSortedZeroMode_mellin_integrableOn_of_cutoff_bound _ hm hC hb
      T A B H f g k hA hB hH⟩

theorem a03EndpointPhysicalTensorSum_const_mul_mellin
    (F : A03NearTensorData→A03SixTensorSpace→ℂ) (z : ℂ)
    (positive : Bool) (T A B H : ℝ) (σ α : MomentShifts) (v : ℝ)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    a03EndpointPhysicalTensorSum (fun p y => z*F p y) positive T A B H σ α v f g k=
      z*a03EndpointPhysicalTensorSum F positive T A B H σ α v f g k := by
  unfold a03EndpointPhysicalTensorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem a03SixTensorPhysicalZeroMode_const_mul
    (F : A03SixTensorSpace→ℂ) (z : ℂ) (m n : Bool) (q : QuadraticScales) (α β : ℕ→ℂ) :
    a03SixTensorPhysicalZeroMode (fun y => z*F y) m n q α β=
      z*a03SixTensorPhysicalZeroMode F m n q α β := by
  unfold a03SixTensorPhysicalZeroMode
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have he : (fun x : ℝ => (∏ j : Fin 5,
      (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))*
        (z*F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))))=
      fun x : ℝ => z*((∏ j : Fin 5,
        (rectangularSmoothBlockWeight (a03SixZeroSourceArguments m n q w x j.succ):ℂ))*
          F (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x))) := by
    funext x
    ring
  rw [he,integral_const_mul]
  ring

theorem a03EndpointPhysicalSortedZeroMode_const_mul_mellin
    (F : A03SixTensorSpace→ℂ) (z : ℂ) (T A B H : ℝ)
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    a03EndpointPhysicalSortedZeroMode (fun y => z*F y) T A B H f g k=
      z*a03EndpointPhysicalSortedZeroMode F T A B H f g k :=
  a03SixTensorPhysicalZeroMode_const_mul F z _ _ _ _ _

theorem a03_actual_main_raw_tensor_mellin_integrableOn
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 4*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum (a03ActualTensorRawKernel Φ c)
        positive T A B H σ (rawMomentShifts T σ) v f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode
        (a03ActualTensorRawKernel Φ c (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  filter_upwards [a03_actual_main_tensor_mellin_integrableOn hΦ hΦs hc hc1 hε hκ hθ hR hs f g,
    eventually_ge_atTop (1:ℝ)] with T hint hT
  intro A B H hA hB hH k hactive σ hσ hroot positive
  obtain ⟨hi,hz⟩ := hint A B H hA hB hH k hactive σ hσ hroot positive
  have he : ∀ (p : A03NearTensorData), p.T=T → ∀ y,
      a03ActualTensorRawKernel Φ c p y=((T^ε:ℝ):ℂ)*a03ActualTensorNormalizedKernel Φ c ε p y := by
    intro p hp y
    unfold a03ActualTensorNormalizedKernel
    rw [hp,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,
      ←Real.rpow_add (zero_lt_one.trans_le hT),add_neg_cancel,Real.rpow_zero]
    simp
  have hsum : ∀ v, ((T^ε:ℝ):ℂ)*a03EndpointPhysicalTensorSum (a03ActualTensorNormalizedKernel Φ c ε)
      positive T A B H σ (rawMomentShifts T σ) v f g k=
      a03EndpointPhysicalTensorSum (a03ActualTensorRawKernel Φ c) positive T A B H σ (rawMomentShifts T σ) v f g k := by
    intro v
    unfold a03EndpointPhysicalTensorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [he _ rfl]
      ring
    · ring
  have hzero : ∀ v, ((T^ε:ℝ):ℂ)*a03EndpointPhysicalSortedZeroMode
      (a03ActualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive))
      T A B H f g k=
      a03EndpointPhysicalSortedZeroMode
        (a03ActualTensorRawKernel Φ c (phaseActualNearTensorData T σ (rawMomentShifts T σ) v A B H k positive))
        T A B H f g k := by
    intro v
    rw [←a03EndpointPhysicalSortedZeroMode_const_mul_mellin]
    congr 1
    funext y
    exact (he _ rfl y).symm
  exact ⟨(hi.const_mul ((T^ε:ℝ):ℂ)).congr (ae_of_all _ hsum),
    (hz.const_mul ((T^ε:ℝ):ℂ)).congr (ae_of_all _ hzero)⟩

theorem a03_actual_dual_raw_tensor_mellin_integrableOn
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R s : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 4*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : s<1)
    (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ, phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ σ : MomentShifts, (∀ j, ‖σ j‖≤R) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) → ∀ positive : Bool,
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalTensorSum (a03ActualDualTensorRawKernel Φ c)
        positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) ∧
      IntegrableOn (fun v : ℝ => a03EndpointPhysicalSortedZeroMode
        (a03ActualDualTensorRawKernel Φ c (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive))
        T A B H f g k) (Icc (-θ*Real.log T) (θ*Real.log T)) := by
  filter_upwards [a03_actual_dual_tensor_mellin_integrableOn hΦ hΦs hc hc1 hε hκ hθ hR hs f g,
    eventually_ge_atTop (1:ℝ)] with T hint hT
  intro A B H hA hB hH k hactive σ hσ hroot positive
  obtain ⟨hi,hz⟩ := hint A B H hA hB hH k hactive σ hσ hroot positive
  have he : ∀ (p : A03NearTensorData), p.T=T → ∀ y,
      a03ActualDualTensorRawKernel Φ c p y=((T^ε:ℝ):ℂ)*a03ActualDualTensorNormalizedKernel Φ c ε p y := by
    intro p hp y
    unfold a03ActualDualTensorNormalizedKernel
    rw [hp,Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,
      ←Real.rpow_add (zero_lt_one.trans_le hT),add_neg_cancel,Real.rpow_zero]
    simp
  have hsum : ∀ v, ((T^ε:ℝ):ℂ)*a03EndpointPhysicalTensorSum (a03ActualDualTensorNormalizedKernel Φ c ε)
      positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k=
      a03EndpointPhysicalTensorSum (a03ActualDualTensorRawKernel Φ c) positive T A B H σ (bblrSixShifts (rawMomentShifts T σ) 1) v f g k := by
    intro v
    unfold a03EndpointPhysicalTensorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs
    · rw [he _ rfl]
      ring
    · ring
  have hzero : ∀ v, ((T^ε:ℝ):ℂ)*a03EndpointPhysicalSortedZeroMode
      (a03ActualDualTensorNormalizedKernel Φ c ε (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive))
      T A B H f g k=
      a03EndpointPhysicalSortedZeroMode
        (a03ActualDualTensorRawKernel Φ c (phaseActualNearTensorData T σ (bblrSixShifts (rawMomentShifts T σ) 1) v A B H k positive))
        T A B H f g k := by
    intro v
    rw [←a03EndpointPhysicalSortedZeroMode_const_mul_mellin]
    congr 1
    funext y
    exact (he _ rfl y).symm
  exact ⟨(hi.const_mul ((T^ε:ℝ):ℂ)).congr (ae_of_all _ hsum),
    (hz.const_mul ((T^ε:ℝ):ℂ)).congr (ae_of_all _ hzero)⟩

end
end SixthMoment

import SixthMoment.Numerator.U.Sources.PassiveNativeSourceGeometry

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_source_domain_mono {T A B H η ρ : ℝ}
    (f g : ℝ→ℝ) (k : Fin 4→ℕ) (hηρ : η≤ρ)
    (h : A03ActualPassiveNearZeroBlock T A B H η f g k) :
    A03ActualPassiveNearZeroBlock T A B H ρ f g k := by
  obtain ⟨p⟩ := h
  exact ⟨{ p with low_gap := p.low_gap.trans (mul_le_mul_of_nonneg_right hηρ p.X_pos.le) }⟩

theorem a03_actual_passive_source_restricted_domain {T A B H s u S U : ℝ}
    (hT : 1≤T) (hs : s≤S) (hu : u≤U) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hk : k∈rectangularAFEProductScaleGrid (T^(2+u)))
    (hp : A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k) :
    k∈rectangularAFEProductScaleGrid (T^(2+U)) ∧
    A03ActualPassiveNearZeroBlock T A B H (T^(S-1)) f g k := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  exact ⟨rectangularAFEProductScaleGrid_mono (Real.rpow_pos_of_pos hTp _)
      (Real.rpow_pos_of_pos hTp _) (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hk,
    a03_actual_passive_source_domain_mono f g k
      (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) hp⟩

theorem a03_actual_passive_tensor_parameters_valid {s : ℝ} (hs : s<1)
    (T0 θ κ : ℝ) (f g : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4→ℕ, A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      ∀ σ α : MomentShifts, (∀ j, ‖α j‖≤1/4) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      A03NearTensorValid T0 θ κ (phaseActualNearTensorData T σ α v A B H k positive) := by
  have ht : Tendsto (fun T : ℝ => T^(s-1)) atTop (nhds 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (show 0<1-s by linarith)
  have hsmall : ∀ᶠ T : ℝ in atTop,T^(s-1)≤1/800 :=
    ((tendsto_order.1 ht).2 (1/800) (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ),eventually_ge_atTop T0]
    with T ht hT hT0
  intro A B H hA hB hH k hp σ α hα hroot v hv positive
  obtain ⟨p⟩ := hp
  have hden : 0<B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)) :=
    mul_pos hB (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _))
  have hr0 : 0≤H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))) :=
    div_nonneg hH.le hden.le
  have hsmall' := (p.relative_gap_bound hA hB hH).trans
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤8))
  have hsign : |rectangularGapSign positive|=1 := by
    cases positive <;> norm_num [rectangularGapSign]
  exact ⟨hT,hT0,hα,hroot,hv,hr0,by change H/(B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)))≤1/100; linarith,hsign⟩

end
end SixthMoment

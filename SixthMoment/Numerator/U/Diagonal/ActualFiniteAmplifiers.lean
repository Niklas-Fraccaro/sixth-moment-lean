import SixthMoment.Numerator.U.Diagonal.ActualDiagonalGrouping
import SixthMoment.Numerator.U.Reconstruction.RectangularAFEError


namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

def actualAmplifierCutoff (T a : ℝ) : Finset ActualPositiveAmplifierIndex :=
  (Finset.Icc 1 ⌊T^a⌋₊).subtype (fun m => m ≠ 0)

theorem actualAmplifierProfile_zero_outside {T a : ℝ} (hT : 1 < T)
    (f : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (m : ActualPositiveAmplifierIndex)
    (hm : m ∉ actualAmplifierCutoff T a) : f (Real.log m.val/Real.log T)=0 := by
  have hpos : 1 ≤ m.val := Nat.one_le_iff_ne_zero.mpr m.property
  have hfloor : ⌊T^a⌋₊ < m.val := by
    simp only [actualAmplifierCutoff,Finset.mem_subtype,Finset.mem_Icc,not_and] at hm
    exact Nat.lt_of_not_ge (hm hpos)
  have hpow : T^a < (m.val:ℝ) := Nat.lt_of_floor_lt hfloor
  have hlog : a*Real.log T < Real.log (m.val:ℝ) :=
    Real.lt_log_of_rpow_lt (zero_lt_one.trans hT) hpow
  exact rectangular_supported_profile_zero_above f hf _
    ((lt_div_iff₀ (Real.log_pos hT)).mpr hlog)

theorem actualAmplifier_sum_eq_finite {T a b : ℝ} (hT : 1 < T)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (H : ℕ → ℕ → ℂ) :
    (∑' p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex,
      (f (Real.log p.1.val/Real.log T):ℂ)*(g (Real.log p.2.val/Real.log T):ℂ)*H p.1.val p.2.val) =
      ∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
        (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*H m n := by
  rw [tsum_eq_sum (s := (actualAmplifierCutoff T a).product (actualAmplifierCutoff T b))]
  · change (∑ p ∈ (actualAmplifierCutoff T a) ×ˢ (actualAmplifierCutoff T b),
      (f (Real.log p.1.val/Real.log T):ℂ)*
        (g (Real.log p.2.val/Real.log T):ℂ)*H p.1.val p.2.val) = _
    rw [Finset.sum_product (actualAmplifierCutoff T a) (actualAmplifierCutoff T b)
      (fun p => (f (Real.log p.1.val/Real.log T):ℂ)*
        (g (Real.log p.2.val/Real.log T):ℂ)*H p.1.val p.2.val)]
    unfold actualAmplifierCutoff
    calc
      _ = ∑ m ∈ (Finset.Icc 1 ⌊T^a⌋₊).subtype (fun m => m ≠ 0),
          ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
            (f (Real.log m.val/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*H m.val n := by
        apply Finset.sum_congr rfl
        intro m hm
        exact Finset.sum_subtype_of_mem (s := Finset.Icc 1 ⌊T^b⌋₊)
          (fun n => (f (Real.log m.val/Real.log T):ℂ)*
            (g (Real.log n/Real.log T):ℂ)*H m.val n) (fun n hn => by
          exact Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
      _ = _ := Finset.sum_subtype_of_mem (s := Finset.Icc 1 ⌊T^a⌋₊)
        (fun m => ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊, (f (Real.log m/Real.log T):ℂ)*
          (g (Real.log n/Real.log T):ℂ)*H m n) (fun m hm => by
        exact Nat.ne_zero_of_lt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1))
  · intro p hp
    have hp' : ¬(p.1 ∈ actualAmplifierCutoff T a ∧ p.2 ∈ actualAmplifierCutoff T b) :=
      fun h => hp (Finset.mem_product.mpr h)
    by_cases hm : p.1 ∈ actualAmplifierCutoff T a
    · rw [actualAmplifierProfile_zero_outside hT g hg p.2 (by exact fun hn => hp' ⟨hm,hn⟩)]
      simp
    · rw [actualAmplifierProfile_zero_outside hT f hf p.1 hm]
      simp

theorem actualFiniteAmplifiedDiagonal_eq_MellinEuler {T a b t δ : ℝ}
    (hT : 1 < T) (ht : t ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
      (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm G α m n t) =
      (1/(2*π):ℂ)*(((Real.log T:ℝ):ℂ)/(2*π))^2*
        ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α
          (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ t w
          ∂(volume.prod (volume.prod volume)) := by
  rw [← actualAmplifier_sum_eq_finite hT f g hf hg]
  apply actualAmplifiedDiagonal_eq_MellinEuler (f := fun x => (f x:ℂ))
    (g := fun x => (g x:ℂ)) (L := Real.log T) (δ := δ) ht G α hG
  · exact hf.2.1.comp_left (show Complex.ofReal 0 = 0 from rfl)
  · exact Complex.ofRealCLM.contDiff.comp hf.1
  · exact hg.2.1.comp_left (show Complex.ofReal 0 = 0 from rfl)
  · exact Complex.ofRealCLM.contDiff.comp hg.1
  · exact Real.log_pos hT
  · exact hδ
  · exact hδ1
  · exact hα

end
end SixthMoment

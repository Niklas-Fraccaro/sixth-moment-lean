import Sechstmoment.Arithmetic.Watt.Adapters


namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff Topology
noncomputable section
set_option maxHeartbeats 2000000

def transition (x : ℝ) : ℝ := Real.smoothTransition (4*x-2)

theorem transition_smooth : ContDiff ℝ ∞ transition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem transition_zero {x : ℝ} (hx : x ≤ 1/2) : transition x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem transition_one {x : ℝ} (hx : 3/4 ≤ x) : transition x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem transition_norm (x : ℝ) : ‖transition x‖ ≤ 1 := by
  unfold transition
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem transition_derivative_zero {j : ℕ} (hj : j ≠ 0) {x : ℝ}
    (hx : x ∉ Icc (1/2 : ℝ) (3/4)) : iteratedDeriv j transition x = 0 := by
  have hh : x < 1/2 ∨ 3/4 < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  rcases hh with hx | hx
  · have he : transition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact transition_zero hy.le
    simpa only [iteratedDeriv_const,hj,ite_false] using he.iteratedDeriv_eq j
  · have he : transition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact transition_one hy.le
    simpa only [iteratedDeriv_const,hj,ite_false] using he.iteratedDeriv_eq j

theorem transition_derivative_bounds :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j) ∧ ∀ j x, 0 < x →
      ‖iteratedDeriv j transition x‖ ≤ b j*x^(-(j : ℝ)) := by
  have hex (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, 0 < x →
      ‖iteratedDeriv j transition x‖ ≤ C*x^(-(j : ℝ)) := by
    by_cases hj : j = 0
    · refine ⟨1,by norm_num,?_⟩
      intro x _
      simpa only [hj,iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one]
        using transition_norm x
    obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/2 : ℝ) (3/4))).exists_bound_of_continuousOn
      (transition_smooth.continuous_iteratedDeriv j (by exact_mod_cast le_top)).continuousOn
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x hx
    by_cases hxs : x ∈ Icc (1/2 : ℝ) (3/4)
    · have hp : 1 ≤ x^(-(j : ℝ)) := by
        rw [Real.rpow_neg hx.le]
        exact (one_le_inv₀ (Real.rpow_pos_of_pos hx _)).mpr
          (Real.rpow_le_one hx.le (by linarith [hxs.2]) (Nat.cast_nonneg _))
      exact ((hC x hxs).trans (le_max_left _ _)).trans
        (le_mul_of_one_le_right (le_max_right _ _) hp)
    · rw [transition_derivative_zero hj hxs,norm_zero]
      positivity
  choose b hb hd using hex
  exact ⟨b,hb,hd⟩

def blockScale (A : ℝ) (j : ℕ) : ℝ := A/(4/3 : ℝ)^j

@[simp] theorem blockScale_zero (A : ℝ) : blockScale A 0 = A := by simp [blockScale]

theorem blockScale_pos {A : ℝ} (hA : 0 < A) (j : ℕ) : 0 < blockScale A j := by
  unfold blockScale
  positivity

theorem blockScale_succ (A : ℝ) (j : ℕ) :
    blockScale A (j+1) = (3/4)*blockScale A j := by
  unfold blockScale
  rw [pow_succ]
  ring

theorem blockScale_antitone {A : ℝ} (hA : 0 ≤ A) : Antitone (blockScale A) := by
  intro i j hij
  unfold blockScale
  exact div_le_div_of_nonneg_left hA (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4/3) hij)

theorem exists_final_block {A : ℝ} (hA : 1 ≤ A) :
    ∃ N : ℕ, 1 ≤ blockScale A N ∧ blockScale A N < 4/3 := by
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near hA (by norm_num : (1 : ℝ) < 4/3)
  refine ⟨N,?_,?_⟩
  · exact (le_div_iff₀ (by positivity : (0 : ℝ) < (4/3 : ℝ)^N)).mpr (by simpa using hlo)
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (4/3 : ℝ)^N)).mpr
    simpa only [pow_succ, mul_comm] using hhi

def block (A : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => transition (x/A)
  | j+1 => fun x => transition (x/blockScale A (j+1))-transition (x/blockScale A j)

theorem block_smooth (A : ℝ) (j : ℕ) : ContDiff ℝ ∞ (block A j) := by
  cases j with
  | zero => exact transition_smooth.comp (contDiff_id.div_const A)
  | succ j =>
    exact (transition_smooth.comp (contDiff_id.div_const _)).sub
      (transition_smooth.comp (contDiff_id.div_const _))

theorem sum_blocks (A x : ℝ) (N : ℕ) :
    (∑ j ∈ range (N+1), block A j x) = transition (x/blockScale A N) := by
  induction N with
  | zero => simp [block]
  | succ N ih =>
    rw [sum_range_succ,ih]
    simp only [block]
    ring

theorem sum_blocks_eq_one {A x : ℝ} {N : ℕ}
    (hA : 0 < A) (hN : blockScale A N < 4/3) (hx : 1 ≤ x) :
    (∑ j ∈ range (N+1), block A j x) = 1 := by
  rw [sum_blocks]
  apply transition_one
  apply (le_div_iff₀ (blockScale_pos hA N)).mpr
  linarith

theorem block_succ_zero_of_outside {A x : ℝ} (hA : 0 < A) (j : ℕ)
    (hx : x ∉ Icc (blockScale A (j+1)/2) (blockScale A (j+1))) :
    block A (j+1) x = 0 := by
  have hp := blockScale_pos hA j
  have hp' := blockScale_pos hA (j+1)
  have hscale := blockScale_succ A j
  have hcases : x < blockScale A (j+1)/2 ∨ blockScale A (j+1) < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  change transition (x/blockScale A (j+1))-transition (x/blockScale A j) = 0
  rcases hcases with hx | hx
  · rw [transition_zero ((div_le_iff₀ hp').mpr (by linarith)),
      transition_zero ((div_le_iff₀ hp).mpr (by nlinarith))]
    ring
  · rw [transition_one ((le_div_iff₀ hp').mpr (by nlinarith)),
      transition_one ((le_div_iff₀ hp).mpr (by nlinarith))]
    ring

theorem block_succ_support {A : ℝ} (hA : 0 < A) (j : ℕ) :
    tsupport (block A (j+1)) ⊆ Icc (blockScale A (j+1)/2) (blockScale A (j+1)) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hout
  exact hx (block_succ_zero_of_outside hA j hout)

def weightedBlock (u : ℝ → ℂ) (A : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  u x*(block A j x : ℂ)

theorem weightedBlock_smooth {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (A : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (weightedBlock u A j) :=
  hu.mul (Complex.ofRealCLM.contDiff.comp (block_smooth A j))

theorem weightedBlock_support {u : ℝ → ℂ} {A : ℝ} (hA : 0 < A)
    (hu : tsupport u ⊆ Icc (1/2) A) (j : ℕ) :
    tsupport (weightedBlock u A j) ⊆ Icc (blockScale A j/2) (blockScale A j) := by
  cases j with
  | zero =>
    simp only [blockScale_zero]
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hu' : u x ≠ 0 := by
      intro hz
      exact hx (by simp [weightedBlock,hz])
    have hxA := hu (subset_tsupport u hu')
    refine ⟨?_,hxA.2⟩
    by_contra hh
    have hcut : transition (x/A) = 0 :=
      transition_zero ((div_le_iff₀ hA).mpr (by linarith))
    exact hx (by simp [weightedBlock,block,hcut])
  | succ j =>
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hne : block A (j+1) x ≠ 0 := by
      intro hz
      exact hx (by simp [weightedBlock,hz])
    exact block_succ_support hA j (subset_tsupport _ hne)

theorem sum_weightedBlocks {u : ℝ → ℂ} {A x : ℝ} {N : ℕ}
    (hA : 0 < A) (hN : blockScale A N < 4/3) (hx : 1 ≤ x) :
    (∑ j ∈ range (N+1), weightedBlock u A j x) = u x := by
  simp only [weightedBlock, ← mul_sum, ← Complex.ofReal_sum,
    sum_blocks_eq_one hA hN hx, Complex.ofReal_one, mul_one]

end
end Watt41
end DivisorProof

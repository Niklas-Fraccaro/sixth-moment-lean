import Sechstmoment.Zeta.DirichletL.DualBound
import Sechstmoment.Zeta.DirichletL.SmoothCharMeanSquare


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators Classical
noncomputable section

theorem char_parity_norm_sq_sum_le {N : ℕ} [NeZero N]
    (S : Finset (DirichletCharacter ℂ N)) (F : DirichletCharacter ℂ N → ℕ → ℂ) :
    (∑ χ ∈ S, ‖F χ (dirichletParity χ)‖^2) ≤
      (∑ χ : DirichletCharacter ℂ N, ‖F χ 0‖^2)+
        (∑ χ : DirichletCharacter ℂ N, ‖F χ 1‖^2) := by
  calc
    _ ≤ ∑ χ ∈ S, (‖F χ 0‖^2+‖F χ 1‖^2) := by
      apply Finset.sum_le_sum
      intro χ _
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (dirichletParity_le_one χ) with h | h
      · rw [h]
        linarith [sq_nonneg ‖F χ 1‖]
      · rw [h]
        linarith [sq_nonneg ‖F χ 0‖]
    _ ≤ _ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => by positivity)

theorem sum_dirichlet_inv {N : ℕ} [NeZero N] (f : DirichletCharacter ℂ N → ℝ) :
    (∑ χ : DirichletCharacter ℂ N, f χ⁻¹) = ∑ χ : DirichletCharacter ℂ N, f χ := by
  exact Fintype.sum_equiv (Equiv.inv (DirichletCharacter ℂ N)) _ _ (fun _ => rfl)

theorem primitiveDirichlet_fourthMoment_small_exponent {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      (∑ χ : DirichletCharacter ℂ N with χ.IsPrimitive ∧ χ ≠ 1, ‖χ.LFunction s‖^4) ≤
        C*(N : ℝ)^(1+2*ε)*(1+|s.im|)^20 := by
  obtain ⟨K,hK,hmean⟩ := dirichletSmoothTransform_mean_square hε
  obtain ⟨D,hD,hdual⟩ := dirichletSquareDualFactor_norm_sq_bound
  refine ⟨4*K+4*D^2*K, by positivity, ?_⟩
  intro N hN s hs
  have : NeZero N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  let H : ℝ := 1+|s.im|
  have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg s.im]
  let δ : ℝ := s.re-1/2+ε
  have hδ : δ ∈ Icc (0 : ℝ) 1 := by dsimp [δ]; constructor <;> linarith [hs.1,hs.2]
  let S : Finset (DirichletCharacter ℂ N) := Finset.univ.filter (fun χ => χ.IsPrimitive ∧ χ ≠ 1)
  let Z : ℝ := D*(N : ℝ)^(1-2*s.re)*H^4
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hpoint (χ : DirichletCharacter ℂ N) (hχ : χ ∈ S) :
      ‖χ.LFunction s‖^4 ≤
        2*‖dirichletSmoothTransform χ s (dirichletParity χ)‖^2+
        2*Z^2*‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖^2 := by
    have hp := (Finset.mem_filter.mp hχ).2
    have hafe := dirichletL_square_eq_smooth_transforms χ hp.2 hp.1
      (by linarith [hs.1] : 0 < s.re) (by linarith [hs.2] : s.re < 1)
    have hx := hdual N hN χ hp.1 s hs
    change ‖dirichletSquareDualFactor χ s‖^2 ≤ Z at hx
    have hmul : ‖(dirichletSquareDualFactor χ s)^2*
        dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖ ≤
        Z*‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖ := by
      rw [norm_mul,norm_pow]
      gcongr
    calc
      _ = ‖(χ.LFunction s)^2‖^2 := by rw [norm_pow]; ring
      _ = ‖dirichletSmoothTransform χ s (dirichletParity χ)+
          (dirichletSquareDualFactor χ s)^2*
            dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖^2 := by rw [hafe]
      _ ≤ (‖dirichletSmoothTransform χ s (dirichletParity χ)‖+
          Z*‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖)^2 := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add le_rfl hmul)
      _ ≤ _ := by nlinarith [sq_nonneg (‖dirichletSmoothTransform χ s (dirichletParity χ)‖-
          Z*‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖)]
  have hdir (a : ℕ) (ha : a ≤ 1) :
      (∑ χ : DirichletCharacter ℂ N, ‖dirichletSmoothTransform χ s a‖^2) ≤
        K*(N : ℝ)^(1+2*ε)*H^12 :=
    hmean N hN s ⟨by linarith [hs.1],hs.2⟩ a ha ε ⟨hε.le,by linarith⟩ (by linarith [hs.1])
  have hdualmean (a : ℕ) (ha : a ≤ 1) :
      (∑ χ : DirichletCharacter ℂ N, ‖dirichletSmoothTransform χ⁻¹ (1-s) a‖^2) ≤
        K*(N : ℝ)^(1+2*δ)*H^12 := by
    rw [sum_dirichlet_inv (fun χ => ‖dirichletSmoothTransform χ (1-s) a‖^2)]
    have h := hmean N hN (1-s) (by simp only [sub_re,one_re]; constructor <;> linarith [hs.1,hs.2])
      a ha δ hδ (by dsimp [δ]; linarith)
    simpa [H] using h
  have hdirsum : (∑ χ ∈ S, ‖dirichletSmoothTransform χ s (dirichletParity χ)‖^2) ≤
      2*(K*(N : ℝ)^(1+2*ε)*H^12) := by
    exact (char_parity_norm_sq_sum_le S (fun χ a => dirichletSmoothTransform χ s a)).trans
      (by linarith [hdir 0 (by norm_num),hdir 1 (by norm_num)])
  have hdualsum : (∑ χ ∈ S, ‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖^2) ≤
      2*(K*(N : ℝ)^(1+2*δ)*H^12) := by
    exact (char_parity_norm_sq_sum_le S (fun χ a => dirichletSmoothTransform χ⁻¹ (1-s) a)).trans
      (by linarith [hdualmean 0 (by norm_num),hdualmean 1 (by norm_num)])
  have hZmean : Z^2*(K*(N : ℝ)^(1+2*δ)*H^12) ≤
      D^2*K*(N : ℝ)^(1+2*ε)*H^20 := by
    have hpow : ((N : ℝ)^(1-2*s.re))^2 = (N : ℝ)^((1-2*s.re)*2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      norm_num
    have hprod : (N : ℝ)^((1-2*s.re)*2)*(N : ℝ)^(1+2*δ) =
        (N : ℝ)^(2-2*s.re+2*ε) := by
      rw [← Real.rpow_add hNr]
      congr 1
      dsimp [δ]
      ring
    calc
      _ = D^2*K*((N : ℝ)^((1-2*s.re)*2)*(N : ℝ)^(1+2*δ))*H^20 := by
        dsimp only [Z]
        rw [mul_pow,mul_pow,hpow]
        ring
      _ = D^2*K*(N : ℝ)^(2-2*s.re+2*ε)*H^20 := by rw [hprod]
      _ ≤ _ := by gcongr; linarith [hs.1]
  have hHpow : H^12 ≤ H^20 := pow_le_pow_right₀ hH (by norm_num)
  change (∑ χ ∈ S, ‖χ.LFunction s‖^4) ≤ _
  calc
    _ ≤ (∑ χ ∈ S, (2*‖dirichletSmoothTransform χ s (dirichletParity χ)‖^2+
        2*Z^2*‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖^2)) :=
      Finset.sum_le_sum hpoint
    _ = 2*(∑ χ ∈ S, ‖dirichletSmoothTransform χ s (dirichletParity χ)‖^2)+
        2*Z^2*(∑ χ ∈ S, ‖dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ)‖^2) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
    _ ≤ 4*(K*(N : ℝ)^(1+2*ε)*H^12)+4*(Z^2*(K*(N : ℝ)^(1+2*δ)*H^12)) := by
      nlinarith [mul_le_mul_of_nonneg_left hdualsum (by positivity : 0 ≤ 2*Z^2)]
    _ ≤ 4*(K*(N : ℝ)^(1+2*ε)*H^20)+4*(D^2*K*(N : ℝ)^(1+2*ε)*H^20) := by gcongr
    _ = _ := by dsimp [H]; ring

theorem primitiveDirichlet_fourthMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      (∑ χ : DirichletCharacter ℂ N with χ.IsPrimitive ∧ χ ≠ 1, ‖χ.LFunction s‖^4) ≤
        C*(N : ℝ)^(1+ε)*(1+|s.im|)^20 := by
  let δ : ℝ := min (ε/2) (1/4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  obtain ⟨C,hC,hbound⟩ := primitiveDirichlet_fourthMoment_small_exponent hδ (min_le_right _ _)
  refine ⟨C,hC,?_⟩
  intro N hN s hs
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN.out
  exact (hbound N hN s hs).trans (by
    gcongr
    have h := min_le_left (ε/2) (1/4 : ℝ)
    change δ ≤ ε/2 at h
    linarith)

end
end Sechstmoment.Source

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Sechstmoment.Zeta.DirichletL.CharPolynomials


namespace Sechstmoment.Source
open Complex Real ZMod Finset ComplexConjugate
open scoped BigOperators Classical
noncomputable section

theorem additive_conj_orthogonality (q : ℕ) [NeZero q] (a b : ZMod q) :
    ∑ k : ZMod q, conj (stdAddChar (a*k)) * stdAddChar (b*k) =
      if a = b then (q : ℂ) else 0 := by
  simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
    show ∀ k : ZMod q, -(a*k)+b*k = k*(b-a) by intro k; ring]
  have h := AddChar.sum_mulShift (b-a) (isPrimitive_stdAddChar q)
  simpa only [sub_eq_zero,eq_comm,ZMod.card,Nat.cast_ite,Nat.cast_zero] using h

theorem additive_fourier_parseval (q : ℕ) [NeZero q] (A : ZMod q → ℂ) :
    ∑ k : ZMod q, ‖∑ a : ZMod q, A a * stdAddChar (a*k)‖^2 =
      (q : ℝ)*∑ a : ZMod q, ‖A a‖^2 := by
  simpa only [← Finset.mul_sum] using finite_transform_parseval
    (fun k a : ZMod q => stdAddChar (a*k)) A (fun _ => (q : ℝ))
    (by intro a b; simpa using additive_conj_orthogonality q a b)

theorem residue_units_card (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (ZMod q)).filter IsUnit).card = q.totient := by
  rw [← ZMod.card_units_eq_totient]
  have he : ((Finset.univ : Finset (ZMod q)).filter IsUnit) =
      Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),Units.val_injective⟩ := by
    ext a
    simp [IsUnit]
  rw [he,Finset.card_map,Finset.card_univ]

theorem dirichlet_character_norm_sq_sum (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖χ a‖^2 = (q.totient : ℝ) := by
  have hpoint (a : ZMod q) : ‖χ a‖^2 = if IsUnit a then (1 : ℝ) else 0 := by
    split_ifs with ha
    · obtain ⟨u,rfl⟩ := ha
      simp
    · simp [MulChar.map_nonunit _ ha]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [residue_units_card]

theorem all_gaussSum_fourier_energy (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∑ k : ZMod q, ‖gaussSum χ (stdAddChar.mulShift k)‖^2 =
      (q : ℝ)*(q.totient : ℝ) := by
  simpa only [gaussSum,AddChar.mulShift_apply,mul_comm,
    dirichlet_character_norm_sq_sum] using additive_fourier_parseval q (fun a => χ a)

theorem all_gaussSum_norm_sq_le (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ stdAddChar‖^2 ≤ (q : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hunit (a : ZMod q) (ha : IsUnit a) :
      ‖gaussSum χ (stdAddChar.mulShift a)‖^2 = ‖gaussSum χ stdAddChar‖^2 := by
    obtain ⟨u,rfl⟩ := ha
    rw [gaussSum_mulShift_eq,norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul]
  have hsum : (q.totient : ℝ)*‖gaussSum χ stdAddChar‖^2 ≤
      (q : ℝ)*(q.totient : ℝ) := by
    rw [← all_gaussSum_fourier_energy q χ]
    calc
      _ = ∑ a : ZMod q with IsUnit a, ‖gaussSum χ (stdAddChar.mulShift a)‖^2 := by
        simp_rw [Finset.sum_congr rfl (fun a ha => hunit a (Finset.mem_filter.mp ha).2)]
        simp only [sum_const,nsmul_eq_mul]
        rw [residue_units_card]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro a _ _; positivity)
  nlinarith

theorem all_gaussSum_norm_le_sqrt (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ stdAddChar‖ ≤ Real.sqrt q := by
  exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)).mpr
    (all_gaussSum_norm_sq_le q χ)

theorem additive_character_expansion (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    stdAddChar a = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ stdAddChar * χ a := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have he : (∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ stdAddChar * χ a) =
      (q.totient : ℂ)*stdAddChar a := by
    simp only [gaussSum,Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b : ZMod q, stdAddChar b *
          ∑ χ : DirichletCharacter ℂ q, conj (χ b)*χ a := by
        simp only [Finset.mul_sum,← MulChar.star_apply',RCLike.star_def]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        simp_rw [char_conj_orthogonality q]
        rw [Finset.sum_eq_single a]
        · simp [ha,mul_comm]
        · intro b _ hb
          simp [hb]
        · simp
  rw [he,← mul_assoc,inv_mul_cancel₀ hφ,one_mul]

theorem additive_character_expansion_nonunit (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : ¬ IsUnit a) :
    (∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ stdAddChar * χ a) = 0 := by
  simp [MulChar.map_nonunit _ ha]

theorem additive_character_finite_sum (q : ℕ) [NeZero q]
    (s : Finset ℕ) (c : ℕ → ℂ) (hs : ∀ n ∈ s, Nat.Coprime n q) :
    (∑ n ∈ s, c n * stdAddChar (-(n : ZMod q))) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        gaussSum χ⁻¹ stdAddChar * χ (-1) * (∑ n ∈ s, c n * χ n) := by
  have hneg (χ : DirichletCharacter ℂ q) (n : ZMod q) :
      χ (-n) = χ (-1)*χ n := by
    rw [show -n = (-1)*n by ring,map_mul]
  calc
    _ = ∑ n ∈ s, c n*((q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, gaussSum χ⁻¹ stdAddChar * χ (-(n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← additive_character_expansion q _
        ((ZMod.isUnit_iff_coprime n q).mpr (hs n hn)).neg]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro n _
      rw [hneg χ (n : ZMod q)]
      ring

end
end Sechstmoment.Source

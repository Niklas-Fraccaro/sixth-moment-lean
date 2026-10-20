import Mathlib.Analysis.PSeries
import SixthMoment.Numerator.U.ZeroModes.Transforms.DiagonalNativeSummation

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03DiagonalQuadSmallMajorant (c : ℝ) (q : Fin 4→ℕ) : ℝ :=
  ∏ j : Fin 4,(q j+1:ℝ)^(-(1/2+3*c/4))

theorem a03DiagonalQuadSmallMajorant_nonneg (c : ℝ) (q : Fin 4→ℕ) :
    0≤a03DiagonalQuadSmallMajorant c q := Finset.prod_nonneg (fun _ _ => by positivity)

theorem a03DiagonalQuadSmallMajorant_fixedPair (c : ℝ) {a b : ℕ} (x : FixedPairFibres a b) :
    a03DiagonalQuadSmallMajorant c (fixedPairQuad x)=
      ((b*x.1:ℕ):ℝ)^(-(1/2+3*c/4))*((a*x.1:ℕ):ℝ)^(-(1/2+3*c/4)) := by
  obtain ⟨h0,h1,h2,h3⟩ := fixedPairQuad_values x
  unfold a03DiagonalQuadSmallMajorant
  rw [Fin.prod_univ_four]
  have he {n m : ℕ} (h : n+1=m) : (n+1:ℝ)=(m:ℝ) := by exact_mod_cast h
  rw [he h0,he h1,he h2,he h3]
  have hbn : (x.2.1.val.1:ℝ)*(x.2.1.val.2:ℝ)=((b*x.1:ℕ):ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp x.2.1.property).1
  have han : (x.2.2.val.1:ℝ)*(x.2.2.val.2:ℝ)=((a*x.1:ℕ):ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp x.2.2.property).1
  rw [show (x.2.1.val.1:ℝ)^(-(1/2+3*c/4))*(x.2.1.val.2:ℝ)^(-(1/2+3*c/4))*
    (x.2.2.val.1:ℝ)^(-(1/2+3*c/4))*(x.2.2.val.2:ℝ)^(-(1/2+3*c/4))=
    ((x.2.1.val.1:ℝ)^(-(1/2+3*c/4))*(x.2.1.val.2:ℝ)^(-(1/2+3*c/4)))*
    ((x.2.2.val.1:ℝ)^(-(1/2+3*c/4))*(x.2.2.val.2:ℝ)^(-(1/2+3*c/4))) by ring,
    ←Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    ←Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),hbn,han]

theorem a03DivisorsAntidiagonal_card (n : ℕ) :
    n.divisorsAntidiagonal.card=n.divisors.card := by
  have h := Nat.sum_divisorsAntidiagonal (fun _ _ => (1:ℕ)) (n:=n)
  simpa using h

theorem a03DiagonalSmall_fibre_uniform_bound {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ,0≤D ∧ ∀ a b : ℕ,a≠0 → b≠0 → ∀ n : ℕ,
      (∑ x : ↥(b*n).divisorsAntidiagonal × ↥(a*n).divisorsAntidiagonal,
        a03DiagonalQuadSmallMajorant c (fixedPairQuad ⟨n,x⟩))≤D*(n:ℝ)^(-(1+c)) := by
  obtain ⟨B,hB,hdiv⟩ := divisor_prime_cost_subpower (show 0<c/4 by linarith) (by norm_num : (1:ℝ)≤1)
  simp only [one_pow,mul_one] at hdiv
  refine ⟨B^2,sq_nonneg B,?_⟩
  intro a b ha hb n
  by_cases hn : n=0
  · subst n
    have hz : (∑ x : ↥(b*0).divisorsAntidiagonal × ↥(a*0).divisorsAntidiagonal,
        a03DiagonalQuadSmallMajorant c (fixedPairQuad ⟨0,x⟩))=0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hh := (Nat.mem_divisorsAntidiagonal.mp x.1.property).2
      simp at hh
    rw [hz]
    positivity
  have hbn : b*n≠0 := mul_ne_zero hb hn
  have han : a*n≠0 := mul_ne_zero ha hn
  have he : (∑ x : ↥(b*n).divisorsAntidiagonal × ↥(a*n).divisorsAntidiagonal,
        a03DiagonalQuadSmallMajorant c (fixedPairQuad ⟨n,x⟩))=
      ((b*n).divisors.card:ℝ)*((a*n).divisors.card:ℝ)*
        ((b*n:ℕ):ℝ)^(-(1/2+3*c/4))*((a*n:ℕ):ℝ)^(-(1/2+3*c/4)) := by
    simp only [a03DiagonalQuadSmallMajorant_fixedPair]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,
      a03DivisorsAntidiagonal_card,nsmul_eq_mul,Nat.cast_mul]
    ring
  rw [he]
  calc
    _≤(B*((b*n:ℕ):ℝ)^(c/4))*(B*((a*n:ℕ):ℝ)^(c/4))*
        ((b*n:ℕ):ℝ)^(-(1/2+3*c/4))*((a*n:ℕ):ℝ)^(-(1/2+3*c/4)) := by
      gcongr
      · exact hdiv _ hbn
      · exact hdiv _ han
    _=B^2*((a*b:ℕ):ℝ)^(-(1/2+c/2))*(n:ℝ)^(-(1+c)) := by
      have hbp : (0:ℝ)<((b*n:ℕ):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hbn
      have hap : (0:ℝ)<((a*n:ℕ):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero han
      have hnp : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [show (B*((b*n:ℕ):ℝ)^(c/4))*(B*((a*n:ℕ):ℝ)^(c/4))*
        ((b*n:ℕ):ℝ)^(-(1/2+3*c/4))*((a*n:ℕ):ℝ)^(-(1/2+3*c/4))=
        B^2*(((b*n:ℕ):ℝ)^(c/4)*((b*n:ℕ):ℝ)^(-(1/2+3*c/4)))*
          (((a*n:ℕ):ℝ)^(c/4)*((a*n:ℕ):ℝ)^(-(1/2+3*c/4))) by ring,
        ←Real.rpow_add hbp,←Real.rpow_add hap,
        show c/4+(-(1/2+3*c/4))= -(1/2+c/2) by ring]
      simp only [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg b) (Nat.cast_nonneg n),
        Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg n),
        Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      rw [show B^2*((b:ℝ)^(-(1/2+c/2))*(n:ℝ)^(-(1/2+c/2)))*
        ((a:ℝ)^(-(1/2+c/2))*(n:ℝ)^(-(1/2+c/2)))=
        B^2*((a:ℝ)^(-(1/2+c/2))*(b:ℝ)^(-(1/2+c/2)))*
          ((n:ℝ)^(-(1/2+c/2))*(n:ℝ)^(-(1/2+c/2))) by ring,
        ←Real.rpow_add hnp,show -(1/2+c/2)+(-(1/2+c/2))= -(1+c) by ring]
    _≤_ := by
      have hpow : ((a*b:ℕ):ℝ)^(-(1/2+c/2))≤1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ha hb)) (by linarith)
      calc
        _≤B^2*1*(n:ℝ)^(-(1+c)) := by gcongr
        _=_ := by ring

theorem a03DiagonalQuadSmallMajorant_uniform_mass {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ,0≤D ∧ ∀ a b : ℕ,a≠0 → b≠0 →
      Summable (fun q : Fin 4→ℕ => if diagonalQuadRelation a b q then
        a03DiagonalQuadSmallMajorant c q else 0) ∧
      (∑' q : Fin 4→ℕ,if diagonalQuadRelation a b q then
        a03DiagonalQuadSmallMajorant c q else 0)≤D := by
  obtain ⟨B,hB,hfibre⟩ := a03DiagonalSmall_fibre_uniform_bound hc
  have hS : Summable (fun n : ℕ => (n:ℝ)^(-(1+c))) := Real.summable_nat_rpow.mpr (by linarith)
  let J : ℝ := ∑' n : ℕ,(n:ℝ)^(-(1+c))
  have hJ : 0≤J := tsum_nonneg (fun _ => by positivity)
  refine ⟨B*J,mul_nonneg hB hJ,?_⟩
  intro a b ha hb
  let g := Nat.gcd a b
  let a' := a/g
  let b' := b/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  have ha' : a'≠0 := (Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero ha)) hg).ne'
  have hb' : b'≠0 := (Nat.div_pos (Nat.gcd_le_right _ (Nat.pos_of_ne_zero hb)) hg).ne'
  have hab : a'.Coprime b' := Nat.coprime_div_gcd_div_gcd hg
  have hga : g*a'=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g*b'=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hrel (q : Fin 4→ℕ) : diagonalQuadRelation a b q↔diagonalQuadRelation a' b' q := by
    have hh : diagonalQuadRelation a b q↔diagonalQuadRelation (g*a') (g*b') q := by rw [hga,hgb]
    rw [hh]
    unfold diagonalQuadRelation
    convert Nat.mul_left_cancel_iff hg using 1
    ring_nf
  let F : FixedPairFibres a' b'→ℝ := fun x => a03DiagonalQuadSmallMajorant c (fixedPairQuad x)
  have hfs : Summable (fun n : ℕ => ∑ x : ↥(b'*n).divisorsAntidiagonal × ↥(a'*n).divisorsAntidiagonal,F ⟨n,x⟩) := by
    apply (hS.mul_left B).of_nonneg_of_le
    · intro n
      exact Finset.sum_nonneg (fun _ _ => a03DiagonalQuadSmallMajorant_nonneg _ _)
    · exact hfibre a' b' ha' hb'
  have hF : Summable F := (summable_sigma_of_nonneg (fun x => a03DiagonalQuadSmallMajorant_nonneg _ _)).mpr
    ⟨fun _ => (hasSum_fintype _).summable,by simpa only [tsum_fintype] using hfs⟩
  have hsub : Summable (fun q : {q : Fin 4→ℕ // diagonalQuadRelation a' b' q} =>
      a03DiagonalQuadSmallMajorant c q.val) := (fixedDiagonalPairFibresEquiv ha' hb' hab).summable_iff.mp hF
  have hsel : Summable (fun q : Fin 4→ℕ => if diagonalQuadRelation a' b' q then
      a03DiagonalQuadSmallMajorant c q else 0) := by
    exact (summable_subtype_iff_indicator (s:={q : Fin 4→ℕ|diagonalQuadRelation a' b' q})).mp hsub
  have he : (∑'q:Fin 4→ℕ,if diagonalQuadRelation a b q then a03DiagonalQuadSmallMajorant c q else 0)=
      ∑'x:FixedPairFibres a' b',F x := by
    simp only [hrel]
    have hs := (tsum_subtype {q:Fin 4→ℕ|diagonalQuadRelation a' b' q}
      (fun q => a03DiagonalQuadSmallMajorant c q)).symm
    simp only [Set.indicator_apply,Set.mem_ofPred_eq] at hs
    rw [hs]
    exact (fixedDiagonalPairFibresEquiv ha' hb' hab).tsum_eq _ |>.symm
  refine ⟨by simpa only [hrel] using hsel,?_⟩
  rw [he,hF.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fintype]
  exact (hfs.tsum_le_tsum (hfibre a' b' ha' hb') (hS.mul_left B)).trans_eq (by rw [tsum_mul_left])

theorem a03DiagonalSmallLine_denominator_norm_bound {c : ℝ} (_hc : 0<c)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤c/4) (v : ℝ) (q : Fin 4→ℕ) :
    ‖1/(∏ j : Fin 4,(q j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I)))‖≤
      a03DiagonalQuadSmallMajorant c q := by
  rw [one_div,norm_inv,norm_prod,←Finset.prod_inv_distrib]
  unfold a03DiagonalQuadSmallMajorant
  apply Finset.prod_le_prod₀ (fun _ _ => inv_nonneg.mpr (norm_nonneg _))
  intro j _
  rw [show (q j+1:ℂ)=((q j+1:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),←Real.rpow_neg (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤q j+1 by omega))
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  simp only [add_re,div_ofNat_re,one_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
    mul_zero,zero_mul,sub_zero,add_zero]
  linarith

theorem a03DiagonalSmallLine_smooth_grid_mass_bound {c : ℝ} (hc : 0<c) :
    ∃ D : ℝ,0≤D ∧ ∀ a b : ℕ,a≠0 → b≠0 → ∀ X : ℝ,
      (∑ k∈rectangularAFEProductScaleGrid X,∑ q∈rectangularAFESmoothBox k,
        rectangularAFESmoothWeight k q*(if diagonalQuadRelation a b q then
          a03DiagonalQuadSmallMajorant c q else 0))≤D := by
  obtain ⟨D,hD,hmass⟩ := a03DiagonalQuadSmallMajorant_uniform_mass hc
  refine ⟨D,hD,?_⟩
  intro a b ha hb X
  obtain ⟨hs,hbound⟩ := hmass a b ha hb
  let M : (Fin 4→ℕ)→ℝ := fun q => if diagonalQuadRelation a b q then a03DiagonalQuadSmallMajorant c q else 0
  have hM (q : Fin 4→ℕ) : 0≤M q := by dsimp [M]; split_ifs <;> first | exact a03DiagonalQuadSmallMajorant_nonneg _ _ | positivity
  have hsk (k : Fin 4→ℕ) : Summable (fun q => rectangularAFESmoothWeight k q*M q) := by
    apply hs.of_nonneg_of_le
    · intro q
      exact mul_nonneg (rectangular_AFE_smooth_weight_nonneg k q) (hM q)
    · intro q
      exact mul_le_of_le_one_left (hM q) (rectangular_small_contour_smooth_weight_le_one k q)
  have hp (q : Fin 4→ℕ) : (∑k∈rectangularAFEProductScaleGrid X,rectangularAFESmoothWeight k q*M q)≤M q := by
    rw [←Finset.sum_mul]
    apply mul_le_of_le_one_left (hM q)
    exact (rectangular_AFE_smooth_weight_hasSum q).summable.sum_le_tsum _
      (fun k _ => rectangular_AFE_smooth_weight_nonneg _ _) |>.trans_eq
        (rectangular_AFE_smooth_weight_hasSum q).tsum_eq
  have hsum : Summable (fun q : Fin 4→ℕ => ∑k∈rectangularAFEProductScaleGrid X,rectangularAFESmoothWeight k q*M q) :=
    hs.of_nonneg_of_le (fun q => Finset.sum_nonneg (fun k _ =>
      mul_nonneg (rectangular_AFE_smooth_weight_nonneg _ _) (hM q))) hp
  calc
    _≤∑ k∈rectangularAFEProductScaleGrid X,∑'q:Fin 4→ℕ,rectangularAFESmoothWeight k q*M q := by
      apply Finset.sum_le_sum
      intro k _
      exact (hsk k).sum_le_tsum _ (fun q _ => mul_nonneg (rectangular_AFE_smooth_weight_nonneg _ _) (hM q))
    _=∑'q:Fin 4→ℕ,∑ k∈rectangularAFEProductScaleGrid X,rectangularAFESmoothWeight k q*M q := by
      exact (Summable.tsum_finsetSum (fun k _ => hsk k)).symm
    _≤∑'q:Fin 4→ℕ,M q := by
      exact hsum.tsum_le_tsum hp hs
    _≤D := hbound

end
end SixthMoment

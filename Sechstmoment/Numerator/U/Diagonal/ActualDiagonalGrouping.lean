import Sechstmoment.Numerator.U.Diagonal.ActualTripleMellin

/-! Genuine source indexing: positive amplifier pairs and the four n+1 variables. -/

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

abbrev ActualPositiveAmplifierIndex := {m : ℕ // m ≠ 0}

abbrev ActualDiagonalSourceIndices :=
  (p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex) ×
    {q : Fin 4 → ℕ // diagonalQuadRelation p.1.val p.2.val q}

def actualDiagonalSourceIndicesEquiv : DiagonalSixIndices ≃ ActualDiagonalSourceIndices where
  toFun x := ⟨(⟨x.val.1.1,(diagonalSixIndices_components_ne_zero x).1⟩,
      ⟨x.val.2.1,(diagonalSixIndices_components_ne_zero x).2.2.2.1⟩),
    ⟨diagonalSixQuad x,diagonalSixQuad_source_relation x⟩⟩
  invFun x := ⟨((x.1.1.val,x.2.val 0+1,x.2.val 1+1),
      (x.1.2.val,x.2.val 2+1,x.2.val 3+1)),by
    constructor
    · simpa only [diagonalQuadRelation,mul_assoc] using x.2.property
    · exact mul_ne_zero x.1.1.property (by positivity)⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨h0,h1,h2,h3⟩ := diagonalSixQuad_positive_values x
    change ((x.val.1.1,diagonalSixQuad x 0+1,diagonalSixQuad x 1+1),
      (x.val.2.1,diagonalSixQuad x 2+1,diagonalSixQuad x 3+1))=x.val
    rw [h0,h1,h2,h3]
  right_inv x := by
    rcases x with ⟨⟨⟨m,hm⟩,⟨n,hn⟩⟩,⟨q,hq⟩⟩
    have hv : diagonalSixQuad
        ⟨((m,q 0+1,q 1+1),(n,q 2+1,q 3+1)),by
          constructor
          · simpa only [diagonalQuadRelation,mul_assoc] using hq
          · exact mul_ne_zero hm (by positivity)⟩ = q := by
      funext j
      fin_cases j <;> simp [diagonalSixQuad]
    dsimp only
    congr 1
    exact Subtype.ext hv

def actualSourceAmplifiedDiagonalTerm (G : ℂ → ℂ) (α : MomentShifts) (f g : ℝ → ℂ)
    (L t : ℝ) (x : ActualDiagonalSourceIndices) : ℂ :=
  f (Real.log x.1.1.val/L)*g (Real.log x.1.2.val/L)*
    bblrDiagonalSummand G α x.1.1.val x.1.2.val t x.2.val

theorem actualSourceAmplifiedDiagonalTerm_norm_summable {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    Summable (fun x : ActualDiagonalSourceIndices =>
      ‖actualSourceAmplifiedDiagonalTerm G α f g L t x‖) := by
  apply actualDiagonalSourceIndicesEquiv.summable_iff.mp
  exact actualSourceSixDiagonal_norm_summable ht G α hG hf hfs hg hgs hL hδ hδ1 hα

theorem actualAmplifiedDiagonal_eq_sourceSix {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    (∑' p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex,
      f (Real.log p.1.val/L)*g (Real.log p.2.val/L)*bblrDiagonalTerm G α p.1.val p.2.val t) =
      ∑' x : DiagonalSixIndices,
        f (Real.log x.val.1.1/L)*g (Real.log x.val.2.1/L)*
          bblrDiagonalSummand G α x.val.1.1 x.val.2.1 t (diagonalSixQuad x) := by
  have hn := actualSourceAmplifiedDiagonalTerm_norm_summable ht G α hG hf hfs hg hgs hL hδ hδ1 hα
  have hs := hn.of_norm
  have hinner : ∀ p, Summable (fun q => actualSourceAmplifiedDiagonalTerm G α f g L t ⟨p,q⟩) := by
    intro p
    exact (((summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hn).1 p).of_norm
  calc
    _ = ∑' p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex,
      ∑' q : {n : Fin 4 → ℕ // diagonalQuadRelation p.1.val p.2.val n},
        actualSourceAmplifiedDiagonalTerm G α f g L t ⟨p,q⟩ := by
      apply tsum_congr
      intro p
      unfold actualSourceAmplifiedDiagonalTerm bblrDiagonalTerm
      change (f (Real.log p.1.val/L)*g (Real.log p.2.val/L))*
        (∑' n : Fin 4 → ℕ, if diagonalQuadRelation p.1.val p.2.val n then
          bblrDiagonalSummand G α p.1.val p.2.val t n else 0) =
        ∑' q : {n : Fin 4 → ℕ // diagonalQuadRelation p.1.val p.2.val n},
          (f (Real.log p.1.val/L)*g (Real.log p.2.val/L))*
            bblrDiagonalSummand G α p.1.val p.2.val t q.val
      rw [tsum_mul_left]
      congr 1
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Set.coe_ofPred] using
        (tsum_subtype {n : Fin 4 → ℕ | diagonalQuadRelation p.1.val p.2.val n}
          (fun n => bblrDiagonalSummand G α p.1.val p.2.val t n)).symm
    _ = ∑' x : ActualDiagonalSourceIndices, actualSourceAmplifiedDiagonalTerm G α f g L t x :=
      (hs.tsum_sigma' hinner).symm
    _ = _ := (actualDiagonalSourceIndicesEquiv.tsum_eq _).symm

theorem actualAmplifiedDiagonal_eq_MellinEuler {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    (∑' p : ActualPositiveAmplifierIndex × ActualPositiveAmplifierIndex,
      f (Real.log p.1.val/L)*g (Real.log p.2.val/L)*bblrDiagonalTerm G α p.1.val p.2.val t) =
      (1/(2*π):ℂ)*((L:ℂ)/(2*π))^2*
        ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α f g L δ t w
          ∂(volume.prod (volume.prod volume)) := by
  rw [actualAmplifiedDiagonal_eq_sourceSix ht G α hG hf hfs hg hgs hL hδ hδ1 hα,
    actualSourceSixDiagonal_eq_MellinEuler ht G α hG hf hfs hg hgs hL hδ hδ1 hα]

end
end Sechstmoment

import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Sechstmoment.Zeta.AFE.Four.Definitions


namespace Sechstmoment.Source
open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical

noncomputable section

def BBLRv1FixedApproximateFEInput : Prop :=
  ∀ G : ℂ → ℂ, BBLREntireWeight G (fun _ => 0) →
  ∀ K : Set MomentShifts, IsCompact K → ∀ A : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrAFEDiscrepancy G (rawMomentShifts T σ) t‖ ≤ C*T^(-(A : ℝ))

def bblrVerticalIntegrand (G : ℂ → ℂ) (α : MomentShifts) (x t v : ℝ) : ℂ :=
  let z : ℂ := 1+(v : ℂ)*I
  G z/z*bblrGammaQuotient t α z*(Real.pi : ℂ)^(-2*z)*(x : ℂ)^(-z)

def finiteAuxiliaryCombination {m : ℕ} (w : Fin m → ℂ)
    (G : Fin m → ℂ → ℂ) : ℂ → ℂ := fun z => ∑ i, w i*G i z

theorem bblrV_finite_combination {m : ℕ} (w : Fin m → ℂ)
    (G : Fin m → ℂ → ℂ) (α : MomentShifts) (x t : ℝ)
    (hI : ∀ i, Integrable (bblrVerticalIntegrand (G i) α x t)) :
    bblrV (finiteAuxiliaryCombination w G) α x t = ∑ i, w i*bblrV (G i) α x t := by
  have he (v : ℝ) :
      bblrVerticalIntegrand (finiteAuxiliaryCombination w G) α x t v =
        ∑ i, w i*bblrVerticalIntegrand (G i) α x t v := by
    simp only [bblrVerticalIntegrand, finiteAuxiliaryCombination, Finset.sum_div,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change (1/(2*Real.pi) : ℂ)*(∫ v : ℝ,
    bblrVerticalIntegrand (finiteAuxiliaryCombination w G) α x t v) = _
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => (hI i).const_mul (w i))]
  simp only [integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (1/(2*Real.pi) : ℂ)*(w i*∫ v, bblrVerticalIntegrand (G i) α x t v) =
    w i*((1/(2*Real.pi) : ℂ)*∫ v, bblrVerticalIntegrand (G i) α x t v)
  ring

theorem bblrAFESummand_finite_combination {m : ℕ} (w : Fin m → ℂ)
    (G : Fin m → ℂ → ℂ) (α : MomentShifts) (t : ℝ) (n : Fin 4 → ℕ)
    (hI : ∀ i, Integrable
      (bblrVerticalIntegrand (G i) α (positiveQuadProduct n) t)) :
    bblrAFESummand (finiteAuxiliaryCombination w G) α t n =
      ∑ i, w i*bblrAFESummand (G i) α t n := by
  unfold bblrAFESummand
  rw [bblrV_finite_combination w G α _ t hI]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem bblrAFESum_finite_combination {m : ℕ} (w : Fin m → ℂ)
    (G : Fin m → ℂ → ℂ) (α : MomentShifts) (t : ℝ)
    (hI : ∀ i n, Integrable
      (bblrVerticalIntegrand (G i) α (positiveQuadProduct n) t))
    (hS : ∀ i, Summable (bblrAFESummand (G i) α t)) :
    bblrAFESum (finiteAuxiliaryCombination w G) α t =
      ∑ i, w i*bblrAFESum (G i) α t := by
  unfold bblrAFESum
  simp_rw [bblrAFESummand_finite_combination w G α t _ (fun i => hI i _)]
  rw [Summable.tsum_finsetSum (fun i _ => (hS i).mul_left (w i))]
  simp_rw [tsum_mul_left]

theorem bblrAFEDiscrepancy_finite_combination {m : ℕ} (w : Fin m → ℂ)
    (G : Fin m → ℂ → ℂ) (α : MomentShifts) (t : ℝ) (hw : ∑ i, w i = 1)
    (hI : ∀ i n, Integrable
      (bblrVerticalIntegrand (G i) α (positiveQuadProduct n) t))
    (hId : ∀ i n, Integrable
      (bblrVerticalIntegrand (G i) (bblrSixShifts α 1) (positiveQuadProduct n) t))
    (hS : ∀ i, Summable (bblrAFESummand (G i) α t))
    (hSd : ∀ i, Summable (bblrAFESummand (G i) (bblrSixShifts α 1) t)) :
    bblrAFEDiscrepancy (finiteAuxiliaryCombination w G) α t =
      ∑ i, w i*bblrAFEDiscrepancy (G i) α t := by
  unfold bblrAFEDiscrepancy
  rw [bblrAFESum_finite_combination w G α t hI hS,
    bblrAFESum_finite_combination w G (bblrSixShifts α 1) t hId hSd]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]
  rw [← Finset.sum_mul, hw, one_mul]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def BBLRFiniteBasisAnalyticReceipt {m : ℕ} (G : Fin m → ℂ → ℂ)
    (w : ℝ → MomentShifts → Fin m → ℂ) (K : Set MomentShifts) : Prop :=
  ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
    (∑ i, w T σ i = 1) ∧
    (∀ i n, Integrable (bblrVerticalIntegrand (G i) (rawMomentShifts T σ)
      (positiveQuadProduct n) t)) ∧
    (∀ i n, Integrable (bblrVerticalIntegrand (G i)
      (bblrSixShifts (rawMomentShifts T σ) 1) (positiveQuadProduct n) t)) ∧
    (∀ i, Summable (bblrAFESummand (G i) (rawMomentShifts T σ) t)) ∧
    (∀ i, Summable (bblrAFESummand (G i)
      (bblrSixShifts (rawMomentShifts T σ) 1) t))

theorem bblrAFE_fixed_basis_uniform_remainder {m : ℕ}
    (hsource : BBLRv1FixedApproximateFEInput) (G : Fin m → ℂ → ℂ)
    (hG : ∀ i, BBLREntireWeight (G i) (fun _ => 0))
    (K : Set MomentShifts) (hK : IsCompact K)
    (w : ℝ → MomentShifts → Fin m → ℂ)
    (hreceipt : BBLRFiniteBasisAnalyticReceipt G w K)
    (r : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hw : ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∑ i, ‖w T σ i‖ ≤ D*T^r)
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrAFEDiscrepancy (finiteAuxiliaryCombination (w T σ) G)
        (rawMomentShifts T σ) t‖ ≤ C*T^(-(A : ℝ)) := by
  choose C hC0 hC using fun i => hsource (G i) (hG i) K hK (A+r)
  let Csum : ℝ := ∑ i, C i
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun i _ => hC0 i)
  have hCi : ∀ i, C i ≤ Csum := fun i =>
    Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
  refine ⟨Csum*D, mul_nonneg hCsum hD, ?_⟩
  have hCall : ∀ᶠ T : ℝ in atTop, ∀ i, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrAFEDiscrepancy (G i) (rawMomentShifts T σ) t‖ ≤
        C i*T^(-((A+r : ℕ) : ℝ)) := Filter.eventually_all.mpr hC
  filter_upwards [hCall, hreceipt, hw, eventually_gt_atTop (0 : ℝ)] with T hT hR hW hpos
  intro σ hσ t ht
  obtain ⟨hweights, hI, hId, hS, hSd⟩ := hR σ hσ t ht
  rw [bblrAFEDiscrepancy_finite_combination (w T σ) G (rawMomentShifts T σ)
    t hweights hI hId hS hSd]
  have hp : T^(-((A+r : ℕ) : ℝ)) ≥ 0 := (Real.rpow_pos_of_pos hpos _).le
  have hpower : T^(-((A+r : ℕ) : ℝ))*T^r = T^(-(A : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
    congr 1
    push_cast
    ring
  calc
    ‖∑ i, w T σ i*bblrAFEDiscrepancy (G i) (rawMomentShifts T σ) t‖
        ≤ ∑ i, ‖w T σ i‖*‖bblrAFEDiscrepancy (G i) (rawMomentShifts T σ) t‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ
        (fun i => w T σ i*bblrAFEDiscrepancy (G i) (rawMomentShifts T σ) t)
    _ ≤ ∑ i, ‖w T σ i‖*(Csum*T^(-((A+r : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (hT i σ hσ t ht).trans (mul_le_mul_of_nonneg_right (hCi i) hp)
    _ = (Csum*T^(-((A+r : ℕ) : ℝ)))*∑ i, ‖w T σ i‖ := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (Csum*T^(-((A+r : ℕ) : ℝ)))*(D*T^r) :=
      mul_le_mul_of_nonneg_left (hW σ hσ) (mul_nonneg hCsum hp)
    _ = (Csum*D)*T^(-(A : ℝ)) := by
      rw [show Csum*T^(-((A+r : ℕ) : ℝ))*(D*T^r) =
        (Csum*D)*(T^(-((A+r : ℕ) : ℝ))*T^r) by ring, hpower]

end
end Sechstmoment.Source

import Sechstmoment.Arithmetic.Watt.Adapters


namespace DivisorProof
namespace Watt41
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def complexInnerSum (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f : ℕ → ℕ → ℝ → ℂ) (r s : ℕ) : ℂ :=
  ∑ h ∈ positiveRange q.H, ∑ k ∈ positiveRange q.K,
    ∑ l ∈ positiveRange q.L, α h*β k*w l*
      ∑ p ∈ (positiveRange q.P).filter (fun p => p.Coprime r),
        f r s p*classicalKloostermanSum
          ((h : ℤ)*k*inverseRepresentative r (p*s)) (σ*l) (p*s)

def complexWeightedSum (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℂ) : ℂ :=
  ∑ rs ∈ pairRange q, a rs.1*b rs.2*complexInnerSum q σ α β w f rs.1 rs.2

theorem complexInnerSum_ofReal (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f : ℕ → ℕ → ℝ → ℝ) (r s : ℕ) :
    complexInnerSum q σ α β w (fun r s x => (f r s x : ℂ)) r s =
      innerSum q σ α β w f r s := rfl

theorem complexWeightedSum_ofReal (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ) :
    complexWeightedSum q σ a b α β w (fun r s x => (f r s x : ℂ)) =
      weightedSum q σ a b α β w f := rfl

theorem complexInnerSum_add (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f g : ℕ → ℕ → ℝ → ℂ) (r s : ℕ) :
    complexInnerSum q σ α β w (fun r s x => f r s x+g r s x) r s =
      complexInnerSum q σ α β w f r s+complexInnerSum q σ α β w g r s := by
  simp only [complexInnerSum, add_mul, mul_add, sum_add_distrib]

theorem complexInnerSum_const_mul (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f : ℕ → ℕ → ℝ → ℂ) (z : ℂ) (r s : ℕ) :
    complexInnerSum q σ α β w (fun r s x => z*f r s x) r s =
      z*complexInnerSum q σ α β w f r s := by
  simp only [complexInnerSum, mul_sum]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro p _
  ring

theorem complexWeightedSum_add (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f g : ℕ → ℕ → ℝ → ℂ) :
    complexWeightedSum q σ a b α β w (fun r s x => f r s x+g r s x) =
      complexWeightedSum q σ a b α β w f+complexWeightedSum q σ a b α β w g := by
  simp only [complexWeightedSum, complexInnerSum_add, mul_add, sum_add_distrib]

theorem complexWeightedSum_const_mul (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℂ) (z : ℂ) :
    complexWeightedSum q σ a b α β w (fun r s x => z*f r s x) =
      z*complexWeightedSum q σ a b α β w f := by
  simp only [complexWeightedSum, complexInnerSum_const_mul, mul_sum]
  apply sum_congr rfl
  intro rs _
  ring

theorem complexWeightedSum_re_im (q : Scales) (σ : ℤ) (a b : ℕ → ℂ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℂ) :
    complexWeightedSum q σ a b α β w f =
      weightedSum q σ a b α β w (fun r s x => (f r s x).re)+
        Complex.I*weightedSum q σ a b α β w (fun r s x => (f r s x).im) := by
  have heq : f = fun r s x => ((f r s x).re : ℂ)+Complex.I*((f r s x).im : ℂ) := by
    funext r s x
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (f r s x)).symm
  conv_lhs => rw [heq]
  rw [complexWeightedSum_add,complexWeightedSum_const_mul,
    complexWeightedSum_ofReal,complexWeightedSum_ofReal]

theorem iteratedDeriv_re {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun x => (f x).re) x = (iteratedDeriv j f x).re := by
  change iteratedDeriv j (Complex.reCLM ∘ f) x = _
  rw [iteratedDeriv_eq_iteratedFDeriv,
    Complex.reCLM.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  rfl

theorem iteratedDeriv_im {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun x => (f x).im) x = (iteratedDeriv j f x).im := by
  change iteratedDeriv j (Complex.imCLM ∘ f) x = _
  rw [iteratedDeriv_eq_iteratedFDeriv,
    Complex.imCLM.iteratedFDeriv_comp_left hf.contDiffAt (by simp)]
  rfl

end
end Watt41

noncomputable section

theorem Watt41.complexWeighted (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
    (b fbound : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (hf : ∀ j, 0 ≤ fbound j) :
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 1 ≤ X₀ ∧
      ∀ (q : Watt41.Scales) (δ : ℝ) (σ : ℤ) (a bcoeff : ℕ → ℂ)
        (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℂ),
        (∀ i, 1 ≤ q.size i) → 0 < δ → (σ = -1 ∨ σ = 1) →
        Watt41.WeightData b fbound q δ α β w (fun r s x => (f r s x).re) →
        Watt41.WeightData b fbound q δ α β w (fun r s x => (f r s x).im) →
        (∀ r, ‖a r‖ ≤ 1) → (∀ s, ‖bcoeff s‖ ≤ 1) →
        max (q.H^2*q.K) q.L ≤ q.Q^2 → X₀ ≤ q.X →
        ‖Watt41.complexWeightedSum q σ a bcoeff α β w f‖ ≤ C*Watt41.majorant q δ ε := by
  obtain ⟨C,X₀,hC,hX₀,hbound⟩ := hWatt.weighted hε b fbound hb hf
  refine ⟨2*C,X₀,by positivity,hX₀,?_⟩
  intro q δ σ a bcoeff α β w f hsize hδ hσ hre him ha hbc hnum hlarge
  have hr := hbound q δ σ a bcoeff α β w (fun r s x => (f r s x).re)
    hsize hδ hσ hre ha hbc hnum hlarge
  have hi := hbound q δ σ a bcoeff α β w (fun r s x => (f r s x).im)
    hsize hδ hσ him ha hbc hnum hlarge
  rw [Watt41.complexWeightedSum_re_im]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,one_mul]
  linarith

end
end DivisorProof

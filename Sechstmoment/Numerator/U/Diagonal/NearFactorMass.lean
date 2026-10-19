import Sechstmoment.Numerator.U.Diagonal.NearFactorCount

/-!
# Weighted mass of the genuine four-variable near set

This is the arithmetic mass behind a pointwise `1/T` weight or dual-phase
error. Both products are localized below and above; all four AFE variables
are summed. The proof uses the unconditional near-fiber counting theorem,
not an assumed mass bound. The short-interval endpoint term is retained.
-/

namespace Sechstmoment
open scoped BigOperators
open Classical
noncomputable section

/-- The actual lower-localized near set, with all four positive AFE variables. -/
def positiveNearFactorBlock (L P J Q u v H : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (positiveNearFactorRectangle P Q u v H).filter fun pq =>
    L≤pq.1.1*pq.1.2 ∧ J≤pq.2.1*pq.2.2

/-- The true reciprocal square-root weight, including amplifier denominators. -/
def positiveNearFactorWeight (u v : ℕ) (pq : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  1/Real.sqrt ((u:ℝ)*v*(pq.1.1*pq.1.2 : ℕ)*(pq.2.1*pq.2.2 : ℕ))

theorem positiveNearFactorWeight_nonneg (u v : ℕ)
    (pq : (ℕ × ℕ) × (ℕ × ℕ)) : 0≤positiveNearFactorWeight u v pq := by
  unfold positiveNearFactorWeight
  positivity

/-- Counting may choose either product orientation without changing the set. -/
theorem positiveNearFactorBlock_swap_mem {L P J Q u v H : ℕ}
    {pq : (ℕ × ℕ) × (ℕ × ℕ)} :
    pq.swap ∈ positiveNearFactorBlock J Q L P v u H ↔
      pq ∈ positiveNearFactorBlock L P J Q u v H := by
  constructor
  · intro h
    obtain ⟨hrect,hlo⟩ := Finset.mem_filter.mp h
    obtain ⟨hq,hpf⟩ := mem_positiveNearFactorRectangle.mp hrect
    obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp hpf
    exact Finset.mem_filter.mpr ⟨mem_positiveNearFactorRectangle.mpr
      ⟨hp,Finset.mem_filter.mpr ⟨hq,hnear.2,hnear.1⟩⟩,hlo.2,hlo.1⟩
  · intro h
    obtain ⟨hrect,hlo⟩ := Finset.mem_filter.mp h
    obtain ⟨hp,hqf⟩ := mem_positiveNearFactorRectangle.mp hrect
    obtain ⟨hq,hnear⟩ := Finset.mem_filter.mp hqf
    exact Finset.mem_filter.mpr ⟨mem_positiveNearFactorRectangle.mpr
      ⟨hq,Finset.mem_filter.mpr ⟨hp,hnear.2,hnear.1⟩⟩,hlo.2,hlo.1⟩

theorem positiveNearFactorBlock_swap (L P J Q u v H : ℕ) :
    (positiveNearFactorBlock L P J Q u v H).image Prod.swap =
      positiveNearFactorBlock J Q L P v u H := by
  ext pq
  constructor
  · intro h
    obtain ⟨ab,hab,rfl⟩ := Finset.mem_image.mp h
    exact positiveNearFactorBlock_swap_mem.mpr hab
  · intro h
    exact Finset.mem_image.mpr ⟨pq.swap,
      positiveNearFactorBlock_swap_mem.mpr h,Prod.swap_swap pq⟩

theorem positiveNearFactorWeight_swap (u v : ℕ)
    (pq : (ℕ × ℕ) × (ℕ × ℕ)) :
    positiveNearFactorWeight v u pq.swap=positiveNearFactorWeight u v pq := by
  unfold positiveNearFactorWeight
  congr 2
  dsimp [Prod.swap]
  ring

/-- The complete true weighted mass is invariant under product orientation. -/
theorem positiveNearFactorBlock_mass_swap (L P J Q u v H : ℕ) :
    (∑ pq ∈ positiveNearFactorBlock J Q L P v u H,
      positiveNearFactorWeight v u pq)=
    (∑ pq ∈ positiveNearFactorBlock L P J Q u v H,
      positiveNearFactorWeight u v pq) := by
  rw [← positiveNearFactorBlock_swap L P J Q u v H,
    Finset.sum_image (by intro x _ y _ h; exact Prod.swap_injective h)]
  apply Finset.sum_congr rfl
  intro pq hpq
  exact positiveNearFactorWeight_swap u v pq

theorem positiveNearFactorWeight_le_block {L P J Q u v H : ℕ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J)
    {pq : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpq : pq ∈ positiveNearFactorBlock L P J Q u v H) :
    positiveNearFactorWeight u v pq≤1/Real.sqrt ((u:ℝ)*v*L*J) := by
  have hlo := (Finset.mem_filter.mp hpq).2
  have hLreal : (L:ℝ)≤(pq.1.1*pq.1.2 : ℕ) := by exact_mod_cast hlo.1
  have hJreal : (J:ℝ)≤(pq.2.1*pq.2.2 : ℕ) := by exact_mod_cast hlo.2
  have hbase : 0<(u:ℝ)*v*L*J := by positivity
  unfold positiveNearFactorWeight
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hbase)
  apply Real.sqrt_le_sqrt
  gcongr

/-- Actual complete weighted near-block mass, proved from factor counts. -/
theorem positiveNearFactorBlock_mass_le_harmonic {L P J Q u v H K : ℕ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2) :
    (∑ pq ∈ positiveNearFactorBlock L P J Q u v H,
      positiveNearFactorWeight u v pq) ≤
      (P:ℝ)*(harmonic P : ℝ)*
        (2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K)/
          Real.sqrt ((u:ℝ)*v*L*J) := by
  have hcard : ((positiveNearFactorBlock L P J Q u v H).card : ℝ)≤
      ((positiveNearFactorRectangle P Q u v H).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le (positiveNearFactorRectangle P Q u v H)
      (fun pq => L≤pq.1.1*pq.1.2 ∧ J≤pq.2.1*pq.2.2)
  calc
    _ ≤ ∑ _pq ∈ positiveNearFactorBlock L P J Q u v H,
        1/Real.sqrt ((u:ℝ)*v*L*J) :=
      Finset.sum_le_sum (fun _ h => positiveNearFactorWeight_le_block hu hv hL hJ h)
    _ = ((positiveNearFactorBlock L P J Q u v H).card : ℝ)/
        Real.sqrt ((u:ℝ)*v*L*J) := by simp [div_eq_mul_inv]
    _ ≤ ((positiveNearFactorRectangle P Q u v H).card : ℝ)/
        Real.sqrt ((u:ℝ)*v*L*J) :=
      div_le_div_of_nonneg_right hcard (Real.sqrt_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_right
      (positiveNearFactorRectangle_card_le_harmonic hv hQ) (Real.sqrt_nonneg _)

/-- The same genuine weighted mass with its logarithmic majorant. -/
theorem positiveNearFactorBlock_mass_le_log {L P J Q u v H K : ℕ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2) :
    (∑ pq ∈ positiveNearFactorBlock L P J Q u v H,
      positiveNearFactorWeight u v pq) ≤
      (P:ℝ)*(1+Real.log (P:ℝ))*
        (2*(2*(H:ℝ)/(v:ℝ)+1)*(1+Real.log (K:ℝ))+2*K)/
          Real.sqrt ((u:ℝ)*v*L*J) := by
  have hharm (N : ℕ) : 0≤(harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hlog (N : ℕ) : 0≤1+Real.log (N:ℝ) :=
    (hharm N).trans (harmonic_le_one_add_log N)
  apply (positiveNearFactorBlock_mass_le_harmonic hu hv hL hJ hQ).trans
  gcongr
  · have hk := hharm K
    positivity
  · exact harmonic_le_one_add_log P
  · exact harmonic_le_one_add_log K

/-- The actual amplifier indices and all four AFE variables are summed.
Only integer support and product localization assumptions enter. -/
theorem amplifiedPositiveNearFactorBlock_mass_le_harmonic
    {U A V B L P J Q H K : ℕ}
    (hU : 0<U) (hV : 0<V) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2) :
    (∑ uv ∈ (Finset.Icc U A) ×ˢ (Finset.Icc V B),
      ∑ pq ∈ positiveNearFactorBlock L P J Q uv.1 uv.2 H,
        positiveNearFactorWeight uv.1 uv.2 pq) ≤
      (((A+1-U)*(B+1-V) : ℕ):ℝ)*(P:ℝ)*(harmonic P : ℝ)*
        (2*(2*(H:ℝ)/(V:ℝ)+1)*(harmonic K : ℝ)+2*K)/
          Real.sqrt ((U:ℝ)*V*L*J) := by
  have hharm (N : ℕ) : 0≤(harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  let C : ℝ := (P:ℝ)*(harmonic P : ℝ)*
    (2*(2*(H:ℝ)/(V:ℝ)+1)*(harmonic K : ℝ)+2*K)/
      Real.sqrt ((U:ℝ)*V*L*J)
  have hPK := hharm P
  have hKK := hharm K
  have hbound (uv : ℕ × ℕ) (huv : uv ∈ (Finset.Icc U A) ×ˢ (Finset.Icc V B)) :
      (∑ pq ∈ positiveNearFactorBlock L P J Q uv.1 uv.2 H,
        positiveNearFactorWeight uv.1 uv.2 pq)≤C := by
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
    have huU := (Finset.mem_Icc.mp hu).1
    have hvV := (Finset.mem_Icc.mp hv).1
    have hup : 0<uv.1 := hU.trans_le huU
    have hvp : 0<uv.2 := hV.trans_le hvV
    apply (positiveNearFactorBlock_mass_le_harmonic hup hvp hL hJ hQ).trans
    dsimp [C]
    gcongr
  calc
    _ ≤ ∑ _uv ∈ (Finset.Icc U A) ×ˢ (Finset.Icc V B), C :=
      Finset.sum_le_sum hbound
    _ = _ := by simp [C, Finset.card_product, Nat.card_Icc]; ring

end
end Sechstmoment

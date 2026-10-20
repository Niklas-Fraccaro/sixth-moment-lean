import Sechstmoment.Denominator.Balanced.ZetaGaussianPair

namespace Sechstmoment
open Complex Real Source Filter Set
open scoped BigOperators Topology
noncomputable section

def d02ActualPairCut (X : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range ⌊X⌋₊).product (Finset.range ⌊X⌋₊)).filter
    (fun n => d02PositivePairProduct n≤X)

theorem d02ActualPairCut_mem_iff {X : ℝ} (hX : 0<X) (n : ℕ × ℕ) :
    n∈d02ActualPairCut X ↔ d02PositivePairProduct n≤X := by
  classical
  simp only [d02ActualPairCut,Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    have hm : (n.1+1:ℝ)≤X := by
      unfold d02PositivePairProduct at h
      calc
        _ = (n.1+1:ℝ)*1 := by ring
        _ ≤ (n.1+1:ℝ)*(n.2+1:ℝ) :=
          mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) n.2]) (by positivity)
        _ ≤ X := h
    have hn : (n.2+1:ℝ)≤X := by
      unfold d02PositivePairProduct at h
      calc
        _ = 1*(n.2+1:ℝ) := by ring
        _ ≤ (n.1+1:ℝ)*(n.2+1:ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) n.1]) (by positivity)
        _ ≤ X := h
    have hm' : n.1+1≤⌊X⌋₊ := (Nat.le_floor_iff hX.le).mpr (by exact_mod_cast hm)
    have hn' : n.2+1≤⌊X⌋₊ := (Nat.le_floor_iff hX.le).mpr (by exact_mod_cast hn)
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,h⟩

theorem d02ActualGaussianPair_truncation_norm_bound {s r : ℂ} {t X A b : ℝ}
    (ht : 0<t) (hX : t/(2*Real.pi)≤X) (hA : 0≤A) (hAb : 2≤A+b)
    (hs : b≤s.re) (hr : b≤r.re) :
    ‖(∑' n : ℕ × ℕ,d02ActualGaussianSummand s r t n)-
      (∑ n∈d02ActualPairCut X,d02ActualGaussianSummand s r t n)‖≤
      ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
        (t/(2*Real.pi))^A*X^(2-b-A))*d02PairMass := by
  classical
  have hY : 0<t/(2*Real.pi) := by positivity
  have hXp : 0<X := hY.trans_le hX
  let f : ℕ × ℕ → ℂ := d02ActualGaussianSummand s r t
  let a : ℕ × ℕ → ℂ := d02ActualPairCoefficient s r
  have ha : ∀ n,‖a n‖≤(d02PositivePairProduct n)^(-b) :=
    d02ActualPairCoefficient_norm_le hs hr
  have hf : Summable f := d02ActualGaussianSummand_summable ht hs hr hA (by linarith)
  have htail := d02GaussianLongTail_summable a hY hX hAb ha
  let P := d02ActualPairCut X
  have he : (∑' n : ℕ × ℕ,f n)-(∑ n∈P,f n) = ∑' n : ↑(P : Set (ℕ × ℕ))ᶜ,f n := by
    have h := hf.sum_add_tsum_compl (s := P)
    linear_combination -h
  change ‖(∑' n : ℕ × ℕ,f n)-(∑ n∈P,f n)‖≤_
  rw [he]
  have hnorm (n : ↑(P : Set (ℕ × ℕ))ᶜ) :
      ‖f n‖=d02GaussianLongTail a X (t/(2*Real.pi)) n := by
    have hn : X<d02PositivePairProduct n := by
      apply lt_of_not_ge
      intro h
      exact n.property ((d02ActualPairCut_mem_iff hXp n).mpr h)
    unfold f d02ActualGaussianSummand d02GaussianLongTail
    rw [ite_eq_left hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0≤d02GaussianV0 (2*Real.pi*d02PositivePairProduct n/t) from
        d02GaussianTail_nonneg _)]
    congr 2
    field_simp
  calc
    _ ≤ ∑' n : ↑(P : Set (ℕ × ℕ))ᶜ,‖f n‖ := norm_tsum_le_tsum_norm (hf.subtype (fun n => n∈(P : Set (ℕ × ℕ))ᶜ)).norm
    _ = ∑' n : ↑(P : Set (ℕ × ℕ))ᶜ,d02GaussianLongTail a X (t/(2*Real.pi)) n :=
      tsum_congr hnorm
    _ ≤ ∑' n : ℕ × ℕ,d02GaussianLongTail a X (t/(2*Real.pi)) n :=
      Summable.tsum_subtype_le _ _ (fun n => by
        unfold d02GaussianLongTail
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (d02GaussianTail_nonneg _)
        · exact le_rfl) htail
    _ ≤ _ := d02GaussianLongTail_tsum_bound a hY hX hAb ha

theorem d02ActualGaussianPair_truncation_arbitrary_power {R ε δ B : ℝ}
    (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ) (hB : 0≤B) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ t∈Icc T (2*T),
      ∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
        ‖d02ActualGaussianPair t (rawSecondMomentShifts T σ)-
          (∑ n∈d02ActualPairCut (T^(1+δ)),d02ActualGaussianSummand
            (secondSourceZetaPoints t 0+rawSecondMomentShifts T σ 0)
            (secondSourceZetaPoints t 1+rawSecondMomentShifts T σ 1) t n)‖≤C*T^(-B) := by
  let b : ℝ := 1/2-ε
  let A : ℝ := ((1+δ)*(2-b)+B)/δ+2
  let C : ℝ := (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*d02PairMass
  have hb : 0≤b := by dsimp [b]; linarith
  have hb2 : 0<2-b := by dsimp [b]; linarith
  have hnumer : 0≤(1+δ)*(2-b)+B := by positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hAb : 2≤A+b := by
    dsimp [A]
    linarith [div_nonneg hnumer hδ.le]
  have hexponent : A+(1+δ)*(2-b-A)≤-B := by
    have he : A+(1+δ)*(2-b-A)=-B-2*δ := by
      dsimp [A]
      field_simp [hδ.ne']
      ring
    rw [he]
    linarith
  refine ⟨C,by dsimp [C]; exact mul_nonneg (by positivity) d02PairMass_nonneg,?_⟩
  filter_upwards [d02RawSecondMomentShifts_eventually_small hε,
    eventually_ge_atTop (1:ℝ)] with T hsmall hT
  intro t ht σ hσ
  have hTp : 0<T := zero_lt_one.trans_le hT
  have htp : 0<t := hTp.trans_le ht.1
  have hα := hsmall σ hσ
  have hs := d02SecondZetaPoints_re_bounds hε1 hα t 0
  have hr := d02SecondZetaPoints_re_bounds hε1 hα t 1
  have hYT : t/(2*Real.pi)≤T := by
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    have hπ : (1:ℝ)≤Real.pi := by linarith [Real.pi_gt_three]
    have hmul := mul_le_mul_of_nonneg_right hπ hTp.le
    nlinarith [ht.2]
  have hTX : T≤T^(1+δ) := by
    conv_lhs => rw [←Real.rpow_one T]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hbound := d02ActualGaussianPair_truncation_norm_bound htp (hYT.trans hTX)
    hA hAb hs.1 hr.1
  apply hbound.trans
  calc
    _ ≤ ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
        T^A*(T^(1+δ))^(2-b-A))*d02PairMass := by
      gcongr
      exact d02PairMass_nonneg
    _ = C*(T^A*(T^(1+δ))^(2-b-A)) := by
      dsimp [C]
      ring
    _ = C*T^(A+(1+δ)*(2-b-A)) := by
      rw [←Real.rpow_mul hTp.le,←Real.rpow_add hTp]
    _ ≤ C*T^(-B) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hexponent)
      (by dsimp [C]; exact mul_nonneg (by positivity) d02PairMass_nonneg)

def d02ActualGaussianFinitePair (t : ℝ) (α : SecondMomentShifts) (X : ℝ) : ℂ :=
  ∑ n∈d02ActualPairCut X,d02ActualGaussianSummand
    (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) t n

def d02CenteredGaussianFinitePair (T t : ℝ) (σ : SecondMomentShifts) (X : ℝ) : ℂ :=
  Complex.exp ((σ 0+σ 1)/2) *
    (d02ActualGaussianFinitePair t (rawSecondMomentShifts T σ) X +
      secondDualPower t (rawSecondMomentShifts T σ) *
        d02ActualGaussianFinitePair t
          (d02DualSecondMomentShifts (rawSecondMomentShifts T σ)) X)

theorem d02DualSecondMomentShifts_raw_commute (T : ℝ) (σ : SecondMomentShifts) :
    d02DualSecondMomentShifts (rawSecondMomentShifts T σ) =
      rawSecondMomentShifts T (d02DualSecondMomentShifts σ) := by
  funext j
  fin_cases j <;> simp [d02DualSecondMomentShifts,rawSecondMomentShifts,neg_div]

theorem d02CenteredGaussianPair_truncation_arbitrary_power {R ε δ B : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) (hδ : 0<δ) (hB : 0≤B) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ t∈Icc T (2*T),
      ∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
        ‖d02CenteredGaussianPair T t σ-
          d02CenteredGaussianFinitePair T t σ (T^(1+δ))‖≤C*T^(-B) := by
  obtain ⟨K,hK,hpair⟩ := d02ActualGaussianPair_truncation_arbitrary_power
    (R := R) hε hε1 hδ hB
  have hbox : 0≤secondDualBoxConstant R := by unfold secondDualBoxConstant; positivity
  refine ⟨Real.exp R*(K+secondDualBoxConstant R*K),by positivity,?_⟩
  filter_upwards [hpair,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (1:ℝ))] with T hp hT hL
  intro t ht σ hσ
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hτ : t/T∈Icc (1:ℝ) 2 :=
    ⟨(le_div_iff₀ hTp).mpr (by simpa using ht.1),(div_le_iff₀ hTp).mpr ht.2⟩
  have hpower : ‖secondDualPower t (rawSecondMomentShifts T σ)‖≤secondDualBoxConstant R := by
    have h := secondDualPower_normalized_box_norm_le hTp hR hL hτ σ hσ
    have htd : T*(t/T)=t := by field_simp [hTp.ne']
    rw [htd] at h
    exact h
  have hduals := hp t ht (d02DualSecondMomentShifts σ) (d02DualSecondMomentShifts_norm_le hσ)
  rw [←d02DualSecondMomentShifts_raw_commute] at hduals
  have hdirect := hp t ht σ hσ
  change ‖d02ActualGaussianPair t (rawSecondMomentShifts T σ)-
    d02ActualGaussianFinitePair t (rawSecondMomentShifts T σ) (T^(1+δ))‖≤K*T^(-B) at hdirect
  change ‖d02ActualGaussianPair t (d02DualSecondMomentShifts (rawSecondMomentShifts T σ))-
    d02ActualGaussianFinitePair t (d02DualSecondMomentShifts (rawSecondMomentShifts T σ))
      (T^(1+δ))‖≤K*T^(-B) at hduals
  have he : d02CenteredGaussianPair T t σ-d02CenteredGaussianFinitePair T t σ (T^(1+δ)) =
      Complex.exp ((σ 0+σ 1)/2)*
        ((d02ActualGaussianPair t (rawSecondMomentShifts T σ)-
          d02ActualGaussianFinitePair t (rawSecondMomentShifts T σ) (T^(1+δ)))+
          secondDualPower t (rawSecondMomentShifts T σ)*
            (d02ActualGaussianPair t (d02DualSecondMomentShifts (rawSecondMomentShifts T σ))-
              d02ActualGaussianFinitePair t (d02DualSecondMomentShifts (rawSecondMomentShifts T σ))
                (T^(1+δ)))) := by
    unfold d02CenteredGaussianPair d02CenteredGaussianFinitePair
    ring
  rw [he,norm_mul]
  calc
    _ ≤ Real.exp R*(K*T^(-B)+secondDualBoxConstant R*(K*T^(-B))) := by
      apply mul_le_mul (d02ZetaCentering_norm_le σ hσ) _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hdirect (by
        rw [norm_mul]
        exact mul_le_mul hpower hduals (norm_nonneg _) hbox))
    _ = _ := by ring

end
end Sechstmoment

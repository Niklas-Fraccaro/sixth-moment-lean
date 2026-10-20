import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import SixthMoment.Numerator.Polar.RemainderDecay
import SixthMoment.Numerator.U.Replacement.VStar.DiagonalExtraction
import SixthMoment.Numerator.U.ZeroModes.Transforms.DiagonalLeftTail
import SixthMoment.Numerator.U.ZeroModes.Transforms.DiagonalSixPhaseBound

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03PositiveInteger_invSqrt_sum_le (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,(n:ℝ)^(-(1/2:ℝ)))≤2*(N:ℝ)^(1/2:ℝ) := by
  have he : (∑ i∈Finset.range N,((i+1:ℕ):ℝ)^(-(1/2:ℝ)))=
      ∑ n∈Finset.Icc 1 N,(n:ℝ)^(-(1/2:ℝ)) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]
  have hanti : AntitoneOn (fun x : ℝ => x^(-(1/2:ℝ))) (Ioc 0 (0+(N:ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num)
  have hi : IntegrableOn (fun x : ℝ => x^(-(1/2:ℝ))) (Icc 0 (0+(N:ℝ))) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hs := hanti.sum_le_integral_of_integrableOn hi
  simp only [zero_add] at hs
  rw [he,integral_rpow (Or.inl (by norm_num))] at hs
  norm_num at hs
  exact hs.trans_eq (by ring)

theorem a03DyadicPhase_integrable {T : ℝ} (hT : 0<T) (Φ : ℝ→ℝ)
    (hΦ : SmoothDyadicWeight Φ) (ρ : ℂ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^ρ) := by
  have hK : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  have hScaled : HasCompactSupport (fun t : ℝ => (Φ (t/T):ℂ)) := by
    have hs := hK.comp_smul (inv_ne_zero hT.ne')
    have hs' : HasCompactSupport (fun t : ℝ => Φ (t/T)) := by
      convert hs using 1
      funext t
      simp only [smul_eq_mul,div_eq_mul_inv]
      congr 1
      ring
    exact hs'.comp_left (show Complex.ofReal 0=0 from rfl)
  have hc : Continuous (fun t : ℝ =>
      (Φ (t/T):ℂ)*(((max t T)/(2*Real.pi):ℝ):ℂ)^ρ) := by
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (by fun_prop))
    · apply Continuous.cpow (by fun_prop) continuous_const
      intro t
      exact Complex.ofReal_mem_slitPlane.mpr (div_pos (hT.trans_le (le_max_right _ _)) (by positivity))
  have he : (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^ρ)=
      (fun t : ℝ => (Φ (t/T):ℂ)*(((max t T)/(2*Real.pi):ℝ):ℂ)^ρ) := by
    funext t
    by_cases ht : Φ (t/T)=0
    · simp [ht]
    · have hh := (hΦ.2 (subset_tsupport Φ ht)).1
      have hlow : T≤t := by simpa only [one_mul] using (le_div_iff₀ hT).mp hh
      rw [max_eq_left hlow]
      push_cast
      rfl
  rw [he]
  exact hc.integrable_of_hasCompactSupport (hScaled.mul_right)

def a03DiagonalArithmeticIndexedMainTerm (j : Fin 6) (T a b : ℝ) (α : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ :=
  ∑ m∈Finset.Icc 1 ⌊T^a⌋₊,∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
    (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
      ∫ t : ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α j)*
        a03DiagonalNativeArithmetic (bblrSixShifts α j) m n

theorem a03Diagonal_dyadic_pair_uniform_log_tail {κ : ℝ} (hκ : 0<κ)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) → ∀ j : Fin 6,
      ∀ E : ℝ,0≤E →
      (∀ t∈Icc T (2*T),‖(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)‖≤E) →
      ∀ m n : ℕ,m≠0 → n≠0 →
      ‖(∫ t : ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) j) m n t)-
        (∫ t : ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          a03DiagonalNativeArithmetic (bblrSixShifts (rawMomentShifts T σ) j) m n)‖≤
      C*E*(Real.log T)^48*T^(3/4:ℝ)*((m*n:ℕ):ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨B,hB,hbound⟩ := a03Diagonal_native_uniform_log_tail hκ
  have hK : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  have hI : Integrable Φ := hΦ.1.continuous.integrable_of_hasCompactSupport hK
  let J : ℝ := ∫ x : ℝ,‖Φ x‖
  have hJ : 0≤J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨B*J,mul_nonneg hB hJ,?_⟩
  intro T hT hL σ hgap hα j E hE hphase m n hm hn
  have hTp : 0<T := zero_lt_one.trans hT
  have hsmall : ∀ i : Fin 4,-1/2<(bblrSixShifts (rawMomentShifts T σ) j i).re := by
    intro i
    have hh := (Complex.abs_re_le_norm _).trans (bblrSixShifts_norm_le _ hα j i)
    linarith [(abs_le.mp hh).1]
  rw [←integral_sub
    (actualDyadicDiagonal_integrable hTp _ _ (polarPoleKiller_BBLREntireWeight T σ _) hsmall Φ hΦ _ m n)
    ((a03DyadicPhase_integrable hTp Φ hΦ _).mul_const _)]
  let Q : ℝ := B*E*(Real.log T)^48*T^(-(1/4:ℝ))*((m*n:ℕ):ℝ)^(-(1/2:ℝ))
  have hN := norm_integral_le_of_norm_le (f:=fun t : ℝ =>
      (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
        bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) j) m n t-
      (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
        a03DiagonalNativeArithmetic (bblrSixShifts (rawMomentShifts T σ) j) m n)
    ((hI.norm.comp_div hTp.ne').const_mul Q)
    (ae_of_all _ (fun t : ℝ => by
      by_cases ht : Φ (t/T)=0
      · simp [ht,Q]
      · have hh := hΦ.2 (subset_tsupport Φ ht)
        have hlow : T≤t := by simpa only [one_mul] using (le_div_iff₀ hTp).mp hh.1
        have hupp : t≤2*T := (div_le_iff₀ hTp).mp hh.2
        have htpos := hTp.trans_le hlow
        rw [←mul_sub,norm_mul,norm_mul,Complex.norm_real]
        have hp := Real.rpow_le_rpow_of_nonpos hTp hlow (by norm_num : (-(1/4:ℝ))≤0)
        calc
          _≤‖Φ (t/T)‖*E*(B*(Real.log T)^48*t^(-(1/4:ℝ))*((m*n:ℕ):ℝ)^(-(1/2:ℝ))) := by
            gcongr
            · exact hphase t ⟨hlow,hupp⟩
            · exact hbound T hT hL σ hgap hα j m n hm hn t htpos
          _≤Q*‖Φ (t/T)‖ := by
            dsimp [Q]
            calc
              _=(B*E*(Real.log T)^48*((m*n:ℕ):ℝ)^(-(1/2:ℝ))*‖Φ (t/T)‖)*t^(-(1/4:ℝ)) := by
                simp only [Real.norm_eq_abs]
                ring
              _≤(B*E*(Real.log T)^48*((m*n:ℕ):ℝ)^(-(1/2:ℝ))*‖Φ (t/T)‖)*T^(-(1/4:ℝ)) := by gcongr
              _=_ := by simp only [Real.norm_eq_abs]; ring))
  rw [integral_const_mul] at hN
  have hscale := Measure.integral_comp_div (fun x : ℝ => ‖Φ x‖) T
  rw [abs_of_pos hTp,smul_eq_mul] at hscale
  rw [hscale] at hN
  have he : T^(-(1/4:ℝ))*T=T^(3/4:ℝ) := by
    nth_rw 2 [←Real.rpow_one T]
    rw [←Real.rpow_add hTp]
    norm_num
  exact hN.trans_eq (by dsimp only [Q,J]; rw [show
    B*E*(Real.log T)^48*T^(-(1/4:ℝ))*((m*n:ℕ):ℝ)^(-(1/2:ℝ))*(T*(∫x:ℝ,‖Φ x‖))=
    B*(∫x:ℝ,‖Φ x‖)*E*(Real.log T)^48*(T^(-(1/4:ℝ))*T)*((m*n:ℕ):ℝ)^(-(1/2:ℝ)) by ring,he])

theorem a03PositiveInteger_invSqrt_sum_floor_le {T : ℝ} (hT : 0<T) (a : ℝ) :
    (∑ n∈Finset.Icc 1 ⌊T^a⌋₊,(n:ℝ)^(-(1/2:ℝ)))≤2*T^(a/2) := by
  calc
    _≤2*(⌊T^a⌋₊:ℝ)^(1/2:ℝ) := a03PositiveInteger_invSqrt_sum_le _
    _≤2*(T^a)^(1/2:ℝ) := by
      gcongr
      exact Nat.floor_le (Real.rpow_nonneg hT.le _)
    _=_ := by rw [←Real.rpow_mul hT.le]; congr 2; ring

theorem a03DiagonalIndexedMainTerm_uniform_power_bound {R κ a b δ : ℝ}
    (hR : 0≤R) (hκ : 0<κ) (hab : a≤b) (hδ : 0<δ)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts,(∀ i : Fin 4,‖σ i‖≤R) →
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) → ∀ j : Fin 6,
      ‖bblrIndexedMainTerm j T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03DiagonalArithmeticIndexedMainTerm j T a b (rawMomentShifts T σ) f g Φ‖≤
      C*T^(rectangularSecondExponent a b δ) := by
  obtain ⟨F,hF,hfB⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgB⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨B,hB,hpair⟩ := a03Diagonal_dyadic_pair_uniform_log_tail hκ Φ hΦ
  refine ⟨4*F*G*B*Real.exp (8*R),by positivity,?_⟩
  filter_upwards [a03DiagonalSixPhase_uniform_eventually_norm_bound hR,
    rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/64),
    log_pow_48_eventually_le_rpow hδ,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hphase hraw hlog hT hL
  intro σ hσ hgap j
  have hTp : 0<T := zero_lt_one.trans hT
  let Q : ℝ := F*G*B*Real.exp (8*R)*(Real.log T)^48*T^(3/4:ℝ)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hterms : ∀ m∈Finset.Icc 1 ⌊T^a⌋₊,∀ n∈Finset.Icc 1 ⌊T^b⌋₊,
      ‖(f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
        ((∫t:ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) j) m n t)-
        (∫t:ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          a03DiagonalNativeArithmetic (bblrSixShifts (rawMomentShifts T σ) j) m n))‖≤
      Q*(m:ℝ)^(-(1/2:ℝ))*(n:ℝ)^(-(1/2:ℝ)) := by
    intro m hm n hn
    have hm0 : m≠0 := by have hh := (Finset.mem_Icc.mp hm).1; omega
    have hn0 : n≠0 := by have hh := (Finset.mem_Icc.mp hn).1; omega
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]
    calc
      _≤F*G*(B*Real.exp (8*R)*(Real.log T)^48*T^(3/4:ℝ)*((m*n:ℕ):ℝ)^(-(1/2:ℝ))) := by
        gcongr
        · exact hfB _
        · exact hgB _
        · exact hpair T hT hL σ hgap (hraw σ hσ) j _ (Real.exp_pos _).le (hphase σ hσ j) m n hm0 hn0
      _=_ := by
        rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
        dsimp [Q]
        ring
  have hsum : ‖bblrIndexedMainTerm j T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03DiagonalArithmeticIndexedMainTerm j T a b (rawMomentShifts T σ) f g Φ‖≤
      Q*(2*T^(a/2))*(2*T^(b/2)) := by
    unfold bblrIndexedMainTerm a03DiagonalArithmeticIndexedMainTerm
    rw [←Finset.sum_sub_distrib]
    calc
      _≤∑ m∈Finset.Icc 1 ⌊T^a⌋₊,‖(∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
        (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*∫t:ℝ,
          (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) j) m n t)-
        (∑ n∈Finset.Icc 1 ⌊T^b⌋₊,(f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*∫t:ℝ,
          (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) j)*
          a03DiagonalNativeArithmetic (bblrSixShifts (rawMomentShifts T σ) j) m n)‖ := norm_sum_le _ _
      _≤∑ m∈Finset.Icc 1 ⌊T^a⌋₊,∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
        Q*(m:ℝ)^(-(1/2:ℝ))*(n:ℝ)^(-(1/2:ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [←Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [←mul_sub]
        exact hterms m hm n hn
      _=Q*(∑m∈Finset.Icc 1 ⌊T^a⌋₊,(m:ℝ)^(-(1/2:ℝ)))*
        (∑n∈Finset.Icc 1 ⌊T^b⌋₊,(n:ℝ)^(-(1/2:ℝ))) := by
        simp only [←Finset.mul_sum,←Finset.sum_mul]
      _≤_ := by
        gcongr
        · exact a03PositiveInteger_invSqrt_sum_floor_le hTp a
        · exact a03PositiveInteger_invSqrt_sum_floor_le hTp b
  calc
    _≤Q*(2*T^(a/2))*(2*T^(b/2)) := hsum
    _=(4*F*G*B*Real.exp (8*R))*(Real.log T)^48*T^(3/4+a/2+b/2) := by
      dsimp [Q]
      rw [Real.rpow_add hTp,Real.rpow_add hTp]
      ring
    _≤(4*F*G*B*Real.exp (8*R))*T^(δ/2)*T^(3/4+a/2+b/2) := by gcongr
    _≤_ := by
      rw [mul_assoc,←Real.rpow_add hTp]
      gcongr
      · exact hT.le
      · dsimp [rectangularSecondExponent]
        linarith

def a03DiagonalArithmeticSixMainTerms (T a b : ℝ) (α : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∑ j : Fin 6,a03DiagonalArithmeticIndexedMainTerm j T a b α f g Φ

theorem a03DiagonalSixMainTerms_uniform_power_bound {R κ a b δ : ℝ}
    (hR : 0≤R) (hκ : 0<κ) (hab : a≤b) (hδ : 0<δ)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts,(∀ i : Fin 4,‖σ i‖≤R) →
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ‖bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03DiagonalArithmeticSixMainTerms T a b (rawMomentShifts T σ) f g Φ‖≤
      C*T^(rectangularSecondExponent a b δ) := by
  obtain ⟨C,hC,hbound⟩ := a03DiagonalIndexedMainTerm_uniform_power_bound hR hκ hab hδ f g Φ hf hg hΦ
  refine ⟨6*C,by positivity,?_⟩
  filter_upwards [hbound] with T hbound
  intro σ hσ hgap
  rw [bblrSixMainTerms_eq_indexed]
  unfold a03DiagonalArithmeticSixMainTerms
  rw [←Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hbound σ hσ hgap j)).trans_eq (by simp; ring))

theorem a03DiagonalSixMainTerms_uniform_oT {R κ a b : ℝ}
    (hR : 0≤R) (hκ : 0<κ) (hab : a≤b) (hrect : 3*a+5*b<2)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f)
    (hg : SmoothInteriorProfile b g) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ,0<ε → ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts,(∀ i : Fin 4,‖σ i‖≤R) →
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ‖bblrSixMainTerms T a b (rawMomentShifts T σ) (polarPoleKiller T σ) f g Φ-
        a03DiagonalArithmeticSixMainTerms T a b (rawMomentShifts T σ) f g Φ‖≤ε*T := by
  have hs := rectangular_slack_bounds hab hrect
  obtain ⟨C,hC,hbound⟩ := a03DiagonalSixMainTerms_uniform_power_bound hR hκ hab hs.1 f g Φ hf hg hΦ
  have hq : rectangularSecondExponent a b (rectangularSlack a b)<1 := by linarith [hs.2.2]
  have ho := (rpow_isLittleO_id_of_lt_one hq).const_mul_left C
  intro ε hε
  filter_upwards [hbound,ho.bound hε,eventually_gt_atTop (0:ℝ)] with T hbound ho hT
  intro σ hσ hgap
  apply (hbound σ hσ hgap).trans
  have hn : 0≤C*T^(rectangularSecondExponent a b (rectangularSlack a b)) := by positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos hT] using ho

end
end SixthMoment

import SixthMoment.Numerator.U.Diagonal.ActualSixPowers
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.PairShiftedBFactors


namespace SixthMoment
open ArithmeticFunction Nat Complex Source
open scoped BigOperators
open Classical

set_option maxHeartbeats 0
noncomputable section

abbrev FixedPairFibres (a b : ℕ) :=
  (n : ℕ) × (↥(b*n).divisorsAntidiagonal × ↥(a*n).divisorsAntidiagonal)

def fixedPairQuad {a b : ℕ} (x : FixedPairFibres a b) : Fin 4 → ℕ :=
  ![x.2.1.val.1-1,x.2.1.val.2-1,x.2.2.val.1-1,x.2.2.val.2-1]

theorem fixedPairQuad_values {a b : ℕ} (x : FixedPairFibres a b) :
    fixedPairQuad x 0+1=x.2.1.val.1 ∧ fixedPairQuad x 1+1=x.2.1.val.2 ∧
    fixedPairQuad x 2+1=x.2.2.val.1 ∧ fixedPairQuad x 3+1=x.2.2.val.2 := by
  have h₁ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.2.1.property
  have h₂ := Nat.right_ne_zero_of_mem_divisorsAntidiagonal x.2.1.property
  have h₃ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.2.2.property
  have h₄ := Nat.right_ne_zero_of_mem_divisorsAntidiagonal x.2.2.property
  simp only [fixedPairQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  exact ⟨Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h₁),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h₂),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h₃),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h₄)⟩

theorem fixedPairQuad_relation {a b : ℕ} (x : FixedPairFibres a b) :
    diagonalQuadRelation a b (fixedPairQuad x) := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := fixedPairQuad_values x
  have hd := (Nat.mem_divisorsAntidiagonal.mp x.2.1.property).1
  have he := (Nat.mem_divisorsAntidiagonal.mp x.2.2.property).1
  unfold diagonalQuadRelation
  rw [h₀,h₁,h₂,h₃]
  calc
    a*x.2.1.val.1*x.2.1.val.2=a*(b*x.1) := by rw [mul_assoc,hd]
    _ = b*(a*x.1) := by ring
    _ = b*x.2.2.val.1*x.2.2.val.2 := by
      calc
        _ = b*(x.2.2.val.1*x.2.2.val.2) := congrArg (fun t => b*t) he.symm
        _ = _ := by ring

theorem fixedDiagonal_common_product {a b : ℕ} (_ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) (q : {q : Fin 4 → ℕ // diagonalQuadRelation a b q}) :
    let m := (q.val 0+1)*(q.val 1+1)
    let n := (q.val 2+1)*(q.val 3+1)
    m=b*(m/b) ∧ n=a*(m/b) := by
  dsimp only
  let m := (q.val 0+1)*(q.val 1+1)
  let n := (q.val 2+1)*(q.val 3+1)
  have h : a*m=b*n := by simpa only [m,n,mul_assoc,diagonalQuadRelation] using q.property
  have hbm : b ∣ m := hab.symm.dvd_of_dvd_mul_left (by rw [h]; exact Nat.dvd_mul_right _ _)
  have hm : m=b*(m/b) := (Nat.mul_div_cancel' hbm).symm
  refine ⟨hm,?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb)
  change b*n=b*(a*(m/b))
  calc
    _ = a*m := h.symm
    _ = _ := by nth_rw 1 [hm]; ring

def fixedDiagonalPairFibresEquiv {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) : FixedPairFibres a b ≃
      {q : Fin 4 → ℕ // diagonalQuadRelation a b q} :=
  Equiv.ofBijective (fun x => ⟨fixedPairQuad x, fixedPairQuad_relation x⟩) ⟨by
    intro x y hxy
    have hq : fixedPairQuad x=fixedPairQuad y := congrArg Subtype.val hxy
    obtain ⟨hx₀,hx₁,hx₂,hx₃⟩ := fixedPairQuad_values x
    obtain ⟨hy₀,hy₁,hy₂,hy₃⟩ := fixedPairQuad_values y
    have h₀ := congrArg (fun q : Fin 4 → ℕ => q 0+1) hq
    have h₁ := congrArg (fun q : Fin 4 → ℕ => q 1+1) hq
    have h₂ := congrArg (fun q : Fin 4 → ℕ => q 2+1) hq
    have h₃ := congrArg (fun q : Fin 4 → ℕ => q 3+1) hq
    rw [hx₀,hy₀] at h₀
    rw [hx₁,hy₁] at h₁
    rw [hx₂,hy₂] at h₂
    rw [hx₃,hy₃] at h₃
    rcases x with ⟨n,⟨⟨⟨u,v⟩,hd⟩,⟨⟨r,t⟩,he⟩⟩⟩
    rcases y with ⟨m,⟨⟨⟨u',v'⟩,hd'⟩,⟨⟨r',t'⟩,he'⟩⟩⟩
    change u=u' at h₀
    change v=v' at h₁
    change r=r' at h₂
    change t=t' at h₃
    subst u'
    subst v'
    subst r'
    subst t'
    have hnm : n=m := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb)
      ((Nat.mem_divisorsAntidiagonal.mp hd).1.symm.trans
        (Nat.mem_divisorsAntidiagonal.mp hd').1)
    subst m
    rfl,
  by
    intro q
    let x : FixedPairFibres a b :=
      ⟨(q.val 0+1)*(q.val 1+1)/b,
        ⟨⟨(q.val 0+1,q.val 1+1), Nat.mem_divisorsAntidiagonal.mpr
          ⟨(fixedDiagonal_common_product ha hb hab q).1, by
            rw [← (fixedDiagonal_common_product ha hb hab q).1]; positivity⟩⟩,
         ⟨(q.val 2+1,q.val 3+1), Nat.mem_divisorsAntidiagonal.mpr
          ⟨(fixedDiagonal_common_product ha hb hab q).2, by
            rw [← (fixedDiagonal_common_product ha hb hab q).2]; positivity⟩⟩⟩⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [fixedPairQuad,x]⟩

theorem shiftedPairArithmetic_eq_divisorSum (a b : ℂ) (n : ℕ) :
    shiftedPairArithmetic a b n = ∑ d : ↥n.divisorsAntidiagonal,
      shiftedPowerArithmetic a d.val.1*shiftedPowerArithmetic b d.val.2 := by
  rw [shiftedPairArithmetic, ArithmeticFunction.mul_apply]
  exact (Finset.sum_coe_sort _ _).symm

theorem actualDiagonalQuadDirichletTerm_fixedPair {a b : ℕ} (α : MomentShifts)
    (z : ℂ) (x : FixedPairFibres a b) :
    actualDiagonalQuadDirichletTerm α (fixedPairQuad x) z =
      (shiftedPowerArithmetic (1/2+α 0+z) x.2.1.val.1*
        shiftedPowerArithmetic (1/2+α 1+z) x.2.1.val.2)*
      (shiftedPowerArithmetic (1/2+α 2+z) x.2.2.val.1*
        shiftedPowerArithmetic (1/2+α 3+z) x.2.2.val.2) := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := fixedPairQuad_values x
  have hn₀ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.2.1.property
  have hn₁ := Nat.right_ne_zero_of_mem_divisorsAntidiagonal x.2.1.property
  have hn₂ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal x.2.2.property
  have hn₃ := Nat.right_ne_zero_of_mem_divisorsAntidiagonal x.2.2.property
  unfold actualDiagonalQuadDirichletTerm
  rw [Fin.prod_univ_four]
  have he (n m : ℕ) (h : n+1=m) : (n+1:ℂ)=(m:ℂ) := by exact_mod_cast h
  rw [he _ _ h₀,he _ _ h₁,he _ _ h₂,he _ _ h₃]
  simp only [shiftedPowerArithmetic_apply _ hn₀, shiftedPowerArithmetic_apply _ hn₁,
    shiftedPowerArithmetic_apply _ hn₂, shiftedPowerArithmetic_apply _ hn₃,
    Complex.cpow_neg, one_div, mul_inv_rev]
  ring

theorem actualDiagonalQuadDirichletTerm_fixedPair_fibre_sum (α : MomentShifts)
    (z : ℂ) (a b n : ℕ) :
    (∑ x : ↥(b*n).divisorsAntidiagonal × ↥(a*n).divisorsAntidiagonal,
      actualDiagonalQuadDirichletTerm α (fixedPairQuad ⟨n,x⟩) z) =
    shiftedPairArithmetic (1/2+α 0+z) (1/2+α 1+z) (b*n)*
      shiftedPairArithmetic (1/2+α 2+z) (1/2+α 3+z) (a*n) := by
  simp_rw [actualDiagonalQuadDirichletTerm_fixedPair]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← shiftedPairArithmetic_eq_divisorSum,
    ← shiftedPairArithmetic_eq_divisorSum]

theorem actualDiagonalQuadDirichletTerm_tsum_eq_pairDiagonal {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (v : ℝ) :
    (∑' q : Fin 4 → ℕ, if diagonalQuadRelation a b q then
      actualDiagonalQuadDirichletTerm α q (1+(v:ℂ)*I) else 0) =
    ∑' n : ℕ, shiftedPairArithmetic (1/2+α 0+(1+(v:ℂ)*I))
      (1/2+α 1+(1+(v:ℂ)*I)) (b*n)*
      shiftedPairArithmetic (1/2+α 2+(1+(v:ℂ)*I)) (1/2+α 3+(1+(v:ℂ)*I)) (a*n) := by
  have hn : Summable (fun q : Fin 4 → ℕ =>
      ‖actualDiagonalQuadDirichletTerm α q (1+(v:ℂ)*I)‖) := by
    apply (rectangular_AFE_index_majorant_summable α hα).congr
    intro q
    exact (actualDiagonalQuadDirichletTerm_line_norm α q v).symm
  have hs := (hn.subtype (fun q => diagonalQuadRelation a b q)).of_norm
  have hsig := (fixedDiagonalPairFibresEquiv ha hb hab).summable_iff.mpr hs
  change Summable (fun x : FixedPairFibres a b =>
    actualDiagonalQuadDirichletTerm α (fixedPairQuad x) (1+(v:ℂ)*I)) at hsig
  have hselect : (∑' q : Fin 4 → ℕ, if diagonalQuadRelation a b q then
      actualDiagonalQuadDirichletTerm α q (1+(v:ℂ)*I) else 0) =
      ∑' q : {q : Fin 4 → ℕ // diagonalQuadRelation a b q},
        actualDiagonalQuadDirichletTerm α q.val (1+(v:ℂ)*I) := by
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Set.coe_ofPred] using
      (tsum_subtype {q : Fin 4 → ℕ | diagonalQuadRelation a b q}
        (fun q => actualDiagonalQuadDirichletTerm α q (1+(v:ℂ)*I))).symm
  rw [hselect, ← (fixedDiagonalPairFibresEquiv ha hb hab).tsum_eq]
  change (∑' x : FixedPairFibres a b,
    actualDiagonalQuadDirichletTerm α (fixedPairQuad x) (1+(v:ℂ)*I)) = _
  rw [hsig.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  exact actualDiagonalQuadDirichletTerm_fixedPair_fibre_sum α _ a b n

theorem fixedPairHalfShift_product (α : MomentShifts) (z : ℂ) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    shiftedPairArithmetic (1/2+α 0+z) (1/2+α 1+z) (b*n)*
      shiftedPairArithmetic (1/2+α 2+z) (1/2+α 3+z) (a*n) =
    ((a*b:ℕ):ℂ)^(-(1/2+z))*(shiftedPairArithmetic (α 0) (α 1) (b*n)*
      shiftedPairArithmetic (α 2) (α 3) (a*n)*shiftedPowerArithmetic (1+2*z) n) := by
  have he (j : Fin 4) : 1/2+α j+z=α j+(1/2+z) := by ring
  simp_rw [he]
  rw [shiftedPairArithmetic_add_shifts, shiftedPairArithmetic_add_shifts,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
    actualShiftedPower_mul, actualShiftedPower_mul]
  have hconstant : shiftedPowerArithmetic (1/2+z) b*shiftedPowerArithmetic (1/2+z) a =
      ((a*b:ℕ):ℂ)^(-(1/2+z)) := by
    rw [← actualShiftedPower_mul, Nat.mul_comm b a,
      shiftedPowerArithmetic_apply _ (mul_ne_zero ha hb)]
  have hn : shiftedPowerArithmetic (1/2+z) n*shiftedPowerArithmetic (1/2+z) n =
      shiftedPowerArithmetic (1+2*z) n := by
    rw [← actualShiftedPower_add]
    congr 1
    ring
  calc
    _ = (shiftedPowerArithmetic (1/2+z) b*shiftedPowerArithmetic (1/2+z) a)*
      (shiftedPairArithmetic (α 0) (α 1) (b*n)*shiftedPairArithmetic (α 2) (α 3) (a*n)*
        (shiftedPowerArithmetic (1/2+z) n*shiftedPowerArithmetic (1/2+z) n)) := by ring
    _ = _ := by rw [hconstant,hn]

theorem actualDiagonalQuadDirichletTerm_tsum_eq_correlation {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) (α : MomentShifts)
    (hα : ∀ j, -1/2 < (α j).re) (v : ℝ) :
    (∑' q : Fin 4 → ℕ, if diagonalQuadRelation a b q then
      actualDiagonalQuadDirichletTerm α q (1+(v:ℂ)*I) else 0) =
    ((a*b:ℕ):ℂ)^(-(1/2+(1+(v:ℂ)*I)))*
      ∑' n : ℕ, shiftedPairArithmetic (α 0) (α 1) (b*n)*
        shiftedPairArithmetic (α 2) (α 3) (a*n)*shiftedPowerArithmetic (1+2*(1+(v:ℂ)*I)) n := by
  rw [actualDiagonalQuadDirichletTerm_tsum_eq_pairDiagonal ha hb hab α hα v]
  simp_rw [fixedPairHalfShift_product α _ ha hb]
  rw [tsum_mul_left]

theorem bblrDiagonalTerm_eq_fixedCorrelationMellin {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) {t : ℝ} (ht : t ≠ 0)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) :
    bblrDiagonalTerm G α a b t = verticalIntegral 1 (fun z =>
      actualDiagonalMellinFactor G a b t z*((a*b:ℕ):ℂ)^(-(1/2+z))*
        ∑' n : ℕ, shiftedPairArithmetic (α 0) (α 1) (b*n)*
          shiftedPairArithmetic (α 2) (α 3) (a*n)*shiftedPowerArithmetic (1+2*z) n) := by
  rw [bblrDiagonalTerm_eq_actualMellin ht G α hG hα a b]
  unfold verticalIntegral
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  simp only [Complex.ofReal_one]
  rw [actualDiagonalQuadDirichletTerm_tsum_eq_correlation ha hb hab α hα v]
  ring

theorem actualDiagonalMellinFactor_fixedNormalization {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) {t : ℝ} (ht : 0 < t) (G : ℂ → ℂ) (z : ℂ) :
    actualDiagonalMellinFactor G a b t z*((a*b:ℕ):ℂ)^(-(1/2+z)) =
      G z/z*(t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z)) := by
  have hab0 : ((a*b:ℕ):ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero ha hb)
  have hbase : ((a*b:ℕ):ℂ)^(-(1/2:ℂ))*((a*b:ℕ):ℂ)^(-(1/2+z)) =
      ((a*b:ℕ):ℂ)^(-(1+z)) := by
    rw [← Complex.cpow_add _ _ hab0]
    congr 1
    ring
  have ht2 : ((t^2:ℝ):ℂ)^z=(t:ℂ)^(2*z) := by
    simpa only [Real.rpow_two, Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg ht.le (2:ℝ) z).symm
  have htpi : (2*Real.pi:ℂ)^(-2*z)*((t^2:ℝ):ℂ)^z=(t/(2*Real.pi):ℂ)^(2*z) := by
    rw [ht2]
    have hdiv := Complex.div_cpow_ofReal_nonneg ht.le
      (show 0≤2*Real.pi by positivity) (2*z)
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hdiv
    have hneg : (-2:ℂ)*z=-(2*z) := by ring
    rw [hneg, hdiv, Complex.cpow_neg, div_eq_mul_inv]
    ring
  unfold actualDiagonalMellinFactor
  rw [div_eq_mul_inv, ← Complex.cpow_neg ((a*b:ℕ):ℂ) (1/2:ℂ)]
  calc
    _ = G z/z*((2*Real.pi:ℂ)^(-2*z)*((t^2:ℝ):ℂ)^z)*
      (((a*b:ℕ):ℂ)^(-(1/2:ℂ))*((a*b:ℕ):ℂ)^(-(1/2+z))) := by ring
    _ = _ := by rw [hbase,htpi]

theorem bblrDiagonalTerm_eq_fixedCorrelationMellin_normalized {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) {t : ℝ} (ht : 0 < t)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) :
    bblrDiagonalTerm G α a b t = verticalIntegral 1 (fun z =>
      G z/z*(t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z))*
        ∑' n : ℕ, shiftedPairArithmetic (α 0) (α 1) (b*n)*
          shiftedPairArithmetic (α 2) (α 3) (a*n)*shiftedPowerArithmetic (1+2*z) n) := by
  rw [bblrDiagonalTerm_eq_fixedCorrelationMellin ha hb hab ht.ne' G α hG hα]
  congr 1
  funext z
  rw [actualDiagonalMellinFactor_fixedNormalization ha hb ht G z]

end
end SixthMoment

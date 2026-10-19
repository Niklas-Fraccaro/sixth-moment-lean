import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.TripleAbsoluteMass
import Sechstmoment.Numerator.U.ZeroModes.RatioWeightedPolynomialTail

/-! The true countable native gcd mass on a polynomial ratio tail has an
arbitrary power saving. One inverse-ratio factor is retained in each
Dirichlet variable, so both infinite arithmetic sums remain convergent. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 3000000

def a03NativeGCDRatioTailMassTerm (c δ T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (X : ℝ) (p : (ℕ×ℕ)×ℕ) : ℝ :=
  if c*T^δ≤(a:ℝ)*((p.1.1:ℝ)+1)^2/X ∨ c*T^δ≤(b:ℝ)*((p.1.2:ℝ)+1)^2/X then
    a03NativeGCDTripleAbsoluteMassTerm T σ a b X ((p.1.1+1,p.1.2+1),p.2)
  else 0

theorem a03NativeGCDRatioTailMassTerm_nonneg (c δ T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (X : ℝ) (p : (ℕ×ℕ)×ℕ) :
    0≤a03NativeGCDRatioTailMassTerm c δ T σ a b X p := by
  unfold a03NativeGCDRatioTailMassTerm
  split_ifs
  · exact a03NativeGCDTripleAbsoluteMassTerm_nonneg _ _ _ _ _ _
  · exact le_rfl

theorem a03RatioBroadDirichletTerm_succ_bound {T A X K : ℝ} {σ : MomentShifts}
    (hA : 0<A) (hX : 0<X) (m : ℕ)
    (hpart : ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ))
      (A*((m:ℝ)+1)^2/X)‖≤K*(A*((m:ℝ)+1)^2/X)^(-1:ℝ)) :
    a03RatioBroadDirichletTerm T σ A X (m+1)≤K*(X/A)*((m:ℝ)+1)^(-(5/2:ℝ)) := by
  have hm : (0:ℝ)<(m:ℝ)+1 := by positivity
  have hpow : ((m:ℝ)+1)^2*((m:ℝ)+1)^(-(5/2:ℝ))=((m:ℝ)+1)^(-(1/2:ℝ)) := by
    rw [←Real.rpow_two,←Real.rpow_add hm]
    norm_num
  have he : ((m:ℝ)+1)^(-(1/2:ℝ))*(A*((m:ℝ)+1)^2/X)^(-1:ℝ)=
      (X/A)*((m:ℝ)+1)^(-(5/2:ℝ)) := by
    rw [←hpow,Real.rpow_neg_one]
    field_simp
  simp only [a03RatioBroadDirichletTerm,Nat.add_one_ne_zero,ite_false,Nat.cast_add,Nat.cast_one]
  calc
    _≤((m:ℝ)+1)^(-(1/2:ℝ))*(K*(A*((m:ℝ)+1)^2/X)^(-1:ℝ)) :=
      mul_le_mul_of_nonneg_left hpart (Real.rpow_nonneg hm.le _)
    _=K*(((m:ℝ)+1)^(-(1/2:ℝ))*(A*((m:ℝ)+1)^2/X)^(-1:ℝ)) := by ring
    _=_ := by rw [he]; ring

theorem a03NativeGCDRatioTailMass_uniform_rapid {κ δ c : ℝ}
    (hκ : 0<κ) (hδ : 0<δ) (hc : 0<c) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ a b : ℕ,0<a → 0<b → ∀ X : ℝ,0<X →
      Summable (a03NativeGCDRatioTailMassTerm c δ T σ a b X) ∧
      (∑'p : (ℕ×ℕ)×ℕ,a03NativeGCDRatioTailMassTerm c δ T σ a b X p)≤
        C*T^(-(M:ℝ))*(Real.log T)^4*(X^2/((a:ℝ)*(b:ℝ)))*(X/T)^2 := by
  obtain ⟨Ct,hCt,htail⟩ := a03ActualRatioPartition_uniform_weighted_polynomial_tail hκ hδ hc M
  obtain ⟨Cu,hCu,hunit⟩ := a03RatioBroadPartition_unit_power_bound hκ
  let P : ℕ→ℝ := fun m => ((m:ℝ)+1)^(-(5/2:ℝ))
  let H : ℕ→ℝ := fun h => ((h:ℝ)+1)^(-(2:ℝ))
  let Z : ℝ := ∑'m : ℕ,P m
  let W : ℝ := ∑'h : ℕ,H h
  have hP : Summable P := a03GapPower_summable (by norm_num : (1:ℝ)<5/2)
  have hH : Summable H := a03GapPower_summable (by norm_num : (1:ℝ)<2)
  have hnP (m : ℕ) : 0≤P m := by dsimp [P]; positivity
  have hnH (h : ℕ) : 0≤H h := by dsimp [H]; positivity
  have hZ : 0≤Z := tsum_nonneg hnP
  have hW : 0≤W := tsum_nonneg hnH
  have hPP := @Summable.mul_of_nonneg ℕ ℕ P P hP hP hnP hnP
  have hPPH := @Summable.mul_of_nonneg (ℕ×ℕ) ℕ
    (fun p => P p.1*P p.2) H hPP hH (fun p => mul_nonneg (hnP _) (hnP _)) hnH
  refine ⟨Ct*Cu*Z^2*W,by positivity,?_⟩
  filter_upwards [htail,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T htail hT hlog
  intro σ hroot a b ha hb X hX
  have ht : 0<T := zero_lt_one.trans hT
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  let Q : ℝ := Ct*Cu*T^(-(M:ℝ))*(Real.log T)^4*(X/a)*(X/b)*(X/T)^2
  have hQ : 0≤Q := by dsimp [Q]; positivity
  let major : ((ℕ×ℕ)×ℕ)→ℝ := fun p => Q*(P p.1.1*P p.1.2)*H p.2
  have hsmajor : Summable major := by
    simpa only [major,mul_assoc] using hPPH.mul_left Q
  have hunitA (m : ℕ) : a03RatioBroadDirichletTerm T σ a X (m+1)≤Cu*(Real.log T)^4*(X/a)*P m :=
    a03RatioBroadDirichletTerm_succ_bound haR hX m
      (hunit T hT hlog σ hroot _ (by positivity))
  have hunitB (n : ℕ) : a03RatioBroadDirichletTerm T σ b X (n+1)≤Cu*(Real.log T)^4*(X/b)*P n :=
    a03RatioBroadDirichletTerm_succ_bound hbR hX n
      (hunit T hT hlog σ hroot _ (by positivity))
  have hsmallA (m : ℕ) (hlarge : c*T^δ≤(a:ℝ)*((m:ℝ)+1)^2/X) :
      a03RatioBroadDirichletTerm T σ a X (m+1)≤Ct*T^(-(M:ℝ))*(X/a)*P m :=
    a03RatioBroadDirichletTerm_succ_bound haR hX m (htail σ hroot _ hlarge)
  have hsmallB (n : ℕ) (hlarge : c*T^δ≤(b:ℝ)*((n:ℝ)+1)^2/X) :
      a03RatioBroadDirichletTerm T σ b X (n+1)≤Ct*T^(-(M:ℝ))*(X/b)*P n :=
    a03RatioBroadDirichletTerm_succ_bound hbR hX n (htail σ hroot _ hlarge)
  have hp (p : (ℕ×ℕ)×ℕ) : a03NativeGCDRatioTailMassTerm c δ T σ a b X p≤major p := by
    unfold a03NativeGCDRatioTailMassTerm
    split_ifs with hlarge
    · have hd : (1:ℝ)≤Nat.gcd (a*(p.1.1+1)) (b*(p.1.2+1)) := by
        exact_mod_cast Nat.gcd_pos_of_pos_left (b*(p.1.2+1)) (Nat.mul_pos ha (by omega))
      have hfreq := a03NativeGCDFrequencyMassTerm_bound ht hX hd p.2
      have hnF : 0≤a03NativeGCDFrequencyMassTerm T X (Nat.gcd (a*(p.1.1+1)) (b*(p.1.2+1))) p.2 := by
        unfold a03NativeGCDFrequencyMassTerm
        positivity
      unfold a03NativeGCDTripleAbsoluteMassTerm
      rcases hlarge with hlarge|hlarge
      · have hprod := mul_le_mul (hsmallA p.1.1 hlarge) (hunitB p.1.2)
          (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _) (by dsimp [P]; positivity : 0≤Ct*T^(-(M:ℝ))*(X/a)*P p.1.1)
        have hh := mul_le_mul hprod hfreq hnF
          (by dsimp [P]; positivity : 0≤(Ct*T^(-(M:ℝ))*(X/a)*P p.1.1)*(Cu*(Real.log T)^4*(X/b)*P p.1.2))
        exact hh.trans_eq (by dsimp [major,Q,H]; ring)
      · have hprod := mul_le_mul (hunitA p.1.1) (hsmallB p.1.2 hlarge)
          (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _) (by dsimp [P]; positivity : 0≤Cu*(Real.log T)^4*(X/a)*P p.1.1)
        have hh := mul_le_mul hprod hfreq hnF
          (by dsimp [P]; positivity : 0≤(Cu*(Real.log T)^4*(X/a)*P p.1.1)*(Ct*T^(-(M:ℝ))*(X/b)*P p.1.2))
        exact hh.trans_eq (by dsimp [major,Q,H]; ring)
    · dsimp [major,P,H]
      positivity
  have hs := hsmajor.of_nonneg_of_le (a03NativeGCDRatioTailMassTerm_nonneg _ _ _ _ _ _ _) hp
  refine ⟨hs,?_⟩
  calc
    _≤∑'p : (ℕ×ℕ)×ℕ,major p := hs.tsum_le_tsum hp hsmajor
    _=Q*(Z*Z)*W := by
      calc
        _=Q*(∑'p : (ℕ×ℕ)×ℕ,(P p.1.1*P p.1.2)*H p.2) := by
          rw [←tsum_mul_left]
          apply tsum_congr
          intro p
          dsimp [major]
          ring
        _=Q*((Z*Z)*W) := by
          rw [←hPP.tsum_mul_tsum hH hPPH,←hP.tsum_mul_tsum hP hPP]
        _=_ := by ring
    _=_ := by dsimp [Q]; ring

end
end Sechstmoment.Source

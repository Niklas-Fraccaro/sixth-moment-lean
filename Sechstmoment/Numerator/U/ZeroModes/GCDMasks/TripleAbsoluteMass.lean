import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.FrequencyMass
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.SpatialMass
import Sechstmoment.Numerator.U.ZeroModes.RatioBroadDirichletMass

/-! A genuine joint absolute mass for the actual ratio partitions and
all positive native gcd frequencies, before the spatial integration. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDTripleAbsoluteMassTerm (T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (X : ℝ) (p : (ℕ×ℕ)×ℕ) : ℝ :=
  a03RatioBroadDirichletTerm T σ a X p.1.1*
    a03RatioBroadDirichletTerm T σ b X p.1.2*
      a03NativeGCDFrequencyMassTerm T X (Nat.gcd (a*p.1.1) (b*p.1.2)) p.2

theorem a03NativeGCDTripleAbsoluteMassTerm_nonneg (T : ℝ) (σ : MomentShifts)
    (a b : ℕ) (X : ℝ) (p : (ℕ×ℕ)×ℕ) :
    0≤a03NativeGCDTripleAbsoluteMassTerm T σ a b X p := by
  unfold a03NativeGCDTripleAbsoluteMassTerm a03NativeGCDFrequencyMassTerm
  exact mul_nonneg (mul_nonneg (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _)
    (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _))
    (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem a03NativeGCDTripleAbsoluteMass_uniform_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ a b : ℕ,0<a → 0<b → ∀ X : ℝ,0<X →
      Summable (a03NativeGCDTripleAbsoluteMassTerm T σ a b X) ∧
        (∑' p : (ℕ×ℕ)×ℕ,a03NativeGCDTripleAbsoluteMassTerm T σ a b X p)≤
          C*(Real.log T)^8*(X^2/((a:ℝ)*(b:ℝ)))*(X/T)^2 := by
  obtain ⟨C,hC,hbroad⟩ := a03RatioBroadDirichletMass_uniform_bound hκ
  let Z : ℝ := ∑' m : ℕ,(m:ℝ)^(-(5/2:ℝ))
  let H : ℝ := ∑' h : ℕ,((h:ℝ)+1)^(-(2:ℝ))
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have hH : 0≤H := tsum_nonneg (fun _ => by positivity)
  refine ⟨C^2*Z^2*H,by positivity,?_⟩
  intro T hT hlog σ hroot a b ha hb X hX
  have hTp : 0<T := zero_lt_one.trans hT
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  obtain ⟨hA,hAmass⟩ := hbroad T hT hlog σ hroot a X haR hX
  obtain ⟨hB,hBmass⟩ := hbroad T hT hlog σ hroot b X hbR hX
  have hAB := @Summable.mul_of_nonneg ℕ ℕ
    (a03RatioBroadDirichletTerm T σ a X) (a03RatioBroadDirichletTerm T σ b X)
      hA hB (a03RatioBroadDirichletTerm_nonneg _ _ _ _) (a03RatioBroadDirichletTerm_nonneg _ _ _ _)
  let Q : ℕ→ℝ := fun h => (X/T)^2*((h:ℝ)+1)^(-(2:ℝ))
  have hQ : Summable Q := (a03GapPower_summable (by norm_num : (1:ℝ)<2)).mul_left _
  have hnQ (h : ℕ) : 0≤Q h := by dsimp [Q]; positivity
  have hmajor := @Summable.mul_of_nonneg (ℕ×ℕ) ℕ
    (fun p => a03RatioBroadDirichletTerm T σ a X p.1*a03RatioBroadDirichletTerm T σ b X p.2)
      Q hAB hQ (fun p => mul_nonneg (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _)
        (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _)) hnQ
  have hp (p : (ℕ×ℕ)×ℕ) : a03NativeGCDTripleAbsoluteMassTerm T σ a b X p≤
      (a03RatioBroadDirichletTerm T σ a X p.1.1*a03RatioBroadDirichletTerm T σ b X p.1.2)*Q p.2 := by
    by_cases hm : p.1.1=0
    · simp [a03NativeGCDTripleAbsoluteMassTerm,a03RatioBroadDirichletTerm,hm]
    by_cases hn : p.1.2=0
    · simp [a03NativeGCDTripleAbsoluteMassTerm,a03RatioBroadDirichletTerm,hn]
    have hd : (1:ℝ)≤Nat.gcd (a*p.1.1) (b*p.1.2) := by
      exact_mod_cast Nat.gcd_pos_of_pos_left (b*p.1.2) (Nat.mul_pos ha (Nat.pos_of_ne_zero hm))
    exact mul_le_mul_of_nonneg_left (a03NativeGCDFrequencyMassTerm_bound hTp hX hd p.2)
      (mul_nonneg (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _)
        (a03RatioBroadDirichletTerm_nonneg _ _ _ _ _))
  have hs := hmajor.of_nonneg_of_le (a03NativeGCDTripleAbsoluteMassTerm_nonneg _ _ _ _ _) hp
  refine ⟨hs,?_⟩
  calc
    _≤∑' p : (ℕ×ℕ)×ℕ,
        (a03RatioBroadDirichletTerm T σ a X p.1.1*a03RatioBroadDirichletTerm T σ b X p.1.2)*Q p.2 :=
      hs.tsum_le_tsum hp hmajor
    _=(∑' m : ℕ,a03RatioBroadDirichletTerm T σ a X m)*
        (∑' n : ℕ,a03RatioBroadDirichletTerm T σ b X n)*((X/T)^2*H) := by
      rw [←hAB.tsum_mul_tsum hQ hmajor,←hA.tsum_mul_tsum hB hAB]
      dsimp only [Q,H]
      rw [tsum_mul_left]
    _≤(C*(Real.log T)^4*(X/a)*Z)*(C*(Real.log T)^4*(X/b)*Z)*((X/T)^2*H) := by
      gcongr
      exact tsum_nonneg (a03RatioBroadDirichletTerm_nonneg T σ b X)
    _=(C^2*Z^2*H)*(Real.log T)^8*(X^2/((a:ℝ)*(b:ℝ)))*(X/T)^2 := by
      ring

end
end Sechstmoment.Source

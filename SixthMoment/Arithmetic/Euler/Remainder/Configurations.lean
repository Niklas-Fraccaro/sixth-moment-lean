import Mathlib.Data.Nat.Factorization.Basic
import SixthMoment.Arithmetic.Euler.Bivariate.Factorization

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

def leftDegree : Fin 8 → ℕ := ![1, 0, 2, 0, 1, 2, 1, 2]
def rightDegree : Fin 8 → ℕ := ![0, 1, 0, 2, 1, 1, 2, 2]

theorem degrees_nonzero (j : Fin 8) : leftDegree j ≠ 0 ∨ rightDegree j ≠ 0 := by
  fin_cases j <;> simp [leftDegree, rightDegree]

theorem degrees_injective : Function.Injective (fun j : Fin 8 => (leftDegree j, rightDegree j)) := by
  decide

def localCoeff (p : Nat.Primes) (s : Fin 4 → ℂ) (j : Fin 8) : ℂ :=
  residueRest (primeRoot p.val (s 0)) (primeRoot p.val (s 1))
    (primeRoot p.val (s 2)) (primeRoot p.val (s 3)) (primeX p.val)
    (leftDegree j) (rightDegree j)

abbrev Configuration := Σ S : Finset Nat.Primes, S → Fin 8

def configLeft (c : Configuration) : ℕ := ∏ p : c.1, p.val.val ^ leftDegree (c.2 p)
def configRight (c : Configuration) : ℕ := ∏ p : c.1, p.val.val ^ rightDegree (c.2 p)
def configIndex (c : Configuration) : ℕ × ℕ := (configLeft c, configRight c)
def configCoeff (s : Fin 4 → ℂ) (c : Configuration) : ℂ :=
  ∏ p : c.1, localCoeff p.val s (c.2 p)

theorem configLeft_pos (c : Configuration) : 0 < configLeft c := by
  exact Finset.prod_pos (fun p _ => pow_pos p.val.property.pos _)

theorem configRight_pos (c : Configuration) : 0 < configRight c := by
  exact Finset.prod_pos (fun p _ => pow_pos p.val.property.pos _)

theorem config_factorization (S : Finset Nat.Primes) (f : S → ℕ) (p : Nat.Primes) :
    (∏ q : S, q.val.val ^ f q).factorization p.val =
      ∑ q : S, if q.val = p then f q else 0 := by
  rw [Nat.factorization_prod_apply (fun q _ => pow_ne_zero _ q.val.property.ne_zero)]
  apply Finset.sum_congr rfl
  intro q _
  rw [q.val.property.factorization_pow]
  by_cases h : q.val = p
  · subst p
    simp
  · have h' : q.val.val ≠ p.val := fun hqp => h (Subtype.ext hqp)
    simp [h, Finsupp.single_apply, h']

theorem config_factorization_mem (c : Configuration) (p : Nat.Primes) (hp : p ∈ c.1) :
    (configLeft c).factorization p.val = leftDegree (c.2 ⟨p, hp⟩) ∧
    (configRight c).factorization p.val = rightDegree (c.2 ⟨p, hp⟩) := by
  constructor <;> simp only [configLeft, configRight] <;> rw [config_factorization]
  all_goals
    rw [Finset.sum_eq_single ⟨p, hp⟩]
    · simp
    · intro q _ hq
      have H : q.val ≠ p := fun H => hq (Subtype.ext H)
      simp [H]
    · simp

theorem config_factorization_not_mem (c : Configuration) (p : Nat.Primes) (hp : p ∉ c.1) :
    (configLeft c).factorization p.val = 0 ∧ (configRight c).factorization p.val = 0 := by
  constructor <;> simp only [configLeft, configRight] <;> rw [config_factorization]
  all_goals
    apply Finset.sum_eq_zero
    intro q _
    have H : q.val ≠ p := fun H => hp (H ▸ q.property)
    simp [H]

theorem config_support_iff (c : Configuration) (p : Nat.Primes) :
    p ∈ c.1 ↔ (configLeft c).factorization p.val ≠ 0 ∨
      (configRight c).factorization p.val ≠ 0 := by
  by_cases hp : p ∈ c.1
  · rw [config_factorization_mem c p hp |>.1, config_factorization_mem c p hp |>.2]
    exact iff_of_true hp (degrees_nonzero _)
  · simp only [hp, config_factorization_not_mem c p hp |>.1,
      config_factorization_not_mem c p hp |>.2, ne_eq, not_true_eq_false, or_self]

theorem configIndex_injective : Function.Injective configIndex := by
  intro c d h
  have hl : configLeft c = configLeft d := congrArg Prod.fst h
  have hr : configRight c = configRight d := congrArg Prod.snd h
  have hs : c.1 = d.1 := by
    ext p
    rw [config_support_iff c p, config_support_iff d p, hl, hr]
  rcases c with ⟨S, f⟩
  rcases d with ⟨T, g⟩
  dsimp at hs
  subst T
  congr 1
  funext p
  apply degrees_injective
  have hfl := congrArg (fun n => n.factorization p.val.val) hl
  have hfr := congrArg (fun n => n.factorization p.val.val) hr
  rw [(config_factorization_mem ⟨S,f⟩ p.val p.property).1,
    (config_factorization_mem ⟨S,g⟩ p.val p.property).1] at hfl
  rw [(config_factorization_mem ⟨S,f⟩ p.val p.property).2,
    (config_factorization_mem ⟨S,g⟩ p.val p.property).2] at hfr
  exact Prod.ext hfl hfr

def gamma (s : Fin 4 → ℂ) : ℕ × ℕ → ℂ := Function.extend configIndex (configCoeff s) 0

theorem gamma_config (s : Fin 4 → ℂ) (c : Configuration) :
    gamma s (configIndex c) = configCoeff s c :=
  configIndex_injective.extend_apply _ _ _

theorem gamma_outside (s : Fin 4 → ℂ) (n : ℕ × ℕ) (hn : n ∉ Set.range configIndex) :
    gamma s n = 0 := Function.extend_apply' _ _ _ hn

theorem gamma_zero_left (s : Fin 4 → ℂ) (n : ℕ) : gamma s (0,n) = 0 := by
  apply gamma_outside
  rintro ⟨c, hc⟩
  have := configLeft_pos c
  have H := congrArg Prod.fst hc
  change configLeft c = 0 at H
  omega

theorem gamma_zero_right (s : Fin 4 → ℂ) (n : ℕ) : gamma s (n,0) = 0 := by
  apply gamma_outside
  rintro ⟨c, hc⟩
  have := configRight_pos c
  have H := congrArg Prod.snd hc
  change configRight c = 0 at H
  omega

end
end SixthMoment.Source.NoDPGlobalRest

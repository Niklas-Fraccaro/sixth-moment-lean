import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Front

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 500000

def a03ZeroModeGCDInitialBase (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) : ℂ :=
  A a*B b*(a:ℂ)^(-1+α 1-u)*(b:ℂ)^(-1+α 3-v)*
    (x:ℂ)^(-1-α 1-α 3+u+v)*
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        a03ZeroModeGCDArchKernel Φ T σ 1 a b x s

def a03ZeroModeGCDInitialMNKernel (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) (mn : ℕ×ℕ) : ℂ :=
  a03ZeroModeGCDInitialBase Φ T σ α a b A B x u v s*riemannZeta s*
    a03GCDDirichletTerm a b (α 0-α 1+2*u) (α 2-α 3+2*v) s mn

def a03ZeroModeGCDInitialMNHKernel (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) (mnh : (ℕ×ℕ)×ℕ) : ℂ :=
  a03ZeroModeGCDInitialBase Φ T σ α a b A B x u v s*shiftedPowerArithmetic s mnh.2*
    a03GCDDirichletTerm a b (α 0-α 1+2*u) (α 2-α 3+2*v) s mnh.1

def a03ZeroModeGCDInitialKernel (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) : ℂ :=
  a03ZeroModeGCDInitialBase Φ T σ α a b A B x u v s*riemannZeta s*
    a03GCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s

theorem a03ZeroModeGCDInitialMNKernel_tsum (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) :
    (∑'mn : ℕ×ℕ,a03ZeroModeGCDInitialMNKernel Φ T σ α a b A B x u v s mn)=
      a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s := by
  unfold a03ZeroModeGCDInitialMNKernel a03ZeroModeGCDInitialKernel a03GCDDirichlet
  exact tsum_mul_left

theorem a03ZeroModeGCDInitialMNHKernel_apply (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ)
    {m n h : ℕ} (hm : m≠0) (hn : n≠0) (hh : h≠0) :
    a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B x u v s ((m,n),h)=
      a03ZeroModeGCDInitialBase Φ T σ α a b A B x u v s*(h:ℂ)^(-s)*
        (Nat.gcd (a*m) (b*n):ℂ)^(1-s)*(m:ℂ)^(-1-α 0+α 1-2*u)*(n:ℂ)^(-1-α 2+α 3-2*v) := by
  unfold a03ZeroModeGCDInitialMNHKernel
  rw [shiftedPowerArithmetic_apply _ hh,a03GCDDirichletTerm_apply a b _ _ s hm hn]
  have he : -(1+(α 0-α 1+2*u))= -1-α 0+α 1-2*u := by ring
  have hf : -(1+(α 2-α 3+2*v))= -1-α 2+α 3-2*v := by ring
  rw [he,hf]
  ring

end
end Sechstmoment.Source

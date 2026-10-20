import Mathlib.Tactic.GCongr
import SixthMoment.Certificate.Exact.DenominatorBound
import SixthMoment.Certificate.Exact.NumeratorBound

namespace SixthMoment

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem finite_certificate_ratio :
    declaredBound < 362880*finiteNumerator^2/Finite.finiteDenominator := by
  have hn := finite_numerator_gt_lower
  have hd := Finite.finite_denominator_lt_upper
  have hd₀ := Finite.finite_denominator_pos
  have hn₀ : 0 ≤ finiteNumerator := by linarith
  apply certifiedBound_gt_declared.trans_le
  unfold certifiedBound numeratorLower
  gcongr

end SixthMoment

import Sechstmoment.Certificate.Kernels.Balanced.Sample
import Sechstmoment.Numerator.Kernels.CollisionLimits
import Sechstmoment.Numerator.U.Bounds.SharpGammaFrontReduction
import Sechstmoment.Numerator.U.Bounds.SharpGammaSourceBudget
import Sechstmoment.Numerator.U.Bounds.SharpPassiveSourceBudget
import Sechstmoment.Numerator.U.Bounds.SharpReplacementErrors
import Sechstmoment.Numerator.U.Diagonal.ActualWeightError
import Sechstmoment.Numerator.U.Diagonal.AmplifierReciprocalCount
import Sechstmoment.Numerator.U.Reconstruction.RectangularDyadicTransfer
import Sechstmoment.Numerator.U.Reconstruction.RectangularMassGrowth
import Sechstmoment.Numerator.U.Separation.ActualPhaseRemainder
import Sechstmoment.Numerator.U.Separation.AmplifiedSpatialTruncation
import Sechstmoment.Numerator.U.Sources.BlockBounds
import Sechstmoment.Numerator.U.Sources.Weights.Normalized
import Sechstmoment.Numerator.U.ZeroModes.EightEtaFrontSharpMainBudget
import Sechstmoment.Numerator.V.DP.DPBilinearSourceAdapter
import Sechstmoment.Numerator.V.DP.DPSharpAdapter
import Sechstmoment.Theorem
import Sechstmoment.Zeta.AmplifierProfiles
import Sechstmoment.Zeta.Moments.MixedCauchy

/- The integrated FullGoal assembly uses only literature input 1.
The independent V replacement is checked locally; final assembly replay is deferred. -/

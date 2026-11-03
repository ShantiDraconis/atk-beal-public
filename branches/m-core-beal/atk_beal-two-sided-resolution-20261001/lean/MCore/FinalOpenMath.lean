import MCore.ExactFinalProducer

namespace MCore.BealFinal

/-- Exact arithmetic residual: no wrappers remain. -/
abbrev OpenMathResidual : Prop :=
  GCDLowerBoundProducer

theorem residual_closes_final
    (h : OpenMathResidual) :
    FinalExternalCertificate :=
  finalExternal_of_gcdLowerBound h

end MCore.BealFinal

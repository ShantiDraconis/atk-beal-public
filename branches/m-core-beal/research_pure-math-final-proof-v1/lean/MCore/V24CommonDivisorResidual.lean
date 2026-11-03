import MCore.BealResidualSystem

namespace MCore

theorem primitive_has_no_common_divisor
    (d : PrimitiveBealCandidate) :
    ¬ ∃ k : Nat, CommonDivisor k d.data.a d.data.b d.data.c := by
  intro h
  have hcp : CommonPrime d.data.a d.data.b d.data.c :=
    (commonPrime_iff_commonDivisor).2 h
  exact d.noCommonPrime hcp

theorem normalized_has_no_common_divisor
    (d : NormalizedBealCandidate) :
    ¬ ∃ k : Nat, CommonDivisor k d.data.a d.data.b d.data.c :=
  primitive_has_no_common_divisor d.toPrimitiveBealCandidate

def CommonDivisorResidual : Prop :=
  ∀ d : NormalizedBealCandidate,
    ¬ ∃ k : Nat, CommonDivisor k d.data.a d.data.b d.data.c

theorem commonDivisorResidual_holds : CommonDivisorResidual := by
  intro d
  exact normalized_has_no_common_divisor d

end MCore

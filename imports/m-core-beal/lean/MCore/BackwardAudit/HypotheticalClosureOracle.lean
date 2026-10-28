import MCore.BealSpecification

namespace MCore.BackwardAudit

def HypotheticalClosure : Prop := BealConjecture

theorem hypothetical_common_prime
    (H : HypotheticalClosure) (d : BealData) :
    CommonPrime d.a d.b d.c :=
  H d

#print axioms MCore.BackwardAudit.hypothetical_common_prime

end MCore.BackwardAudit

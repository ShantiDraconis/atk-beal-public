import MCore.BealFinalMathematicalChain

namespace MCore
namespace BealFinal

abbrev FinalExternalCertificate : Prop :=
  BealUniversalCommonPrimeCertificate

def FINAL_ROOT : Prop :=
  BealConjecture

theorem finalExternal_to_FINAL_ROOT
    (E : FinalExternalCertificate) :
    FINAL_ROOT :=
  universalCommonPrime_closes_beal E

def finalExternal_to_proofCertificate
    (E : FinalExternalCertificate) :
    BealProofCertificate :=
  universalCommonPrime_to_proofCertificate E

end BealFinal
end MCore

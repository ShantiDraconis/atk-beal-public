import MCore.FinalExternal
import MCore.GCDLowerBoundProducer

namespace MCore
namespace BealFinal

/-- The exact smallest arithmetic producer currently exposed by the kernel
    closes FinalExternal directly. -/
def finalExternal_of_gcdLowerBound
    (h : GCDLowerBoundProducer) :
    FinalExternalCertificate :=
  {
    witness := fun d =>
      (commonPrime_iff_one_lt_nestedGCD d).mpr (h d)
  }

theorem FINAL_ROOT_of_gcdLowerBound
    (h : GCDLowerBoundProducer) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_gcdLowerBound h)

/-- Equivalent characterization of the final external certificate by the
    scalar nested-gcd lower bound. -/
theorem finalExternal_iff_gcdLowerBound :
    Nonempty FinalExternalCertificate ↔ GCDLowerBoundProducer := by
  constructor
  · rintro ⟨E⟩ d
    exact (commonPrime_iff_one_lt_nestedGCD d).mp (E.witness d)
  · intro h
    exact ⟨finalExternal_of_gcdLowerBound h⟩

#print axioms MCore.BealFinal.finalExternal_of_gcdLowerBound
#print axioms MCore.BealFinal.FINAL_ROOT_of_gcdLowerBound
#print axioms MCore.BealFinal.finalExternal_iff_gcdLowerBound


/-- Equivalent primitive-candidate producer.  T11 already proves that Beal is
    exactly the nonexistence of a pairwise-primitive reduced candidate. -/
def finalExternal_of_no_pairwise_reduced_candidate
    (h : ¬ T11PairwiseReducedCandidate) :
    FinalExternalCertificate := by
  have hBeal : BealConjecture :=
    (T11_beal_iff_pairwise_frontier).2 h
  exact ⟨fun d => hBeal d⟩

/-- Parity-normalized version: T12 preserves the frontier exactly. -/
def finalExternal_of_no_parity_reduced_candidate
    (h : ¬ T12ParityReducedCandidate) :
    FinalExternalCertificate := by
  have hBeal : BealConjecture :=
    (T12_beal_iff_parity_frontier).2 h
  exact ⟨fun d => hBeal d⟩

theorem FINAL_ROOT_of_no_pairwise_reduced_candidate
    (h : ¬ T11PairwiseReducedCandidate) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_no_pairwise_reduced_candidate h)

theorem FINAL_ROOT_of_no_parity_reduced_candidate
    (h : ¬ T12ParityReducedCandidate) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_no_parity_reduced_candidate h)

#print axioms MCore.BealFinal.finalExternal_of_no_pairwise_reduced_candidate
#print axioms MCore.BealFinal.finalExternal_of_no_parity_reduced_candidate
#print axioms MCore.BealFinal.FINAL_ROOT_of_no_pairwise_reduced_candidate
#print axioms MCore.BealFinal.FINAL_ROOT_of_no_parity_reduced_candidate


/-- The first genuinely semantic Beal cut after the exact T7--T34 reductions. -/
def finalExternal_of_global_elimination
    (h : T35GlobalEliminationBridge) :
    FinalExternalCertificate := by
  have hBeal : BealConjecture :=
    (T35_beal_iff_global_elimination_bridge).2 h
  exact ⟨fun d => hBeal d⟩

/-- Fully field-by-field T36--T42 route into FinalExternal. -/
def finalExternal_of_T42_bundle
    {G : T35GapLedger}
    (b : T42FinalProofBundle G) :
    FinalExternalCertificate := by
  have hBeal : BealConjecture :=
    T42_final_bundle_exports_beal b
  exact ⟨fun d => hBeal d⟩

theorem FINAL_ROOT_of_T42_bundle
    {G : T35GapLedger}
    (b : T42FinalProofBundle G) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_T42_bundle b)

#print axioms MCore.BealFinal.finalExternal_of_global_elimination
#print axioms MCore.BealFinal.finalExternal_of_T42_bundle
#print axioms MCore.BealFinal.FINAL_ROOT_of_T42_bundle

end BealFinal
end MCore

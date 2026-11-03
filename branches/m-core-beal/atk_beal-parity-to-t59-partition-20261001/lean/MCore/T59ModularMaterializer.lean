import MCore.T59ParityPartition
import MCore.T58

namespace MCore

/--
Exact bridge from one concrete T59 residual Beal candidate to the lowered
newform layer.

The bridge must preserve the reduced exponent signature. The survivor proof is
explicit: it is mathematical output of the actual Frey/conductor/level-lowering
construction, not metadata.
-/
structure T59LoweredNewformBridge
    (Survives : T44LoweredNewformCase → Prop) where
  lower : T59ResidualCandidate → T44LoweredNewformCase

  x_preserved :
    ∀ d, (lower d).x = d.x
  y_preserved :
    ∀ d, (lower d).y = d.y
  z_preserved :
    ∀ d, (lower d).z = d.z

  survives :
    ∀ d, Survives (lower d)

/--
Any global elimination theorem for the lowered-newform survivor predicate,
combined with a genuine candidate-to-lowered-case bridge, eliminates every
T59 residual candidate.
-/
def T59ResidualEliminator.ofLoweredNewforms
    {Survives : T44LoweredNewformCase → Prop}
    (B : T59LoweredNewformBridge Survives)
    (hElim : T44AllNewformsEliminated Survives) :
    T59ResidualEliminator := by
  intro d
  exact hElim (B.lower d) (B.survives d)

/--
The five-family T58 eliminator closes the T59 residual branch as soon as:
1. every T59 candidate is genuinely lowered to a survivor;
2. every survivor lies in the certified residual domain;
3. all five family-specific elimination certificates are supplied.
-/
def T59ResidualEliminator.ofFiveFamilyBundle
    {Survives : T44LoweredNewformCase → Prop}
    (B : T59LoweredNewformBridge Survives)
    (hDomain : T58ResidualSurvivorDomain Survives)
    (bundle : T58MixedEliminationBundle Survives) :
    T59ResidualEliminator :=
  T59ResidualEliminator.ofLoweredNewforms B
    (T58_five_family_bundle_eliminates_residual_survivors hDomain bundle)

/--
Full Beal closure through the modular route.

The all-four branch and exponent-3 equal-prime branch are already kernel
closed through Mathlib. Therefore the remaining material inputs are exactly:
* FLT at prime exponents > 3 for the equal-prime branch;
* a genuine lowering bridge for every T59 residual candidate;
* residual-domain soundness;
* five family-specific newform elimination certificates.
-/
theorem T59_modular_materializer_closes_beal
    (hBeyond : T59FLTBeyondThree)
    {Survives : T44LoweredNewformCase → Prop}
    (B : T59LoweredNewformBridge Survives)
    (hDomain : T58ResidualSurvivorDomain Survives)
    (bundle : T58MixedEliminationBundle Survives) :
    BealConjecture :=
  T59_beyondThree_and_residual_close_beal hBeyond
    (T59ResidualEliminator.ofFiveFamilyBundle B hDomain bundle)

/--
The lowering bridge automatically preserves the T58 exponent-domain
requirements because T59 candidates already carry the reduced mixed signature
and the not-all-four firewall.
-/
theorem lowered_case_has_t59_signature
    {Survives : T44LoweredNewformCase → Prop}
    (B : T59LoweredNewformBridge Survives)
    (d : T59ResidualCandidate) :
    T7ReducedExponent (B.lower d).x ∧
    T7ReducedExponent (B.lower d).y ∧
    T7ReducedExponent (B.lower d).z ∧
    T45MixedReducedSignature (B.lower d).x (B.lower d).y (B.lower d).z ∧
    ¬ T49AllFour (B.lower d).x (B.lower d).y (B.lower d).z := by
  rw [B.x_preserved d, B.y_preserved d, B.z_preserved d]
  exact ⟨d.x_reduced, d.y_reduced, d.z_reduced, d.mixed, d.notAllFour⟩

#print axioms MCore.T59ResidualEliminator.ofLoweredNewforms
#print axioms MCore.T59ResidualEliminator.ofFiveFamilyBundle
#print axioms MCore.T59_modular_materializer_closes_beal
#print axioms MCore.lowered_case_has_t59_signature

end MCore

import MCore.T51

namespace MCore

/-!
T52 — CERTIFIED SIGNATURE -> LIST LEVEL INTERFACE

The level table is not hard-coded.  A valid table must prove:
* nonemptiness for every residual signature;
* soundness: every listed level is genuinely admissible;
* completeness: every genuinely admissible level is listed.

This is the fail-closed replacement for unproved formulas such as 32, 64,
2*p, or 2*p*q*r.
-/

structure T52ResidualSignature where
  x : Nat
  y : Nat
  z : Nat
  hx : T7ReducedExponent x
  hy : T7ReducedExponent y
  hz : T7ReducedExponent z
  mixed : T45MixedReducedSignature x y z
  notAllFour : ¬ T49AllFour x y z

theorem T52_residual_signature_five_family_coverage
    (s : T52ResidualSignature) :
    T51MixedFiveFamilySplit s.x s.y s.z :=
  T51_mixed_reduced_five_family_split s.mixed s.notAllFour

/-- Semantic predicate supplied by the actual conductor/level-lowering layer. -/
abbrev T52AdmissibleLevel := T52ResidualSignature → Nat → Prop

/-- The desired table shape. -/
abbrev T52ListLevel := T52ResidualSignature → List Nat

structure T52CertifiedLevelTable (AdmissibleLevel : T52AdmissibleLevel) where
  levels : T52ListLevel
  nonempty : ∀ s : T52ResidualSignature, levels s ≠ []
  sound :
    ∀ (s : T52ResidualSignature) (N : Nat),
      N ∈ levels s → AdmissibleLevel s N
  complete :
    ∀ (s : T52ResidualSignature) (N : Nat),
      AdmissibleLevel s N → N ∈ levels s

theorem T52_table_exact_iff
    {AdmissibleLevel : T52AdmissibleLevel}
    (cert : T52CertifiedLevelTable AdmissibleLevel)
    (s : T52ResidualSignature)
    (N : Nat) :
    N ∈ cert.levels s ↔ AdmissibleLevel s N :=
  ⟨cert.sound s N, cert.complete s N⟩

/-- Merely giving each signature a nonempty list is not enough to certify
    level coverage. -/
def T52UniversalNonemptyPromotion : Prop :=
  ∀ (Admissible : Nat → Nat → Prop) (levels : Nat → List Nat),
    (∀ s : Nat, levels s ≠ []) →
    ∀ (s N : Nat), Admissible s N → N ∈ levels s

theorem T52_nonempty_only_is_insufficient :
    ¬ T52UniversalNonemptyPromotion := by
  intro h
  let Admissible : Nat → Nat → Prop := fun s N => s = 0 ∧ N = 2
  let levels : Nat → List Nat := fun _ => [1]
  have hne : ∀ s : Nat, levels s ≠ [] := by
    intro s
    simp [levels]
  have hbad : 2 ∈ levels 0 :=
    h Admissible levels hne 0 2 ⟨rfl, rfl⟩
  simp [levels] at hbad

/-- Exact current scientific state: interface certified, concrete modular
    level table still requires conductor + level-lowering mathematics. -/
def T52LevelTableState : T36GapState :=
  .openBridge

#print axioms MCore.T52_residual_signature_five_family_coverage
#print axioms MCore.T52_table_exact_iff
#print axioms MCore.T52_nonempty_only_is_insufficient

end MCore

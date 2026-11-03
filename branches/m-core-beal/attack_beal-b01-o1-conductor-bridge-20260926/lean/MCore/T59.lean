import MCore.T58

namespace MCore

/-!
T59 — CANDIDATE-KEYED MODULAR LEVEL FRONTIER

T52 deliberately left the semantic predicate [AdmissibleLevel] abstract.
T59 sharpens the key of the level table.

For generalized Fermat/Beal, the lowered level is not determined by the
exponent signature alone.  It is computed from a concrete Frey object and its
local data.  Therefore the certified table is keyed by a residual candidate
(A,B,C,x,y,z), while the signature remains a classification layer only.
-/

/-- Residual Beal candidate after the equal-prime/all-four branches have been
    split away.  These are exactly the arithmetic fields needed before a
    genuine Frey/local-conductor package is attached. -/
structure T59ResidualCandidate where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_reduced : T7ReducedExponent x
  y_reduced : T7ReducedExponent y
  z_reduced : T7ReducedExponent z
  equation : a ^ x + b ^ y = c ^ z
  pairwisePrimitive : T11PairwisePrimitive a b c
  exactlyOneEven : T12ExactlyOneEven a b c
  mixed : T45MixedReducedSignature x y z
  notAllFour : ¬ T49AllFour x y z

/-- Forget bases/local arithmetic and retain only the reduced signature. -/
def T59ResidualCandidate.signature
    (d : T59ResidualCandidate) : T52ResidualSignature :=
  {
    x := d.x
    y := d.y
    z := d.z
    hx := d.x_reduced
    hy := d.y_reduced
    hz := d.z_reduced
    mixed := d.mixed
    notAllFour := d.notAllFour
  }

/-- Every concrete residual candidate is still covered by the five-family
    signature partition frozen at T51. -/
theorem T59_candidate_has_five_family_signature
    (d : T59ResidualCandidate) :
    T51MixedFiveFamilySplit d.x d.y d.z :=
  T51_mixed_reduced_five_family_split d.mixed d.notAllFour

/-- Semantic level predicate supplied by the future Frey/local-conductor and
    level-lowering implementation. -/
abbrev T59CandidateAdmissibleLevel :=
  T59ResidualCandidate → Nat → Prop

/-- A candidate-keyed level table. -/
abbrev T59CandidateLevelTable :=
  T59ResidualCandidate → List Nat

/-- Exact fail-closed certificate for a concrete level table. -/
structure T59CertifiedCandidateLevelTable
    (AdmissibleLevel : T59CandidateAdmissibleLevel) where
  levels : T59CandidateLevelTable
  nonempty :
    ∀ d : T59ResidualCandidate, levels d ≠ []
  sound :
    ∀ (d : T59ResidualCandidate) (N : Nat),
      N ∈ levels d → AdmissibleLevel d N
  complete :
    ∀ (d : T59ResidualCandidate) (N : Nat),
      AdmissibleLevel d N → N ∈ levels d

theorem T59_candidate_table_exact_iff
    {AdmissibleLevel : T59CandidateAdmissibleLevel}
    (cert : T59CertifiedCandidateLevelTable AdmissibleLevel)
    (d : T59ResidualCandidate)
    (N : Nat) :
    N ∈ cert.levels d ↔ AdmissibleLevel d N :=
  ⟨cert.sound d N, cert.complete d N⟩

/-- What it would mean for a table depending only on (x,y,z) to be exact for
    every concrete residual candidate sharing that signature. -/
def T59SignatureOnlyExact
    (AdmissibleLevel : T59CandidateAdmissibleLevel)
    (levels : T52ListLevel) : Prop :=
  ∀ (d : T59ResidualCandidate) (N : Nat),
    N ∈ levels d.signature ↔ AdmissibleLevel d N

/-- Fail-proof theorem: if two concrete candidates with the same signature
    differ on whether a level N is admissible, then no signature-only table can
    be exact for both.  Thus any actual local variation forces the level key to
    contain more data than the exponents alone. -/
theorem T59_signature_only_exact_impossible_of_local_variation
    {AdmissibleLevel : T59CandidateAdmissibleLevel}
    {levels : T52ListLevel}
    {d₁ d₂ : T59ResidualCandidate}
    {N : Nat}
    (hsig : d₁.signature = d₂.signature)
    (h₁ : AdmissibleLevel d₁ N)
    (h₂ : ¬ AdmissibleLevel d₂ N) :
    ¬ T59SignatureOnlyExact AdmissibleLevel levels := by
  intro hExact
  have hm₁ : N ∈ levels d₁.signature :=
    (hExact d₁ N).2 h₁
  have hm₂ : N ∈ levels d₂.signature := by
    rw [← hsig]
    exact hm₁
  exact h₂ ((hExact d₂ N).1 hm₂)

/-- The current frontier is therefore candidate/local-data -> level table,
    not signature -> level table. -/
def T59CandidateLevelState : T36GapState :=
  .openBridge

#print axioms MCore.T59_candidate_has_five_family_signature
#print axioms MCore.T59_candidate_table_exact_iff
#print axioms MCore.T59_signature_only_exact_impossible_of_local_variation

end MCore

import MCore.BealFastExternalEndpoint

namespace MCore

/-!
BEAL PRODUCER ROUTER

Fail-closed formal transport for four independent mathematical mechanisms.
A route may eliminate only a subfamily of Beal data.  No partial route is
promoted to `BealConjecture` without an explicit coverage proof.
-/

/-- A family of admissible Beal instances handled by one mathematical route. -/
abbrev BealFamily := BealData → Prop

/-- Exact constructive control object: a route must produce a genuine common
prime on every datum in its declared family. -/
structure BealFamilyControlCertificate (Family : BealFamily) where
  witness :
    ∀ d : BealData, Family d → CommonPrime d.a d.b d.c

/-- The corresponding no-counterexample statement is derived, not assumed. -/
theorem BealFamilyControlCertificate.excludes
    {Family : BealFamily}
    (C : BealFamilyControlCertificate Family) :
    ∀ d : BealData, Family d → ¬ BealCounterexample d := by
  intro d hd hcounter
  exact hcounter (C.witness d hd)

/-- Universal control object for the canonical Beal endpoint. -/
structure BealUniversalControl where
  witness : ∀ d : BealData, CommonPrime d.a d.b d.c

theorem BealUniversalControl.closes
    (C : BealUniversalControl) : BealConjecture :=
  C.witness

/-- Universal coverage turns family control into the canonical Beal endpoint. -/
structure BealCoveredControlCertificate (Family : BealFamily) where
  control : BealFamilyControlCertificate Family
  coverage : ∀ d : BealData, Family d

def BealCoveredControlCertificate.toUniversal
    {Family : BealFamily}
    (C : BealCoveredControlCertificate Family) :
    BealUniversalControl :=
  ⟨fun d => C.control.witness d (C.coverage d)⟩

/-- Generic semantics for a modular/Frey route.  These are predicates, not
assertions that the corresponding mathematics has already been proved. -/
structure FreyModularSemantics where
  InFamily : BealFamily
  ResidualPrime : BealData → Nat → Prop
  Modular : BealData → Nat → Prop
  Irreducible : BealData → Nat → Prop
  LoweredLevel : BealData → Nat → Nat → Prop
  Weight2NewformExists : Nat → Prop

/-- Modular/Frey producer data.  `noNewformAtLevel` is the formal
`S₂(N₀)=0`-style contradiction input, generalized to any lowered level. -/
structure FreyModularData where
  semantics : FreyModularSemantics
  chooseResidualPrime : ∀ d, semantics.InFamily d → Nat
  residualPrime :
    ∀ d hd, semantics.ResidualPrime d (chooseResidualPrime d hd)
  modular :
    ∀ d hd, semantics.Modular d (chooseResidualPrime d hd)
  irreducible :
    ∀ d hd, semantics.Irreducible d (chooseResidualPrime d hd)
  loweredLevel : ∀ d, semantics.InFamily d → Nat
  levelLowering :
    ∀ d hd,
      semantics.LoweredLevel d
        (chooseResidualPrime d hd)
        (loweredLevel d hd)
  noNewformAtLevel :
    ∀ d hd, ¬ semantics.Weight2NewformExists (loweredLevel d hd)
  /-- The genuinely mathematical final implication for this route. -/
  contradiction :
    ∀ d hd,
      semantics.Modular d (chooseResidualPrime d hd) →
      semantics.Irreducible d (chooseResidualPrime d hd) →
      semantics.LoweredLevel d
        (chooseResidualPrime d hd)
        (loweredLevel d hd) →
      (¬ semantics.Weight2NewformExists (loweredLevel d hd)) →
      CommonPrime d.a d.b d.c

def FreyModularData.toControl
    (D : FreyModularData) :
    BealFamilyControlCertificate D.semantics.InFamily :=
  { witness := by
      intro d hd
      exact D.contradiction d hd
        (D.modular d hd)
        (D.irreducible d hd)
        (D.levelLowering d hd)
        (D.noNewformAtLevel d hd) }

/-- ABC/Szpiro route contract.  The actual abc inequality and the deduction
to a common prime remain explicit fields. -/
structure AbcData where
  InFamily : BealFamily
  AbcControl : BealData → Prop
  abc : ∀ d, InFamily d → AbcControl d
  abcImpliesCommonPrime :
    ∀ d, InFamily d → AbcControl d → CommonPrime d.a d.b d.c

def AbcData.toControl (D : AbcData) :
    BealFamilyControlCertificate D.InFamily :=
  { witness := fun d hd => D.abcImpliesCommonPrime d hd (D.abc d hd) }

/-- Effective linear-forms route.  The bound and finite verification are
separate so an effective bound is not confused with completion of the finite
check. -/
structure BakerData where
  InFamily : BealFamily
  BoundCertificate : BealData → Prop
  FiniteCheckCertificate : BealData → Prop
  effectiveBound : ∀ d, InFamily d → BoundCertificate d
  finiteCheck :
    ∀ d, InFamily d → BoundCertificate d → FiniteCheckCertificate d
  finiteCheckImpliesCommonPrime :
    ∀ d, InFamily d → FiniteCheckCertificate d → CommonPrime d.a d.b d.c

def BakerData.toControl (D : BakerData) :
    BealFamilyControlCertificate D.InFamily :=
  { witness := by
      intro d hd
      exact D.finiteCheckImpliesCommonPrime d hd
        (D.finiteCheck d hd (D.effectiveBound d hd)) }

/-- Higher-dimensional Frey/hypergeometric route. -/
structure HypergeometricSemantics where
  InFamily : BealFamily
  RepresentationExists : BealData → Prop
  Modular : BealData → Prop
  Irreducible : BealData → Prop
  LoweringContradiction : BealData → Prop

structure HypergeometricData where
  semantics : HypergeometricSemantics
  representation :
    ∀ d, semantics.InFamily d → semantics.RepresentationExists d
  modularityOfRepresentation :
    ∀ d, semantics.InFamily d →
      semantics.RepresentationExists d → semantics.Modular d
  irreducibility :
    ∀ d, semantics.InFamily d →
      semantics.RepresentationExists d → semantics.Irreducible d
  levelLoweringContradiction :
    ∀ d, semantics.InFamily d →
      semantics.Modular d →
      semantics.Irreducible d →
      semantics.LoweringContradiction d
  contradictionImpliesCommonPrime :
    ∀ d, semantics.InFamily d →
      semantics.LoweringContradiction d → CommonPrime d.a d.b d.c

def HypergeometricData.toControl (D : HypergeometricData) :
    BealFamilyControlCertificate D.semantics.InFamily :=
  { witness := by
      intro d hd
      have hrep := D.representation d hd
      have hmod := D.modularityOfRepresentation d hd hrep
      have hirr := D.irreducibility d hd hrep
      have hcontra := D.levelLoweringContradiction d hd hmod hirr
      exact D.contradictionImpliesCommonPrime d hd hcontra }

/-- The four parallel OPEN_MATH mechanisms. -/
inductive BealProducer where
  | modularFreyCurve (d : FreyModularData)
  | abcSzpiroTransform (d : AbcData)
  | linearFormsInLogs (d : BakerData)
  | newFreyVariety (d : HypergeometricData)

def BealProducer.family : BealProducer → BealFamily
  | .modularFreyCurve d => d.semantics.InFamily
  | .abcSzpiroTransform d => d.InFamily
  | .linearFormsInLogs d => d.InFamily
  | .newFreyVariety d => d.semantics.InFamily

def BealProducer.toFamilyControl :
    (P : BealProducer) → BealFamilyControlCertificate P.family
  | .modularFreyCurve d => d.toControl
  | .abcSzpiroTransform d => d.toControl
  | .linearFormsInLogs d => d.toControl
  | .newFreyVariety d => d.toControl

/-- One producer closes all of Beal only if its family covers every admissible
datum.  This is the fail-closed global promotion rule. -/
structure BealUniversalProducer where
  producer : BealProducer
  coverage : ∀ d : BealData, producer.family d

def BealUniversalProducer.toEndpoint
    (P : BealUniversalProducer) :
    BealUniversalControl :=
  ⟨fun d =>
      P.producer.toFamilyControl.witness d (P.coverage d)⟩

theorem producer_closes_beal
    (P : BealUniversalProducer) :
    BealConjecture :=
  P.toEndpoint.closes

/-- Multiple partial routes may be combined.  Each datum must be routed to
one producer whose declared family contains it. -/
structure BealProducerCover where
  producers : List BealProducer
  covers :
    ∀ d : BealData,
      ∃ P, P ∈ producers ∧ P.family d

/-- A cover is not yet enough to close Beal: one also needs a selected
producer together with its membership proof for each datum.  This selector
keeps the transport constructive and explicit. -/
structure BealProducerSelector (C : BealProducerCover) where
  select : BealData → BealProducer
  inList : ∀ d, select d ∈ C.producers
  handles : ∀ d, (select d).family d

def BealProducerSelector.toEndpoint
    {C : BealProducerCover}
    (S : BealProducerSelector C) :
    BealUniversalControl :=
  ⟨fun d =>
      (S.select d).toFamilyControl.witness d (S.handles d)⟩

theorem producer_cover_closes_beal
    {C : BealProducerCover}
    (S : BealProducerSelector C) :
    BealConjecture :=
  S.toEndpoint.closes

#print axioms MCore.BealFamilyControlCertificate.excludes
#print axioms MCore.producer_closes_beal
#print axioms MCore.producer_cover_closes_beal

end MCore

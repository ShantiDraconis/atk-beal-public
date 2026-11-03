import MCore.K10
import MCore.K8
import MCore.BealThreeLaneClosure

namespace MCore

/-! FASTEST LOGICALLY EXACT ENDPOINT

`K10.commonPrime_iff_commonDivisor` means the terminal producer does not need
to construct a prime directly.  It is enough to construct any common divisor
> 1; K10 extracts a prime divisor constructively.
-/

/-- Per-datum nontrivial common-divisor witness. -/
structure BealCommonDivisorWitness (d : BealData) where
  divisor : Nat
  nontrivial : 1 < divisor
  dvdA : divisor ∣ d.a
  dvdB : divisor ∣ d.b
  dvdC : divisor ∣ d.c

def BealCommonDivisorWitness.toExists
    {d : BealData} (W : BealCommonDivisorWitness d) :
    ∃ g : Nat, CommonDivisor g d.a d.b d.c :=
  ⟨W.divisor, W.nontrivial, W.dvdA, W.dvdB, W.dvdC⟩

/-- Fast universal producer: only a nontrivial common divisor per datum. -/
structure BealCommonDivisorProducer where
  produce : ∀ d : BealData, BealCommonDivisorWitness d

theorem commonDivisorProducer_to_commonPrime
    (P : BealCommonDivisorProducer)
    (d : BealData) : CommonPrime d.a d.b d.c :=
  (commonPrime_iff_commonDivisor).2 (P.produce d).toExists

theorem commonDivisorProducer_closes_beal
    (P : BealCommonDivisorProducer) : BealConjecture :=
  closeBeal_from_commonPrime_witnesses
    (commonDivisorProducer_to_commonPrime P)

/-- Converse: Beal itself provides the common-divisor producer.  Hence this
    endpoint is not weaker or stronger than Beal; it is an exact reformulation. -/
noncomputable def beal_to_commonDivisorProducer
    (H : BealConjecture) : BealCommonDivisorProducer :=
  { produce := fun d =>
      let hDiv : ∃ g : Nat, CommonDivisor g d.a d.b d.c :=
        (commonPrime_iff_commonDivisor).1 (H d)
      let g : Nat := Classical.choose hDiv
      let hg : CommonDivisor g d.a d.b d.c :=
        Classical.choose_spec hDiv
      { divisor := g
        nontrivial := hg.1
        dvdA := hg.2.1
        dvdB := hg.2.2.1
        dvdC := hg.2.2.2 } }

theorem beal_iff_commonDivisorProducer :
    BealConjecture ↔ Nonempty BealCommonDivisorProducer := by
  constructor
  · intro H
    exact ⟨beal_to_commonDivisorProducer H⟩
  · rintro ⟨P⟩
    exact commonDivisorProducer_closes_beal P

/-- Minimal final external proof object for the shortest exact route. -/
structure BealFastExternalProof where
  endpoint : BealCommonDivisorProducer

theorem BealFastExternalProof.closes
    (P : BealFastExternalProof) : BealConjecture :=
  commonDivisorProducer_closes_beal P.endpoint

def BealFastExternalProof.toCertificate
    (P : BealFastExternalProof) : BealProofCertificate :=
  ⟨P.closes⟩

#print axioms MCore.commonDivisorProducer_to_commonPrime
#print axioms MCore.commonDivisorProducer_closes_beal
#print axioms MCore.beal_iff_commonDivisorProducer
#print axioms MCore.BealFastExternalProof.closes

end MCore

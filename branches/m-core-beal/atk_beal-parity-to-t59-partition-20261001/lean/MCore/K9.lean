import MCore.K8
import MCore.GCDSignature
import MCore.K9.Core.Arith

namespace MCore

/-- The elementary prime-divisor theorem isolated as an explicit dependency.
    K9 does not assume or axiomatize it: downstream closure must supply a proof. -/
def PrimeDivisorProperty : Prop :=
  ∀ n : Nat, 1 < n → ∃ p : Nat, IsPrime p ∧ p ∣ n

/-- Core-only transitivity of natural-number divisibility, proved by witness composition. -/
theorem nat_dvd_trans {a b c : Nat} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨k, hk⟩
  rcases hbc with ⟨l, hl⟩
  refine ⟨k * l, ?_⟩
  calc
    c = b * l := hl
    _ = (a * k) * l := congrArg (fun n : Nat => n * l) hk
    _ = a * (k * l) := K9.Core.mul_assoc_core a k l

/-- A prime divisor of a nontrivial common divisor yields a common prime. -/
theorem commonDivisor_to_commonPrime_of_primeDivisor
    (hPD : PrimeDivisorProperty) {a b c : Nat}
    (h : ∃ d : Nat, CommonDivisor d a b c) : CommonPrime a b c := by
  rcases h with ⟨d, hdgt, hda, hdb, hdc⟩
  rcases hPD d hdgt with ⟨p, hp, hpd⟩
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · exact nat_dvd_trans hpd hda
  · exact nat_dvd_trans hpd hdb
  · exact nat_dvd_trans hpd hdc

/-- Under the isolated prime-divisor property, common-prime and nontrivial
    common-divisor formulations are equivalent. -/
theorem commonPrime_iff_commonDivisor_of_primeDivisor
    (hPD : PrimeDivisorProperty) {a b c : Nat} :
    CommonPrime a b c ↔ ∃ d : Nat, CommonDivisor d a b c := by
  constructor
  · exact commonPrime_to_commonDivisor
  · exact commonDivisor_to_commonPrime_of_primeDivisor hPD

end MCore

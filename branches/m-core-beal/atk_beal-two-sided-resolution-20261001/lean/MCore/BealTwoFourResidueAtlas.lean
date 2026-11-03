import Mathlib
import MCore.BealResidualMod16

namespace MCore

/--
For odd exponent p, the two-four signature x=z=4 forces an explicit mod-16
condition according to which base is the unique even one.
-/
theorem T59_two_four_xz_residue_atlas
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    (T12Even d.a -> d.b ^ d.y % 16 = 1) ∧
    (T12Even d.b -> d.a ^ 4 % 16 = 1) ∧
    (T12Even d.c -> d.b ^ d.y % 16 = 15) := by
  constructor
  · intro ha
    have hbOdd : d.b % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact (T12_not_even_iff_odd d.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hcOdd : d.c % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact (T12_not_even_iff_odd d.c).mp hA.2.2
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    have hA16 : d.a ^ 4 % 16 = 0 := beal_even_fourth_mod_sixteen ha
    have hC16 : d.c ^ 4 % 16 = 1 := beal_odd_fourth_mod_sixteen hcOdd
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    simpa [hx, hz, Nat.add_mod, hA16, hC16] using hmod
  constructor
  · intro hb
    have haOdd : d.a % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (T12_not_even_iff_odd d.a).mp hB.1
      · exact False.elim (hC.2.1 hb)
    exact beal_odd_fourth_mod_sixteen haOdd
  · intro hc
    have haOdd : d.a % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (T12_not_even_iff_odd d.a).mp hC.1
    have hA16 : d.a ^ 4 % 16 = 1 := beal_odd_fourth_mod_sixteen haOdd
    have hC16 : d.c ^ 4 % 16 = 0 := beal_even_fourth_mod_sixteen hc
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    have hsum : (1 + (d.b ^ d.y % 16)) % 16 = 0 := by
      simpa [hx, hz, Nat.add_mod, hA16, hC16] using hmod
    omega

/--
Symmetric residue atlas for the signature y=z=4.
-/
theorem T59_two_four_yz_residue_atlas
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    (T12Even d.a -> d.b ^ 4 % 16 = 1) ∧
    (T12Even d.b -> d.a ^ d.x % 16 = 1) ∧
    (T12Even d.c -> d.a ^ d.x % 16 = 15) := by
  constructor
  · intro ha
    have hbOdd : d.b % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact (T12_not_even_iff_odd d.b).mp hA.2.1
      · exact False.elim (hB.1 ha)
      · exact False.elim (hC.1 ha)
    exact beal_odd_fourth_mod_sixteen hbOdd
  constructor
  · intro hb
    have hcOdd : d.c % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.1 hb)
      · exact (T12_not_even_iff_odd d.c).mp hB.2.2
      · exact False.elim (hC.2.1 hb)
    have hB16 : d.b ^ 4 % 16 = 0 := beal_even_fourth_mod_sixteen hb
    have hC16 : d.c ^ 4 % 16 = 1 := beal_odd_fourth_mod_sixteen hcOdd
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    simpa [hy, hz, Nat.add_mod, hB16, hC16] using hmod
  · intro hc
    have hbOdd : d.b % 2 = 1 := by
      rcases d.exactlyOneEven with hA | hB | hC
      · exact False.elim (hA.2.2 hc)
      · exact False.elim (hB.2.2 hc)
      · exact (T12_not_even_iff_odd d.b).mp hC.2.1
    have hB16 : d.b ^ 4 % 16 = 1 := beal_odd_fourth_mod_sixteen hbOdd
    have hC16 : d.c ^ 4 % 16 = 0 := beal_even_fourth_mod_sixteen hc
    have hmod := congrArg (fun n : Nat => n % 16) d.equation
    have hsum : (d.a ^ d.x % 16 + 1) % 16 = 0 := by
      simpa [hy, hz, Nat.add_mod, hB16, hC16] using hmod
    omega

/--
Complete elementary local atlas for all permutations of the (4,4,p) family.
It exposes the residue conditions that remain before any Frey/conductor input.
-/
def T59TwoFourPrimeResidueAtlas (d : T59ResidualCandidate) : Prop :=
  (d.x = 4 -> d.y = 4 -> d.c ^ d.z % 16 = 1) ∧
  (d.x = 4 -> d.z = 4 ->
    (T12Even d.a -> d.b ^ d.y % 16 = 1) ∧
    (T12Even d.b -> d.a ^ 4 % 16 = 1) ∧
    (T12Even d.c -> d.b ^ d.y % 16 = 15)) ∧
  (d.y = 4 -> d.z = 4 ->
    (T12Even d.a -> d.b ^ 4 % 16 = 1) ∧
    (T12Even d.b -> d.a ^ d.x % 16 = 1) ∧
    (T12Even d.c -> d.a ^ d.x % 16 = 15))

theorem T59_two_four_prime_residue_atlas
    (d : T59ResidualCandidate) :
    T59TwoFourPrimeResidueAtlas d := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun hx hy => T59_two_four_forces_rhs_pow_mod_sixteen d hx hy
  · exact fun hx hz => T59_two_four_xz_residue_atlas d hx hz
  · exact fun hy hz => T59_two_four_yz_residue_atlas d hy hz

#print axioms MCore.T59_two_four_xz_residue_atlas
#print axioms MCore.T59_two_four_yz_residue_atlas
#print axioms MCore.T59_two_four_prime_residue_atlas

end MCore

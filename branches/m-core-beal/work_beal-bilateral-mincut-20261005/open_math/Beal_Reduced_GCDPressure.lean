import MCore.BealEffective.ReducedFamilies

namespace MCore
namespace BealEffective
namespace OpenMath

private def reducedToBealData
    (r : ReducedPrimitiveCandidate) : BealData where
  a := r.a
  b := r.b
  c := r.c
  x := r.x
  y := r.y
  z := r.z
  a_pos := r.a_pos
  b_pos := r.b_pos
  c_pos := r.c_pos
  x_gt_two := r.x_reduced.1
  y_gt_two := r.y_reduced.1
  z_gt_two := r.z_reduced.1
  equation := r.equation

/-- Every reduced primitive candidate is pairwise primitive in the project predicate. -/
theorem reduced_pairwisePrimitive_core
    (r : ReducedPrimitiveCandidate) :
    PairwisePrimitive r.a r.b r.c := by
  constructor
  · intro hab
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      ab_pair_forces_common (reducedToBealData r) hab
    exact r.no_common hcommon
  constructor
  · intro hac
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      ac_pair_forces_common (reducedToBealData r) hac
    exact r.no_common hcommon
  · intro hbc
    have hcommon :
        ∃ p : Nat, CommonDivisor p r.a r.b r.c :=
      bc_pair_forces_common (reducedToBealData r) hbc
    exact r.no_common hcommon

/-- Project pairwise-primitivity forces gcd(a,b)=1. -/
theorem reduced_gcd_ab_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.b = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hda hdb
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hda with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.a_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((reduced_pairwisePrimitive_core r).1 ⟨d, hdgt, hda, hdb⟩)

/-- Project pairwise-primitivity forces gcd(a,c)=1. -/
theorem reduced_gcd_ac_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.c = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hda hdc
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hda with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.a_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((reduced_pairwisePrimitive_core r).2.1 ⟨d, hdgt, hda, hdc⟩)

/-- Project pairwise-primitivity forces gcd(b,c)=1. -/
theorem reduced_gcd_bc_eq_one
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.b r.c = 1 := by
  apply (Nat.gcd_eq_one_iff).2
  intro d hdb hdc
  by_cases hd1 : d = 1
  · exact hd1
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    rcases hdb with ⟨k, hk⟩
    simp at hk
    exact (Nat.ne_of_gt r.b_pos) hk
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdgt : 1 < d := by
    have hle : 1 ≤ d := Nat.succ_le_of_lt hdpos
    exact Nat.lt_of_le_of_ne hle (Ne.symm hd1)
  exact False.elim ((reduced_pairwisePrimitive_core r).2.2 ⟨d, hdgt, hdb, hdc⟩)

/-- All three pairwise gcd equalities, packaged without adding hypotheses. -/
theorem reduced_pairwise_gcd_packet
    (r : ReducedPrimitiveCandidate) :
    Nat.gcd r.a r.b = 1 ∧
    Nat.gcd r.a r.c = 1 ∧
    Nat.gcd r.b r.c = 1 := by
  exact ⟨
    reduced_gcd_ab_eq_one r,
    reduced_gcd_ac_eq_one r,
    reduced_gcd_bc_eq_one r
  ⟩

#print axioms MCore.BealEffective.OpenMath.reduced_pairwisePrimitive_core
#print axioms MCore.BealEffective.OpenMath.reduced_gcd_ab_eq_one
#print axioms MCore.BealEffective.OpenMath.reduced_gcd_ac_eq_one
#print axioms MCore.BealEffective.OpenMath.reduced_gcd_bc_eq_one
#print axioms MCore.BealEffective.OpenMath.reduced_pairwise_gcd_packet

end OpenMath
end BealEffective
end MCore

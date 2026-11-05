import MCore.T9

namespace MCore

/-- Core power-add identity, kept local so exponent normalization does not
    require an external algebra package. -/
theorem T10_pow_add (a m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]

/-- Reassociate a power so a chosen divisor of the exponent becomes the
    outer exponent. -/
theorem T10_pow_mul_outer (a k r : Nat) :
    (a ^ k) ^ r = a ^ (k * r) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Nat.pow_succ, ih, Nat.mul_succ, T10_pow_add]

/-- Purely propositional reduced candidate. Keeping this in Prop permits the
    constructive T7 existential witnesses to be consumed without choice. -/
def T10ReducedCandidate : Prop :=
  ∃ a b c x y z : Nat,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    T7ReducedExponent x ∧
    T7ReducedExponent y ∧
    T7ReducedExponent z ∧
    a ^ x + b ^ y = c ^ z ∧
    (¬ ∃ q : Nat, CommonDivisor q a b c)

def T10ReducedScientificFrontier : Prop :=
  ¬ T10ReducedCandidate

/-- Every T6 primitive candidate has a reduced-signature representative. -/
theorem T10_candidate_to_reduced :
    Nonempty T6PrimitiveSolution → T10ReducedCandidate := by
  rintro ⟨s⟩
  rcases T7_exponent_reduction s.x_gt_two with ⟨rx, kx, hx, hrx⟩
  rcases T7_exponent_reduction s.y_gt_two with ⟨ry, ky, hy, hry⟩
  rcases T7_exponent_reduction s.z_gt_two with ⟨rz, kz, hz, hrz⟩
  have hax : (s.a ^ kx) ^ rx = s.a ^ s.x := by
    calc
      (s.a ^ kx) ^ rx = s.a ^ (kx * rx) := T10_pow_mul_outer s.a kx rx
      _ = s.a ^ (rx * kx) := by rw [Nat.mul_comm kx rx]
      _ = s.a ^ s.x := (congrArg (fun n : Nat => s.a ^ n) hx).symm
  have hby : (s.b ^ ky) ^ ry = s.b ^ s.y := by
    calc
      (s.b ^ ky) ^ ry = s.b ^ (ky * ry) := T10_pow_mul_outer s.b ky ry
      _ = s.b ^ (ry * ky) := by rw [Nat.mul_comm ky ry]
      _ = s.b ^ s.y := (congrArg (fun n : Nat => s.b ^ n) hy).symm
  have hcz : (s.c ^ kz) ^ rz = s.c ^ s.z := by
    calc
      (s.c ^ kz) ^ rz = s.c ^ (kz * rz) := T10_pow_mul_outer s.c kz rz
      _ = s.c ^ (rz * kz) := by rw [Nat.mul_comm kz rz]
      _ = s.c ^ s.z := (congrArg (fun n : Nat => s.c ^ n) hz).symm
  refine ⟨s.a ^ kx, s.b ^ ky, s.c ^ kz, rx, ry, rz,
    Nat.pow_pos s.a_pos, Nat.pow_pos s.b_pos, Nat.pow_pos s.c_pos,
    hrx, hry, hrz, ?_, T9_powered_primitive_unconditional s.primitive⟩
  calc
    (s.a ^ kx) ^ rx + (s.b ^ ky) ^ ry
        = s.a ^ s.x + s.b ^ s.y := by rw [hax, hby]
    _ = s.c ^ s.z := s.equation
    _ = (s.c ^ kz) ^ rz := hcz.symm

/-- Every reduced-signature candidate is already a T6 primitive candidate. -/
theorem T10_reduced_to_candidate :
    T10ReducedCandidate → Nonempty T6PrimitiveSolution := by
  rintro ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, heq, hprim⟩
  exact ⟨{
    a := a
    b := b
    c := c
    x := x
    y := y
    z := z
    a_pos := ha
    b_pos := hb
    c_pos := hc
    x_gt_two := hx.1
    y_gt_two := hy.1
    z_gt_two := hz.1
    equation := heq
    primitive := hprim
  }⟩

/-- Exact normalization: primitive candidates exist iff reduced-signature
    primitive candidates exist. -/
theorem T10_candidate_iff_reduced :
    Nonempty T6PrimitiveSolution ↔ T10ReducedCandidate :=
  ⟨T10_candidate_to_reduced, T10_reduced_to_candidate⟩

theorem T10_frontier_iff_reduced :
    T6ScientificFrontier ↔ T10ReducedScientificFrontier := by
  unfold T6ScientificFrontier T10ReducedScientificFrontier
  exact not_congr T10_candidate_iff_reduced

theorem T10_beal_iff_reduced_frontier :
    BealConjecture ↔ T10ReducedScientificFrontier :=
  T6_beal_iff_frontier.trans T10_frontier_iff_reduced

#print axioms MCore.T10_pow_add
#print axioms MCore.T10_pow_mul_outer
#print axioms MCore.T10_candidate_to_reduced
#print axioms MCore.T10_candidate_iff_reduced
#print axioms MCore.T10_beal_iff_reduced_frontier

end MCore

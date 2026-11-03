import MCore.BealTwoFourSharpResidues

namespace MCore

/-- Closed form of the existing T21 difference quotient at exponent four. -/
theorem T21DiffQuot_four
    (c a : Nat) :
    T21DiffQuot c a 4 =
      (c + a) * (c ^ 2 + a ^ 2) := by
  simp [T21DiffQuot, Nat.pow_succ]
  ring

/--
Exact factorization for the residual signature x=z=4:
b^y = (c-a)(c+a)(c^2+a^2).
This reuses the already-certified equal-exponent factorization instead of
introducing a new subtraction argument.
-/
theorem T59_xz_four_exact_factorization
    (d : T59ResidualCandidate)
    (hx : d.x = 4)
    (hz : d.z = 4) :
    d.b ^ d.y =
      (d.c - d.a) *
        ((d.c + d.a) * (d.c ^ 2 + d.a ^ 2)) := by
  have hEq :
      d.b ^ d.y =
        (d.c - d.a) * T21DiffQuot d.c d.a d.x :=
    T22_x_eq_z_exact_factor
      d.b_pos d.equation (by simpa [hx, hz])
  rw [hx, T21DiffQuot_four] at hEq
  exact hEq

/--
Symmetric exact factorization for y=z=4:
a^x = (c-b)(c+b)(c^2+b^2).
-/
theorem T59_yz_four_exact_factorization
    (d : T59ResidualCandidate)
    (hy : d.y = 4)
    (hz : d.z = 4) :
    d.a ^ d.x =
      (d.c - d.b) *
        ((d.c + d.b) * (d.c ^ 2 + d.b ^ 2)) := by
  have hEq :
      d.a ^ d.x =
        (d.c - d.b) * T21DiffQuot d.c d.b d.y :=
    T22_y_eq_z_exact_factor
      d.a_pos d.equation (by simpa [hy, hz])
  rw [hy, T21DiffQuot_four] at hEq
  exact hEq

/--
The quartic residual factorization package for the two-four family.
-/
structure T59QuarticFactorizationPacket
    (d : T59ResidualCandidate) : Prop where
  xz_four :
    d.x = 4 ->
    d.z = 4 ->
    d.b ^ d.y =
      (d.c - d.a) *
        ((d.c + d.a) * (d.c ^ 2 + d.a ^ 2))
  yz_four :
    d.y = 4 ->
    d.z = 4 ->
    d.a ^ d.x =
      (d.c - d.b) *
        ((d.c + d.b) * (d.c ^ 2 + d.b ^ 2))

theorem T59_quartic_factorization_packet
    (d : T59ResidualCandidate) :
    T59QuarticFactorizationPacket d where
  xz_four := fun hx hz =>
    T59_xz_four_exact_factorization d hx hz
  yz_four := fun hy hz =>
    T59_yz_four_exact_factorization d hy hz

#print axioms MCore.T21DiffQuot_four
#print axioms MCore.T59_xz_four_exact_factorization
#print axioms MCore.T59_yz_four_exact_factorization
#print axioms MCore.T59_quartic_factorization_packet

end MCore

import MCore.OpenMath.BealQ10SevenFamilies
import MCore.K10

namespace MCore.OpenMath.BealQ10

open MCore.OpenMath.BealProbe

def PairCommonDivisor (q a b : Nat) : Prop :=
  1 < q ∧ q ∣ a ∧ q ∣ b

private theorem prime_dvd_mul_local
    {p a b : Nat}
    (hp : MCore.IsPrime p)
    (hab : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  rcases (Nat.dvd_mul.mp hab) with ⟨p₁, p₂, hp₁a, hp₂b, hprod⟩
  have hp₁p : p₁ ∣ p := ⟨p₂, hprod.symm⟩
  rcases hp.2 p₁ hp₁p with hp₁one | hp₁eq
  · subst p₁
    have hp₂eq : p₂ = p := by simpa using hprod
    subst p₂
    exact Or.inr hp₂b
  · subst p₁
    exact Or.inl hp₁a

private theorem prime_not_dvd_one
    {p : Nat}
    (hp : MCore.IsPrime p) :
    ¬ p ∣ 1 := by
  intro h
  have hle : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) h
  exact (Nat.not_le_of_gt hp.1) hle

theorem prime_dvd_pow_reflect
    {p a n : Nat}
    (hp : MCore.IsPrime p)
    (hpow : p ∣ a ^ n) :
    p ∣ a := by
  induction n with
  | zero =>
      have : p ∣ 1 := by simpa using hpow
      exact False.elim (prime_not_dvd_one hp this)
  | succ n ih =>
      have hmul : p ∣ a ^ n * a := by
        simpa [Nat.pow_succ] using hpow
      rcases prime_dvd_mul_local hp hmul with hprev | ha
      · exact ih hprev
      · exact ha

def NoCommonDivisor (a b c : Nat) : Prop :=
  ¬ ∃ q : Nat, 1 < q ∧ q ∣ a ∧ q ∣ b ∧ q ∣ c

theorem primitive_no_common
    (d : MCore.BealData)
    (hd : PrimitiveBealSolution d) :
    NoCommonDivisor d.a d.b d.c := by
  rintro ⟨q, hq, hqa, hqb, hqc⟩
  have hab : q ∣ Nat.gcd d.a d.b := Nat.dvd_gcd hqa hqb
  have hg : q ∣ observedDefect d := Nat.dvd_gcd hab hqc
  rw [hd] at hg
  have hqle : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hg
  exact (Nat.not_le_of_gt hq) hqle

theorem powered_no_common
    {a b c ka kb kc : Nat}
    (hNo : NoCommonDivisor a b c) :
    NoCommonDivisor (a ^ ka) (b ^ kb) (c ^ kc) := by
  rintro ⟨q, hq, hqa, hqb, hqc⟩
  rcases MCore.primeDivisorProperty_proved q hq with ⟨p, hp, hpq⟩
  have hpaPow : p ∣ a ^ ka := MCore.nat_dvd_trans hpq hqa
  have hpbPow : p ∣ b ^ kb := MCore.nat_dvd_trans hpq hqb
  have hpcPow : p ∣ c ^ kc := MCore.nat_dvd_trans hpq hqc
  have hpa : p ∣ a := prime_dvd_pow_reflect hp hpaPow
  have hpb : p ∣ b := prime_dvd_pow_reflect hp hpbPow
  have hpc : p ∣ c := prime_dvd_pow_reflect hp hpcPow
  exact hNo ⟨p, hp.1, hpa, hpb, hpc⟩

structure PrimitiveReducedCandidate extends ReducedCandidate where
  no_common : NoCommonDivisor a b c

theorem primitive_to_primitiveReduced
    (d : MCore.BealData)
    (hd : PrimitiveBealSolution d) :
    Nonempty PrimitiveReducedCandidate := by
  rcases exponent_reduction d.x_gt_two with ⟨rx, kx, hx, hrx⟩
  rcases exponent_reduction d.y_gt_two with ⟨ry, ky, hy, hry⟩
  rcases exponent_reduction d.z_gt_two with ⟨rz, kz, hz, hrz⟩
  have hax : (d.a ^ kx) ^ rx = d.a ^ d.x := by
    calc
      (d.a ^ kx) ^ rx = d.a ^ (kx * rx) := (Nat.pow_mul d.a kx rx).symm
      _ = d.a ^ (rx * kx) := by rw [Nat.mul_comm]
      _ = d.a ^ d.x := by rw [← hx]
  have hby : (d.b ^ ky) ^ ry = d.b ^ d.y := by
    calc
      (d.b ^ ky) ^ ry = d.b ^ (ky * ry) := (Nat.pow_mul d.b ky ry).symm
      _ = d.b ^ (ry * ky) := by rw [Nat.mul_comm]
      _ = d.b ^ d.y := by rw [← hy]
  have hcz : (d.c ^ kz) ^ rz = d.c ^ d.z := by
    calc
      (d.c ^ kz) ^ rz = d.c ^ (kz * rz) := (Nat.pow_mul d.c kz rz).symm
      _ = d.c ^ (rz * kz) := by rw [Nat.mul_comm]
      _ = d.c ^ d.z := by rw [← hz]
  refine ⟨{
    toReducedCandidate := {
      a := d.a ^ kx
      b := d.b ^ ky
      c := d.c ^ kz
      x := rx
      y := ry
      z := rz
      a_pos := Nat.pow_pos d.a_pos
      b_pos := Nat.pow_pos d.b_pos
      c_pos := Nat.pow_pos d.c_pos
      x_reduced := hrx
      y_reduced := hry
      z_reduced := hrz
      equation := ?_
    }
    no_common := powered_no_common (primitive_no_common d hd)
  }⟩
  calc
    (d.a ^ kx) ^ rx + (d.b ^ ky) ^ ry
        = d.a ^ d.x + d.b ^ d.y := by rw [hax, hby]
    _ = d.c ^ d.z := d.equation
    _ = (d.c ^ kz) ^ rz := hcz.symm

theorem primitiveReduced_seven_family
    (r : PrimitiveReducedCandidate) :
    SevenFamilySplit r.x r.y r.z :=
  reduced_signature_seven_family r.x_reduced r.y_reduced r.z_reduced

#print axioms MCore.OpenMath.BealQ10.primitive_no_common
#print axioms MCore.OpenMath.BealQ10.powered_no_common
#print axioms MCore.OpenMath.BealQ10.primitive_to_primitiveReduced

end MCore.OpenMath.BealQ10

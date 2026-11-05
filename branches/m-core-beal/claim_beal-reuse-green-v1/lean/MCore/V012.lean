import MCore.K10

namespace MCore

/-- V0 residue: starting from the actual Beal data (including the
    Diophantine equation and exponents > 2), produce a nontrivial
    common divisor of a, b, and c. -/
def V0EquationToCommonDivisor : Prop :=
  ∀ d : BealData, ∃ q : Nat, CommonDivisor q d.a d.b d.c

/-- T0: any Beal proof implies the V0 divisor residue. -/
theorem T0_beal_to_v0
    (h : BealConjecture) : V0EquationToCommonDivisor := by
  intro d
  exact (commonPrime_iff_commonDivisor).mp (h d)

/-- T1 / V1 backward closure: once V0 is discharged, K10 converts the
    nontrivial common divisor into a common prime, closing Beal. -/
theorem T1_v0_to_beal
    (h : V0EquationToCommonDivisor) : BealConjecture := by
  intro d
  exact (commonPrime_iff_commonDivisor).mpr (h d)

/-- V2 collision: after K10, the Beal endpoint is exactly equivalent to V0.
    This isolates the remaining mathematical bridge without promoting it. -/
theorem T2_v2_collision :
    BealConjecture ↔ V0EquationToCommonDivisor :=
  ⟨T0_beal_to_v0, T1_v0_to_beal⟩

/-- T3 sharpens V0 by removing the BealData wrapper.  This is the raw
    Diophantine bridge that remains to be proved. -/
def T3RawEquationDivisorBridge : Prop :=
  ∀ a b c x y z : Nat,
    0 < a → 0 < b → 0 < c →
    2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y = c ^ z →
    ∃ q : Nat, CommonDivisor q a b c

theorem T3_v0_iff_raw :
    V0EquationToCommonDivisor ↔ T3RawEquationDivisorBridge := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz heq
    let d : BealData :=
      { a := a
        b := b
        c := c
        x := x
        y := y
        z := z
        a_pos := ha
        b_pos := hb
        c_pos := hc
        x_gt_two := hx
        y_gt_two := hy
        z_gt_two := hz
        equation := heq }
    exact h d
  · intro h d
    exact h d.a d.b d.c d.x d.y d.z
      d.a_pos d.b_pos d.c_pos d.x_gt_two d.y_gt_two d.z_gt_two d.equation

/-- T4 is the constructive obstruction direction: if T3 holds, there is no
    admissible equation with no nontrivial common divisor. -/
def T4NoPrimitiveEquation : Prop :=
  ∀ a b c x y z : Nat,
    0 < a → 0 < b → 0 < c →
    2 < x → 2 < y → 2 < z →
    (¬ ∃ q : Nat, CommonDivisor q a b c) →
    a ^ x + b ^ y ≠ c ^ z

theorem T4_from_T3
    (h : T3RawEquationDivisorBridge) : T4NoPrimitiveEquation := by
  intro a b c x y z ha hb hc hx hy hz hNo heq
  exact hNo (h a b c x y z ha hb hc hx hy hz heq)

/-- T5: existence of a nontrivial common divisor is stable for positive a,
    because every such divisor is bounded by a and bounded search is decidable. -/
theorem T5_commonDivisor_exists_stable
    {a b c : Nat} (ha : 0 < a) :
    ¬¬ (∃ q : Nat, CommonDivisor q a b c) →
      ∃ q : Nat, CommonDivisor q a b c := by
  intro hnn
  let P : Nat → Prop := fun q =>
    q < a + 1 ∧ 1 < q ∧ q ∣ a ∧ q ∣ b ∧ q ∣ c
  have instP (q : Nat) : Decidable (P q) := inferInstance
  let hex : Decidable (∃ q, q < a + 1 ∧ 1 < q ∧ q ∣ a ∧ q ∣ b ∧ q ∣ c) :=
    inferInstance
  match hex with
  | isTrue h =>
      rcases h with ⟨q, _, hqgt, hqa, hqb, hqc⟩
      exact ⟨q, hqgt, hqa, hqb, hqc⟩
  | isFalse h =>
      exfalso
      apply hnn
      intro hexists
      rcases hexists with ⟨q, hqgt, hqa, hqb, hqc⟩
      have hqa_copy : q ∣ a := hqa
      rcases hqa with ⟨k, hak⟩
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk0
        subst k
        have hz : q * 0 = 0 := Nat.mul_zero q
        exact Nat.ne_of_gt ha (hak.trans hz)
      have hqle : q ≤ a := by
        rw [hak]
        exact Nat.le_mul_of_pos_right q hkpos
      apply h
      exact ⟨q, Nat.lt_succ_of_le hqle, hqgt, hqa_copy, hqb, hqc⟩

/-- Reverse obstruction direction, now constructive: T4 implies T3. -/
theorem T5_T4_to_T3
    (h : T4NoPrimitiveEquation) : T3RawEquationDivisorBridge := by
  intro a b c x y z ha hb hc hx hy hz heq
  apply T5_commonDivisor_exists_stable ha
  intro hNo
  exact (h a b c x y z ha hb hc hx hy hz hNo) heq

theorem T5_T3_iff_T4 :
    T3RawEquationDivisorBridge ↔ T4NoPrimitiveEquation :=
  ⟨T4_from_T3, T5_T4_to_T3⟩

/-- T6 packages the exact surviving mathematical obstruction as data.
    A value of this structure would be a primitive Beal counterexample in the
    common-divisor formulation. -/
structure T6PrimitiveSolution where
  a : Nat
  b : Nat
  c : Nat
  x : Nat
  y : Nat
  z : Nat
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  x_gt_two : 2 < x
  y_gt_two : 2 < y
  z_gt_two : 2 < z
  equation : a ^ x + b ^ y = c ^ z
  primitive : ¬ ∃ q : Nat, CommonDivisor q a b c

def T6ScientificFrontier : Prop :=
  ¬ Nonempty T6PrimitiveSolution

theorem T6_T4_iff_no_primitive :
    T4NoPrimitiveEquation ↔ T6ScientificFrontier := by
  constructor
  · intro h hs
    rcases hs with ⟨s⟩
    exact (h s.a s.b s.c s.x s.y s.z
      s.a_pos s.b_pos s.c_pos
      s.x_gt_two s.y_gt_two s.z_gt_two
      s.primitive) s.equation
  · intro h a b c x y z ha hb hc hx hy hz hprimitive heq
    apply h
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
      x_gt_two := hx
      y_gt_two := hy
      z_gt_two := hz
      equation := heq
      primitive := hprimitive
    }⟩

/-- Exact collision statement after V0/V1/V2 and T3-T5:
    Beal is equivalent to the absence of a T6 primitive solution. -/
theorem T6_beal_iff_frontier :
    BealConjecture ↔ T6ScientificFrontier := by
  calc
    BealConjecture ↔ V0EquationToCommonDivisor := T2_v2_collision
    _ ↔ T3RawEquationDivisorBridge := T3_v0_iff_raw
    _ ↔ T4NoPrimitiveEquation := T5_T3_iff_T4
    _ ↔ T6ScientificFrontier := T6_T4_iff_no_primitive

theorem T3_closes_beal
    (h : T3RawEquationDivisorBridge) : BealConjecture :=
  T1_v0_to_beal ((T3_v0_iff_raw).mpr h)

#print axioms MCore.T0_beal_to_v0
#print axioms MCore.T1_v0_to_beal
#print axioms MCore.T2_v2_collision
#print axioms MCore.T3_v0_iff_raw
#print axioms MCore.T4_from_T3
#print axioms MCore.T3_closes_beal
#print axioms MCore.T5_commonDivisor_exists_stable
#print axioms MCore.T5_T4_to_T3
#print axioms MCore.T5_T3_iff_T4
#print axioms MCore.T6_T4_iff_no_primitive
#print axioms MCore.T6_beal_iff_frontier

end MCore

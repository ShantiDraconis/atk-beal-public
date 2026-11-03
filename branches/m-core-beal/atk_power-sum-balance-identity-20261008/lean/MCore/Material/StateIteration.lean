import MCore.Material.Closure

namespace MCore.Material

/-- Iteration of a state transformation: N^(0)=N and N^(n+1)=T(N^n). -/
def stateIter {α : Type} (T : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => T (stateIter T n s)

@[simp] theorem stateIter_zero {α : Type} (T : α → α) (s : α) :
    stateIter T 0 s = s := rfl

@[simp] theorem stateIter_succ {α : Type} (T : α → α) (n : Nat) (s : α) :
    stateIter T (n + 1) s = T (stateIter T n s) := rfl

/-- A strict Nat-valued descent decreases at every finite iterate. -/
theorem stateIter_measure_strict
    {α : Type} (T : α → α) (μ : α → Nat)
    (hdec : ∀ s, μ (T s) < μ s)
    (n : Nat) (s : α) :
    μ (stateIter T (n + 1) s) < μ (stateIter T n s) := by
  exact hdec (stateIter T n s)

/-- A state space cannot support a globally strict Nat-valued self-descent transform.
This is the well-founded obstruction behind the N -> N^(n) scheme. -/
theorem no_global_nat_descent
    {α : Type} (T : α → α) (μ : α → Nat)
    (hdec : ∀ s, μ (T s) < μ s) :
    IsEmpty α := by
  refine ⟨fun s => ?_⟩
  let P : Nat → Prop := fun m => ∀ s : α, μ s = m → False
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro s hs
        have hlt : μ (T s) < m := by
          simpa [hs] using hdec s
        exact ih (μ (T s)) hlt (T s) rfl
  exact hP (μ s) s rfl

/-- Consequently, a globally defined strict descent on an inhabited state
space is impossible.  A material descent proof must restrict the transform
to nonterminal/counterexample states and prove termination separately. -/
theorem inhabited_forbids_global_nat_descent
    {α : Type} [Nonempty α] (T : α → α) (μ : α → Nat) :
    ¬ (∀ s, μ (T s) < μ s) := by
  intro hdec
  letI : IsEmpty α := no_global_nat_descent T μ hdec
  exact not_nonempty_iff.mpr inferInstance (inferInstance : Nonempty α)

#print axioms MCore.Material.stateIter_measure_strict
#print axioms MCore.Material.no_global_nat_descent
#print axioms MCore.Material.inhabited_forbids_global_nat_descent

end MCore.Material

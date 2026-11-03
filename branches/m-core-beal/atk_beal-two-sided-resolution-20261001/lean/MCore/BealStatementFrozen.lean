import MCore.BealSpecification

namespace MCore

/-- Frozen alias of the repository's canonical Beal statement.
    The external manifest carries the source/content hash. -/
abbrev BealStatementFrozen : Prop := BealConjecture

theorem beal_statement_frozen_exact :
    BealStatementFrozen ↔ BealConjecture := by
  rfl

#print axioms MCore.beal_statement_frozen_exact

end MCore

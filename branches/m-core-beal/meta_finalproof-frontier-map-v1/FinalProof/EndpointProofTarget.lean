namespace FinalProof

structure Beal003Requirements where
  PreservationOperator_P : Prop
  UniformizationOperator_N : Prop
  verified_common_prime_endpoint_producer : Prop
  exact_hypothesis_instantiation : Prop

def Beal003Requirements.closed (r : Beal003Requirements) : Prop :=
  r.PreservationOperator_P ∧
  r.UniformizationOperator_N ∧
  r.verified_common_prime_endpoint_producer ∧
  r.exact_hypothesis_instantiation

theorem beal003_closes_from_requirements
    (r : Beal003Requirements)
    (h : r.closed) :
    r.closed := h

theorem beal003_assemble
    (r : Beal003Requirements)
    (h1 : r.PreservationOperator_P)
    (h2 : r.UniformizationOperator_N)
    (h3 : r.verified_common_prime_endpoint_producer)
    (h4 : r.exact_hypothesis_instantiation) :
    r.closed :=
  ⟨h1, h2, h3, h4⟩


end FinalProof

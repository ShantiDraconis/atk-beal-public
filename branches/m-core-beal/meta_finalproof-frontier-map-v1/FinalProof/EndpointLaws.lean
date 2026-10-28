import FinalProof.EndpointProofTarget

namespace FinalProof

theorem beal003_has_P
    (r : Beal003Requirements) (h : r.closed) :
    r.PreservationOperator_P := h.1

theorem beal003_has_N
    (r : Beal003Requirements) (h : r.closed) :
    r.UniformizationOperator_N := h.2.1

theorem beal003_has_endpoint_producer
    (r : Beal003Requirements) (h : r.closed) :
    r.verified_common_prime_endpoint_producer := h.2.2.1

theorem beal003_has_exact_instantiation
    (r : Beal003Requirements) (h : r.closed) :
    r.exact_hypothesis_instantiation := h.2.2.2

theorem beal003_all_requirements_iff
    (r : Beal003Requirements) :
    r.closed ↔
      r.PreservationOperator_P ∧
      r.UniformizationOperator_N ∧
      r.verified_common_prime_endpoint_producer ∧
      r.exact_hypothesis_instantiation := by
  rfl

end FinalProof

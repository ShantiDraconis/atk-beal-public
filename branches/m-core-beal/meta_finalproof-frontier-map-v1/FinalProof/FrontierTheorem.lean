namespace FinalProof

/-- Beal endpoint boundary: certified infrastructure alone does not close the
common-prime endpoint when the endpoint producer obligation is missing. -/
structure BealEndpointFrontier (A P B : Prop) where
  infrastructure : A
  missingEndpointProducer : ¬ P
  endpointRequires : B → P

theorem beal_endpoint_unreachable
    {A P B : Prop} (f : BealEndpointFrontier A P B) : ¬ B := by
  intro hB
  exact f.missingEndpointProducer (f.endpointRequires hB)

end FinalProof

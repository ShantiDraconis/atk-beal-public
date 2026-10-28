namespace MCore.V5

inductive PromotionStatus where
  | allowed
  | blockedNeedsSoundness
  | circular
  | openBridge
deriving DecidableEq, Repr

def metadataPromotion
    (usesEndpointHypothesis hasSoundness hasIncompleteProof : Bool) : PromotionStatus :=
  if usesEndpointHypothesis then .circular
  else if hasIncompleteProof then .openBridge
  else if !hasSoundness then .blockedNeedsSoundness
  else .allowed

theorem endpoint_hypothesis_blocks (s t : Bool) :
    metadataPromotion true s t = .circular := by
  simp [metadataPromotion]

end MCore.V5

import MCore.BealSpecification
import MCore.V5.Surgery

namespace MCore.V5

structure CounterexamplePayload where
  data : MCore.BealData
  noCommonPrime : MCore.BealCounterexample data

def bottomOfCounterexample (ce : CounterexamplePayload) :
    OmegaBottom MCore.BealData :=
  omegaBottom ce.data

def pointOfCounterexample (ce : CounterexamplePayload) :
    OmegaPoint MCore.BealData :=
  S (bottomOfCounterexample ce)

@[simp] theorem counterexample_payload_preserved (ce : CounterexamplePayload) :
    (pointOfCounterexample ce).payload = ce.data := rfl

end MCore.V5

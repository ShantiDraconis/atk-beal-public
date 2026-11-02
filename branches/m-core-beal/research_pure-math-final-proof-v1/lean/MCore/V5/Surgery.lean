import MCore.V5.OmegaPoint
import MCore.V5.OmegaBottom

namespace MCore.V5

/-- Structural transport only. It preserves the payload and proves no endpoint statement. -/
def Surgery : OmegaBottom α → OmegaPoint α
  | .mk a => .mk a

def S : OmegaBottom α → OmegaPoint α := Surgery

@[simp] theorem S_maps_bottom_to_point (a : α) :
    S (omegaBottom a) = omegaPoint a := rfl

@[simp] theorem S_preserves_payload (b : OmegaBottom α) :
    (S b).payload = b.payload := by
  cases b
  rfl

end MCore.V5

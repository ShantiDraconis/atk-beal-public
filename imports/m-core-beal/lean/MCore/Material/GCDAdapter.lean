import MCore.Material.Closure
import MCore.GCDLowerBoundProducer
namespace MCore.Material
def BealCanonicalMaterial : Prop := MCore.GCDLowerBoundProducer
theorem beal_material_iff_endpoint : MCore.BealConjecture ↔ BealCanonicalMaterial := MCore.bealConjecture_iff_gcdLowerBoundProducer
end MCore.Material

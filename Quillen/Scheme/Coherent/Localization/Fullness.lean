import Quillen.Scheme.Coherent.Localization.SubobjectExtension
import Quillen.Scheme.Coherent.Localization.AffineSectionsGlobal

/-!
# Fullness of actual coherent restriction from the support quotient

The quasicoherence of open pushforward is proved by finite denominator
clearing and actual open base change. The preimage-kernel construction and
graph fractions therefore give unconditional fullness on locally noetherian
schemes. Essential surjectivity still requires coherent object extension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Every coherent subsheaf on the open extends inside its given coherent
ambient sheaf by the actual quasicoherent preimage kernel. -/
theorem coherent_subobject_extension (H : Coherent X) (A : Coherent U)
    (i : A ⟶ (coherentRestriction j).obj H) [Mono i] :
    ∃ (H' : Coherent X) (s : H' ⟶ H), Mono s ∧
      ∃ (e : (coherentRestriction j).obj H' ≅ A),
        (coherentRestriction j).map s = e.hom ≫ i := by
  have : (cokernel i.hom).IsQuasicoherent := quasicoherent_cokernel i.hom
  have : ((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent :=
    quasicoherent_pushforward_open_of_locallyNoetherian j _
  exact coherent_subobject_extension_of_quasicoherent_pushforward j H A i

/-- Actual coherent open morphisms admit supported-Serre fractions on the
ambient locally noetherian scheme. -/
theorem coherent_exists_fraction {M N : Coherent X}
    (φ : (coherentRestriction j).obj M ⟶ (coherentRestriction j).obj N) :
    ∃ (M' : Coherent X) (s : M' ⟶ M) (g : M' ⟶ N),
      (coherentSupportedAway j).isoModSerre s ∧
        (coherentRestriction j).map s ≫ φ = (coherentRestriction j).map g := by
  apply coherent_fraction_of_subobject_extension j
  intro H A i hi
  have : Mono i := hi
  exact coherent_subobject_extension j H A i

/-- The canonical functor from the actual support quotient is full.
Faithfulness and exactness were already proved in `Quotient`. -/
instance quotientCoherentRestriction_full : (quotientCoherentRestriction j).Full := by
  apply quotientCoherentRestriction_full_of_quasicoherent_pushforward j
  intro M hM
  have : M.IsQuasicoherent := hM
  exact quasicoherent_pushforward_open_of_locallyNoetherian j M

end Quillen.CoherentScheme

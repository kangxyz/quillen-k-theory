import Quillen.Scheme.Coherent.Affine.GTheory
import Quillen.Scheme.Sheaf.AffineSupport

/-!
# Actual supported coherent sheaves on a noetherian affine scheme

The support category is the kernel of actual open restriction, applied to
actual coherent sheaves. Its Serre property is proved from exactness of the
inclusion and restriction functors. Its objects have ordinary closed stalk
support, and vanishing on the open is equivalent to support in its complement.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The ordinary stalk support of an affine coherent sheaf is closed. -/
theorem isClosed_support (M : AffineCoherent R) :
    IsClosed (SchemeSheaf.support ((affineCoherentToSheaves R).obj M)) :=
  SchemeSheaf.isClosed_support_of_finite_globalSections _

variable {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Coherent sheaves supported outside the actual open immersion. -/
def affineSupportedAway : ObjectProperty (AffineCoherent R) :=
  (SchemeSheaf.supportedAway j).inverseImage (affineCoherentToSheaves R)

@[simp]
theorem affineSupportedAway_iff (M : AffineCoherent R) :
    affineSupportedAway R j M ↔
      IsZero ((Scheme.Modules.restrictFunctor j).obj ((affineCoherentToSheaves R).obj M)) :=
  Iff.rfl

/-- The support property is a genuine Serre property in coherent sheaves. -/
instance affineSupportedAway_isSerreClass : (affineSupportedAway R j).IsSerreClass := by
  change ((SchemeSheaf.supportedAway j).inverseImage (affineCoherentToSheaves R)).IsSerreClass
  infer_instance

/-- Vanishing on the open is equivalent to disjointness of stalk support and
its image. -/
theorem affineSupportedAway_iff_support_disjoint (M : AffineCoherent R) :
    affineSupportedAway R j M ↔
      Disjoint (SchemeSheaf.support ((affineCoherentToSheaves R).obj M)) (Set.range j) :=
  SchemeSheaf.supportedAway_iff_support_disjoint j _

/-- Equivalently, ordinary stalk support is contained in the open complement. -/
theorem affineSupportedAway_iff_support_subset (M : AffineCoherent R) :
    affineSupportedAway R j M ↔
      SchemeSheaf.support ((affineCoherentToSheaves R).obj M) ⊆ (Set.range j)ᶜ := by
  rw [affineSupportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The full abelian category of actual supported coherent sheaves. -/
abbrev SupportedAffineCoherent := (affineSupportedAway R j).FullSubcategory

instance supportedAffineCoherent_abelian : Abelian (SupportedAffineCoherent R j) := inferInstance

instance supportedAffineCoherent_essentiallySmall :
    EssentiallySmall.{u} (SupportedAffineCoherent R j) :=
  essentiallySmall_of_fully_faithful (affineSupportedAway R j).ι

/-- Its standard abelian exact structure. -/
def supportedAffineCoherentExactStructure : ExactStructure (SupportedAffineCoherent R j) :=
  abelianExactStructure _

/-- G-theory with support, formed from the actual supported coherent category. -/
abbrev SupportedAffineG (n : ℕ) : Type u :=
  ExactStructure.SmallK.{u} (supportedAffineCoherentExactStructure R j) n

end Quillen.CoherentScheme

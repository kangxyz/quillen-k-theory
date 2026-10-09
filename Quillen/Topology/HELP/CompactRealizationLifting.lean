import Quillen.Topology.HELP.Compact
import Quillen.Topology.Realization.MonomorphismLifting

/-!
# Compact HELP supplies lifting against all realized simplicial inclusions

Actual compact simplex-boundary cofibrations are the generators. The
mapping-path endpoint then lifts over every realized simplicial mono by
the proved relative skeletal construction.
-/
noncomputable section
open CategoryTheory Limits Topology MonoidalCategory
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

/-- The actual realized simplex boundary inclusion has HEP, including the
empty boundary in dimension zero. -/
theorem homotopyExtensionProperty_realizationBoundary (n : ℕ) :
    homotopyExtensionProperty (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u}))) := by
  let P := |(Δ[0] : SSet.{u})|
  let a := (realizationBoundaryHomeomorph n).trans
    (Homeomorph.uniqueProd P (simplexBoundary n)).symm
  let b := (SimplexCategory.toTopHomeo ⦋n⦌).trans
    (Homeomorph.uniqueProd P (Convexity.StdSimplex ℝ (Fin (n + 1)))).symm
  apply homotopyExtensionProperty_of_iso_square _
    (parameterizedSimplexBoundaryInclusion P n) (TopCat.isoOfHomeo a) (TopCat.isoOfHomeo b)
    _ (homotopyExtensionProperty_simplexBoundary P n)
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

end Quillen.TheoremA

namespace Quillen.MappingPath
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : CompactHomotopyExtensionLiftingProperty f)
include hf

/-- Compact HELP implies right lifting of the actual mapping-path endpoint
against every realized simplicial monomorphism. -/
theorem endpoint_hasLiftingProperty_realization_mono
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) (TopCat.ofHom (endpoint f)) := by
  apply hasLiftingProperty_realization_mono
  intro n
  have : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  exact endpoint_hasLiftingProperty_of_compactHELP f hf _
    (TheoremA.homotopyExtensionProperty_realizationBoundary n)

end Quillen.MappingPath

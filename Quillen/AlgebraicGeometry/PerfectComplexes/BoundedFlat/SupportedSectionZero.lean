/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionZero

/-!
# The original chosen zero in actual supported sections

The source-independent original zero section is genuinely supported and remains literally the
same chosen section under every original supported coefficient map. These are the actual zero
objects required by a supported iterated-S model and its strict coefficient functors.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The existing original zero section satisfies actual acyclicity on every specified open. -/
theorem boundedFlatAffineSectionZero_supported (j : U ⟶ Spec R) [IsOpenImmersion j] :
    boundedFlatAffineSectionSupported j (boundedFlatAffineSectionZero R) := by
  change ((restrict j).obj ((boundedFlatAffineOriginalEvaluation R).obj
    (boundedFlatAffineSectionZero R)).obj).Acyclic
  rw [boundedFlatAffineOriginalEvaluation_sectionZero]
  exact HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero
    ((boundedFlatPerfect (Spec R)).ι.map_isZero (boundedFlatPerfectWaldhausen (Spec R)).isZero))

/-- The supported chosen zero is the same original source-independent section. -/
def boundedFlatAffineSupportedSectionZero (j : U ⟶ Spec R) [IsOpenImmersion j] :
    BoundedFlatAffineSupportedSections j :=
  ⟨boundedFlatAffineSectionZero R, boundedFlatAffineSectionZero_supported j⟩

/-- The unchanged chosen section is a genuine zero object in the actual supported category. -/
theorem isZero_boundedFlatAffineSupportedSectionZero
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    IsZero (boundedFlatAffineSupportedSectionZero j) :=
  IsZero.of_full_of_faithful_of_isZero (boundedFlatAffineSectionSupported j).ι _
    (isZero_boundedFlatAffineSectionZero R)

/-- Every original supported coefficient restriction retains this same chosen zero literally. -/
theorem boundedFlatAffineSupportedSectionsMap_sectionZero
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    (boundedFlatAffineSupportedSectionsMap j j' f l h).obj
        (boundedFlatAffineSupportedSectionZero j) =
      boundedFlatAffineSupportedSectionZero j' := by
  apply ObjectProperty.FullSubcategory.ext
  exact boundedFlatAffineSectionsMap_sectionZero f

end Quillen.PerfectComplexes

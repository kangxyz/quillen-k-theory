/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionReindex

/-!
# Original supported coefficient and Laurent-unit consumers

Arbitrary open squares, actual evaluated complexes, original unit and inverse-unit maps, and
the original chosen zero remain visible. No negative localization is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Tests.SupportedSections
open PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt

include l h in
/-- The actual reindexed section is acyclic on the original specified target open. -/
theorem original_reindexed_acyclic (s : BoundedFlatAffineSupportedSections j) (n : ℤ) :
    ((restrict j').obj ((boundedFlatAffineOriginalEvaluation S).obj
      ((boundedFlatAffineSectionsMap f).obj s.obj)).obj).ExactAt n :=
  (boundedFlatAffineSectionsMap_supported j j' f l h s.obj s.property) n

/-- The supported action forgets to the exact same original global-unit section map. -/
theorem original_unit_forward (r : (Γ(Spec R, ⊤))ˣ)
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionUnitIso j r).hom.app s).hom =
      (boundedFlatAffineSectionUnitIso R r).hom.app s.obj :=
  boundedFlatAffineSupportedSectionUnitIso_hom j r s

/-- The supported inverse action retains the actual inverse original scalar map. -/
theorem original_unit_inverse (r : (Γ(Spec R, ⊤))ˣ)
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionUnitIso j r).inv.app s).hom =
      (boundedFlatAffineSectionUnitIso R r).inv.app s.obj :=
  boundedFlatAffineSupportedSectionUnitIso_inv j r s

/-- The whole original coefficient square preserves the actual supported unit component. -/
theorem original_unit_coefficient (r : (Γ(Spec R, ⊤))ˣ)
    (s : BoundedFlatAffineSupportedSections j) :
    (boundedFlatAffineSupportedSectionsMap j j' f l h).map
        ((boundedFlatAffineSupportedSectionUnitIso j r).hom.app s) =
      (boundedFlatAffineSupportedSectionUnitIso j'
        (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).hom.app
          ((boundedFlatAffineSupportedSectionsMap j j' f l h).obj s) :=
  NatTrans.congr_app (boundedFlatAffineSupportedSectionUnitIso_coefficient_hom j j' f l h r) s

/-- Original support evaluation retains the same underlying chain complex. -/
theorem original_supported_complex (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedEvaluation j).obj s).obj =
      ((boundedFlatAffineOriginalEvaluation R).obj s.obj).obj := rfl

/-- The unchanged original pointwise zero is retained by every supported coefficient square. -/
theorem original_supported_zero :
    (boundedFlatAffineSupportedSectionsMap j j' f l h).obj
        (boundedFlatAffineSupportedSectionZero j) =
      boundedFlatAffineSupportedSectionZero j' :=
  boundedFlatAffineSupportedSectionsMap_sectionZero j j' f l h

/-- The original supported unit fixes the actual chosen zero by its genuine zero property. -/
theorem original_unit_zero (r : (Γ(Spec R, ⊤))ˣ) :
    (boundedFlatAffineSupportedSectionUnitIso j r).hom.app
        (boundedFlatAffineSupportedSectionZero j) =
      𝟙 (boundedFlatAffineSupportedSectionZero j) :=
  (isZero_boundedFlatAffineSupportedSectionZero j).eq_of_src _ _

end Quillen.Tests.SupportedSections

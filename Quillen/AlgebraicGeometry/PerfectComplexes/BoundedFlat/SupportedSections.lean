/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback

/-!
# Actual supported bounded-flat affine sections

Support means actual acyclicity after the specified original open restriction at identity
evaluation. The original cocartesian evaluation transition proves that coefficient reindexing
preserves this support along every commuting affine open-pair square. The underlying section,
coefficient functor and chain maps are unchanged. No negative localization is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}

attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt

/-- Actual support of a section is acyclicity of its original evaluated complex on the open. -/
def boundedFlatAffineSectionSupported (j : U ⟶ Spec R) [IsOpenImmersion j] :
    ObjectProperty (BoundedFlatAffineSections R) := fun s ↦
  ((restrict j).obj ((boundedFlatAffineOriginalEvaluation R).obj s).obj).Acyclic

/-- Supported objects are original cocartesian sections with the actual support predicate. -/
abbrev BoundedFlatAffineSupportedSections (j : U ⟶ Spec R) [IsOpenImmersion j] :=
  (boundedFlatAffineSectionSupported j).FullSubcategory

/-- Original evaluation lands in the original supported bounded-flat category. -/
def boundedFlatAffineSupportedEvaluation (j : U ⟶ Spec R) [IsOpenImmersion j] :
    BoundedFlatAffineSupportedSections j ⥤ (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatPerfectSupported j).lift
    ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R ⋙
      (boundedFlatPerfect (Spec R)).ι)
    (fun s ↦ ⟨((boundedFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)

/-- Forgetting support after evaluation retains the literal original chain complex. -/
theorem boundedFlatAffineSupportedEvaluation_obj (j : U ⟶ Spec R) [IsOpenImmersion j]
    (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedEvaluation j).obj s).obj =
      ((boundedFlatAffineOriginalEvaluation R).obj s.obj).obj := rfl

/-- The original coefficient reindexing preserves support along the specified whole open square.
-/
theorem boundedFlatAffineSectionsMap_supported
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
    (s : BoundedFlatAffineSections R) (hs : boundedFlatAffineSectionSupported j s) :
    boundedFlatAffineSectionSupported j' ((boundedFlatAffineSectionsMap f).obj s) := by
  let sq : (⟨Arrow.mk j', (show IsOpenImmersion j' from inferInstance)⟩ :
      Quillen.Scheme.OpenPairs) ⟶ ⟨Arrow.mk j, (show IsOpenImmersion j from inferInstance)⟩ :=
    ObjectProperty.homMk (Arrow.homMk l (Spec.map f) h)
  have hp := boundedFlatPerfectSupported_pairPullback sq
    (K := ((boundedFlatAffineOriginalEvaluation R).obj s).obj)
    ⟨((boundedFlatAffineOriginalEvaluation R).obj s).property, hs⟩
  change ((restrict j').obj
    ((boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S).obj s).obj).Acyclic
  rw [boundedFlatAffineSectionsMap_comp_evaluation]
  intro n
  exact (hp.2 n).of_iso ((restrict j').mapIso ((boundedFlatPerfect (Spec S)).ι.mapIso
    ((boundedFlatAffineEvaluationPullbackIso R (Under.mk f)).app s)))

/-- Restrict the unchanged coefficient functor to its actual supported objects. -/
def boundedFlatAffineSupportedSectionsMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    BoundedFlatAffineSupportedSections j ⥤ BoundedFlatAffineSupportedSections j' :=
  (boundedFlatAffineSectionSupported j').lift
    ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineSectionsMap f)
    (fun s ↦ boundedFlatAffineSectionsMap_supported j j' f l h s.obj s.property)

/-- Forgetting support retains the same coefficient reindexing, on objects and morphisms. -/
theorem boundedFlatAffineSupportedSectionsMap_forget
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSupportedSectionsMap j j' f l h ⋙
        (boundedFlatAffineSectionSupported j').ι =
      (boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineSectionsMap f := rfl

end Quillen.PerfectComplexes

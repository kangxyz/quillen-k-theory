/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSupportedSections


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Aglib.CategoryTheory.ObjectProperty.NestedEquivalence
public import Quillen.Aglib.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Actual supported sections on the joint native coefficient family

A support condition is actual acyclicity of the original evaluated complex on
its specified open. The original identity evaluation restricts to a genuine
equivalence with supported bounded-flat complexes. Its Waldhausen structure
uses the restriction of the same joint global zero section.

Every commuting support square over an original joint index arrow restricts
the original section reindexing to an exact, literally zero-preserving functor.
The constructions impose no compactness or flatness condition on the schemes
or coefficient maps. They supply no supported density or quotient theorem.
-/
@[expose] public section

open Quillen.Waldhausen


open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {i k t : Index R} {U V W : Scheme.{u}}
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation

/-- The one joint global zero section is supported on every specified open. -/
theorem boundedFlatCoefficientSectionZero_supported
    (j : U ⟶ space i) [IsOpenImmersion j] :
    boundedFlatCoefficientSectionSupported j (boundedFlatCoefficientSectionZero i) := by
  change ((restrict j).obj ((boundedFlatCoefficientOriginalEvaluation i).obj
    (boundedFlatCoefficientSectionZero i)).obj).Acyclic
  rw [boundedFlatCoefficientOriginalEvaluation_sectionZero]
  exact HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero
    ((boundedFlatPerfect (space i)).ι.map_isZero (boundedFlatPerfectWaldhausen (space i)).isZero))

/-- The supported chosen zero is precisely the existing restricted joint zero. -/
def boundedFlatCoefficientSupportedSectionZero
    (j : U ⟶ space i) [IsOpenImmersion j] : BoundedFlatCoefficientSupportedSections j :=
  ⟨boundedFlatCoefficientSectionZero i, boundedFlatCoefficientSectionZero_supported j⟩

/-- The same joint zero has its actual universal property in the supported category. -/
theorem isZero_boundedFlatCoefficientSupportedSectionZero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsZero (boundedFlatCoefficientSupportedSectionZero j) :=
  IsZero.of_full_of_faithful_of_isZero (boundedFlatCoefficientSectionSupported j).ι _
    (isZero_boundedFlatCoefficientSectionZero i)

/-- Original supported evaluation carries the same joint zero to a genuine zero. -/
theorem boundedFlatCoefficientSupportedEvaluation_sectionZero_isZero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsZero ((boundedFlatCoefficientSupportedEvaluation j).obj
      (boundedFlatCoefficientSupportedSectionZero j)) := by
  apply IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectSupported j).ι
  change IsZero (((boundedFlatCoefficientOriginalEvaluation i).obj
    (boundedFlatCoefficientSectionZero i)).obj)
  rw [boundedFlatCoefficientOriginalEvaluation_sectionZero]
  exact (boundedFlatPerfect (space i)).ι.map_isZero (boundedFlatPerfectWaldhausen (space i)).isZero

/-- Original supported morphism classes and pushouts retain the one joint zero. -/
def boundedFlatCoefficientSupportedSectionWaldhausen
    (j : U ⟶ space i) [IsOpenImmersion j] :
    Structure (BoundedFlatCoefficientSupportedSections j) :=
  (boundedFlatPerfectSupportedWaldhausen j).ofEquivalence
    (boundedFlatCoefficientSupportedSectionEquivalence j)
    (boundedFlatCoefficientSupportedSectionZero j) (by
      rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedEvaluation_sectionZero_isZero j)

/-- The chosen supported Waldhausen zero retains the original global section. -/
theorem boundedFlatCoefficientSupportedSectionWaldhausen_zero
    (j : U ⟶ space i) [IsOpenImmersion j] :
    (boundedFlatCoefficientSupportedSectionWaldhausen j).zero =
      boundedFlatCoefficientSupportedSectionZero j := rfl

/-- Supported section cofibrations are exactly those of their original evaluation. -/
theorem boundedFlatCoefficientSupportedSectionWaldhausen_cof_iff
    (j : U ⟶ space i) [IsOpenImmersion j]
    {S T : BoundedFlatCoefficientSupportedSections j} (f : S ⟶ T) :
    (boundedFlatCoefficientSupportedSectionWaldhausen j).cof f ↔
      (boundedFlatPerfectSupportedWaldhausen j).cof
        ((boundedFlatCoefficientSupportedEvaluation j).map f) := by
  change (boundedFlatPerfectSupportedWaldhausen j).cof
    ((boundedFlatCoefficientSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]

/-- Supported section weak maps are exactly those of their original evaluation. -/
theorem boundedFlatCoefficientSupportedSectionWaldhausen_weq_iff
    (j : U ⟶ space i) [IsOpenImmersion j]
    {S T : BoundedFlatCoefficientSupportedSections j} (f : S ⟶ T) :
    (boundedFlatCoefficientSupportedSectionWaldhausen j).weq f ↔
      (boundedFlatPerfectSupportedWaldhausen j).weq
        ((boundedFlatCoefficientSupportedEvaluation j).map f) := by
  change (boundedFlatPerfectSupportedWaldhausen j).weq
    ((boundedFlatCoefficientSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedFlatCoefficientSupportedSectionEquivalence_functor]

/-- The actual forward supported evaluation is Waldhausen-exact. -/
theorem boundedFlatCoefficientSupportedEvaluation_exact
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatCoefficientSupportedEvaluation j) := by
  rw [← boundedFlatCoefficientSupportedSectionEquivalence_functor]
  exact Structure.ofEquivalence_exact _ _ _ _

/-- The inverse of the same supported equivalence is Waldhausen-exact. -/
theorem boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
    (j : U ⟶ space i) [IsOpenImmersion j] :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedFlatCoefficientSupportedSectionEquivalence j).inverse :=
  Structure.ofEquivalence_inverse_exact _ _ _ _

section Reindex
variable (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
  (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
include l h

/-- The original joint zero is preserved literally by every supported reindexing. -/
theorem boundedFlatCoefficientSupportedSectionsMap_sectionZero :
    (boundedFlatCoefficientSupportedSectionsMap j j' f l h).obj
        (boundedFlatCoefficientSupportedSectionZero j) =
      boundedFlatCoefficientSupportedSectionZero j' := by
  apply ObjectProperty.FullSubcategory.ext
  exact boundedFlatCoefficientSectionsMap_sectionZero f

section
attribute [local irreducible] boundedFlatCoefficientSupportedSectionsMap
  boundedFlatCoefficientSupportedEvaluation

end

section
attribute [local irreducible] boundedFlatCoefficientSupportedEvaluation
  boundedFlatPerfectSupportedPullback boundedFlatPerfectPullback

end

/-- Supported reindexing detects precisely the weak class of its original geometric pullback. -/
theorem boundedFlatCoefficientSupportedSectionsMap_weq_iff
    {S T : BoundedFlatCoefficientSupportedSections j} (p : S ⟶ T) :
    (boundedFlatCoefficientSupportedSectionWaldhausen j').weq
        ((boundedFlatCoefficientSupportedSectionsMap j j' f l h).map p) ↔
      (boundedFlatPerfectSupportedWaldhausen j').weq
        ((boundedFlatPerfectSupportedPullback
          (boundedFlatCoefficientSupportSquare j j' f l h)).map
            ((boundedFlatCoefficientSupportedEvaluation j).map p)) := by
  rw [boundedFlatCoefficientSupportedSectionWaldhausen_weq_iff]
  let e := Functor.isoWhiskerRight
    (boundedFlatCoefficientSupportedSectionReindexIso j j' f l h)
    (boundedFlatPerfectSupported j').ι
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app S) (e.app T) (e.hom.naturality p).symm)

/-- Supported reindexing followed by the original geometric evaluation is exact. -/
theorem boundedFlatCoefficientSupportedSectionsMap_evaluation_exact :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j').cof (boundedFlatPerfectSupportedWaldhausen j').weq
      (boundedFlatCoefficientSupportedSectionsMap j j' f l h ⋙
        boundedFlatCoefficientSupportedEvaluation j') :=
  ExtensionCategory.isExact_of_natIso
    (boundedFlatCoefficientSupportedSectionWaldhausen j) (boundedFlatPerfectSupportedWaldhausen j')
    ((boundedFlatCoefficientSupportedEvaluation_exact j).comp
      (boundedFlatPerfectSupportedPullback_exact (boundedFlatCoefficientSupportSquare j j' f l h)))
    (boundedFlatCoefficientSupportedSectionReindexIso j j' f l h).symm

/-- Every specified support square gives exact original joint section reindexing. -/
theorem boundedFlatCoefficientSupportedSectionsMap_exact :
    IsExact (boundedFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen j').cof
      (boundedFlatCoefficientSupportedSectionWaldhausen j').weq
      (boundedFlatCoefficientSupportedSectionsMap j j' f l h) where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedFlatCoefficientSupportedEvaluation j') _
    ((boundedFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).zero hx)
  cofibration g hg := (boundedFlatCoefficientSupportedSectionWaldhausen_cof_iff j' _).mpr
    ((boundedFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).cofibration g hg)
  weak g hg := (boundedFlatCoefficientSupportedSectionWaldhausen_weq_iff j' _).mpr
    ((boundedFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).weak g hg)
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatCoefficientSupportedEvaluation j')
    exact (boundedFlatCoefficientSupportedSectionsMap_evaluation_exact j j' f l h).pushout hi hp
end Reindex

/-- Supported section Models retain their original classes and the one global zero. -/
def boundedFlatCoefficientSupportedSectionModel
    (j : U ⟶ space i) [IsOpenImmersion j] : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatCoefficientSupportedSections j),
    boundedFlatCoefficientSupportedSectionWaldhausen j⟩

/-- Original supported reindexing is an exact, literally zero-preserving Model map. -/
def boundedFlatCoefficientSupportedSectionModelMap
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      f) :
    boundedFlatCoefficientSupportedSectionModel j ⟶ boundedFlatCoefficientSupportedSectionModel j'
    where
  functor := boundedFlatCoefficientSupportedSectionsMap j j' f l h
  exact := boundedFlatCoefficientSupportedSectionsMap_exact j j' f l h
  zero := boundedFlatCoefficientSupportedSectionsMap_sectionZero j j' f l h

end Quillen.PerfectComplexes

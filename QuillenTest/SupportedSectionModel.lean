/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionModel

/-!
# Original supported chosen-zero model-map consumers

The literal original coefficient action on sections, arrows and zeros is retained. Composition
uses the actual two open-side maps and their entire composite square. The induced original
prespectrum map retains every level and the independent original structure parameter.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace QuillenTest.SupportedSectionModel

open Quillen
open PerfectComplexes
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The actual model map acts on the original coefficient-reindexed section. -/
theorem original_model_object (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionModelMap j j' f l h).functor.obj s).obj =
      (boundedFlatAffineSectionsMap f).obj s.obj := rfl

/-- The same model map acts by the unchanged original coefficient functor on every section arrow.
-/
theorem original_model_arrow {X Y : BoundedFlatAffineSupportedSections j} (a : X ⟶ Y) :
    ((boundedFlatAffineSupportedSectionModelMap j j' f l h).functor.map a).hom =
      (boundedFlatAffineSectionsMap f).map a.hom := rfl

/-- The model arrow is literally based at the original supported source-independent zero. -/
theorem original_model_zero :
    (boundedFlatAffineSupportedSectionModelMap j j' f l h).functor.obj
        (boundedFlatAffineSupportedSectionZero j) = boundedFlatAffineSupportedSectionZero j' :=
  (boundedFlatAffineSupportedSectionModelMap j j' f l h).zero

/-- Identity retains the original identity coefficient and identity open-side arrow. -/
theorem original_model_identity (hId : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedFlatAffineSupportedSectionModelMap j j (𝟙 R) (𝟙 U) hId =
      𝟙 (boundedFlatAffineSupportedSectionModel j) :=
  boundedFlatAffineSupportedSectionModelMap_id j hId

/-- Composition uses the actual coefficient and open-side composites with their specified square.
-/
theorem original_model_composition (j'' : W ⟶ Spec T) [IsOpenImmersion j'']
    (g : S ⟶ T) (m : W ⟶ V) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedFlatAffineSupportedSectionModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedFlatAffineSupportedSectionModelMap j' j'' g m hg :=
  boundedFlatAffineSupportedSectionModelMap_comp j j' j'' f g l m h hg hfg

/-- The original induced prespectrum arrow commutes with the actual structure path at every time.
-/
theorem original_prespectrum_structure (n : ℕ) (t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).map (n + 1)
        ((prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t) =
      (prespectrum (boundedFlatAffineSupportedSectionModel j')).structureMap n
        ((boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).map n x) t :=
  congrArg (fun p ↦ p t)
    ((boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).comm n x)

end QuillenTest.SupportedSectionModel

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionReindexExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionReindex
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-!
# Original supported section models and coefficient maps

The actual supported section category, its proved Waldhausen structure and original chosen
zero give an iterated-S model. Exact original coefficient reindexing gives literal model maps
for every specified affine open-pair square. Their identity and composition laws retain the
actual coefficient and open-side maps. This construction does not strictify geometric evaluation.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

/-- The original supported sections with their actual chosen-zero Waldhausen structure. -/
def boundedFlatAffineSupportedSectionModel (j : U ⟶ Spec R) [IsOpenImmersion j] : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatAffineSupportedSections j), boundedFlatAffineSupportedSectionWaldhausen j⟩

/-- Original supported coefficient reindexing gives an exact, literally zero-preserving model map.
-/
def boundedFlatAffineSupportedSectionModelMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSupportedSectionModel j ⟶ boundedFlatAffineSupportedSectionModel j' where
  functor := boundedFlatAffineSupportedSectionsMap j j' f l h
  exact := boundedFlatAffineSupportedSectionsMap_exact j j' f l h
  zero := boundedFlatAffineSupportedSectionsMap_sectionZero j j' f l h

/-- Identity uses the same supported section model and original coefficient functor. -/
theorem boundedFlatAffineSupportedSectionModelMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedFlatAffineSupportedSectionModelMap j j (𝟙 R) (𝟙 U) h =
      𝟙 (boundedFlatAffineSupportedSectionModel j) := by
  apply Model.Hom.ext
  exact boundedFlatAffineSupportedSectionsMap_id j h

/-- Composition preserves the entire original specified affine open-pair square. -/
theorem boundedFlatAffineSupportedSectionModelMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedFlatAffineSupportedSectionModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedFlatAffineSupportedSectionModelMap j j' f l hf ≫
        boundedFlatAffineSupportedSectionModelMap j' j'' g m hg := by
  apply Model.Hom.ext
  exact boundedFlatAffineSupportedSectionsMap_comp j j' j'' f g l m hf hg hfg

/-- The original iterated-S map on actual supported sections. -/
def boundedFlatAffineSupportedSectionPrespectrumMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    prespectrum (boundedFlatAffineSupportedSectionModel j) ⟶
      prespectrum (boundedFlatAffineSupportedSectionModel j') :=
  prespectrumMap (boundedFlatAffineSupportedSectionModelMap j j' f l h)

end Quillen.PerfectComplexes

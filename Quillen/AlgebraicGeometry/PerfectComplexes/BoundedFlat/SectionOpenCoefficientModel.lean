/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenReindexExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNull

/-!
# Actual relative-open coefficient Model arrows

The unchanged section reindexing and original chosen section zeros give genuine Model maps
for each specified commuting open-pair square. Identity and composition use the same original
strict section functors. The original fine-to-coarse maps commute literally with reindexing;
no geometric evaluation equality or independently chosen zero identification is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S T : CommRingCat.{u}} {U V W : Scheme.{u}}

/-- The original coefficient reindexing with its actual coarse exactness and section zero. -/
def boundedFlatAffineSectionOpenReindexModelMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSectionOpenModel j ⟶ boundedFlatAffineSectionOpenModel j' where
  functor := boundedFlatAffineSectionsMap f
  exact := boundedFlatAffineSectionsMap_open_exact j j' f l h
  zero := (boundedFlatAffineSectionModelMap f).zero

/-- The identity coefficient map retains the unchanged relative-open section Model. -/
theorem boundedFlatAffineSectionOpenReindexModelMap_id
    (j : U ⟶ Spec R) [IsOpenImmersion j]
    (h : 𝟙 U ≫ j = j ≫ Spec.map (𝟙 R)) :
    boundedFlatAffineSectionOpenReindexModelMap j j (𝟙 R) (𝟙 U) h =
      𝟙 (boundedFlatAffineSectionOpenModel j) := by
  apply Model.Hom.ext
  exact underCocartesianReindex_id boundedFlatAffineProjection R

/-- Composition keeps the specified original coefficient and open maps. -/
theorem boundedFlatAffineSectionOpenReindexModelMap_comp
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) (j'' : W ⟶ Spec T)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion j'']
    (f : R ⟶ S) (g : S ⟶ T) (l : V ⟶ U) (m : W ⟶ V)
    (hf : l ≫ j = j' ≫ Spec.map f) (hg : m ≫ j' = j'' ≫ Spec.map g)
    (hfg : (m ≫ l) ≫ j = j'' ≫ Spec.map (f ≫ g)) :
    boundedFlatAffineSectionOpenReindexModelMap j j'' (f ≫ g) (m ≫ l) hfg =
      boundedFlatAffineSectionOpenReindexModelMap j j' f l hf ≫
        boundedFlatAffineSectionOpenReindexModelMap j' j'' g m hg := by
  apply Model.Hom.ext
  exact underCocartesianReindex_comp boundedFlatAffineProjection f g

/-- The original fine-to-coarse Model maps commute with the unchanged coefficient reindexing. -/
theorem boundedFlatAffineSectionOpenModelMap_naturality
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionOpenModelMap j' =
      boundedFlatAffineSectionOpenModelMap j ≫
        boundedFlatAffineSectionOpenReindexModelMap j j' f l h := by
  apply Model.Hom.ext
  exact (Functor.comp_id _).trans (Functor.id_comp _).symm

/-- The actual relative-open coefficient prespectrum map retains the original Model arrow. -/
def boundedFlatAffineSectionOpenReindexPrespectrumMap
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    prespectrum (boundedFlatAffineSectionOpenModel j) ⟶
      prespectrum (boundedFlatAffineSectionOpenModel j') :=
  prespectrumMap (boundedFlatAffineSectionOpenReindexModelMap j j' f l h)

end Quillen.PerfectComplexes

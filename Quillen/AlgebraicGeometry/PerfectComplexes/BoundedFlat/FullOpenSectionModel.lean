/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionReindex
public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum

/-!
# The actual inherited-zero full-open section Model diagram

Every specified open fiber carries its original full-open section Waldhausen model. Literal
coefficient reindexing is exact and retains the single inherited global zero section, so gives
actual Model maps with genuine identity and composition laws. The resulting prespectrum diagram
retains the original iterated-S maps. A comparison from coarse sections and its Laurent seed
remain separate obligations.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.CategoryTheory.StrictSections
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Original full-open sections with their genuine structure and inherited image zero. -/
def boundedFlatAffineFullOpenSectionModel (a : Under R) : Model.{u+1} :=
  ⟨Cat.of (BoundedFlatAffineFullOpenSections j a),
    boundedFlatAffineFullOpenSectionWaldhausen j a⟩

/-- Every original coefficient arrow gives an exact literally zero-preserving Model map. -/
def boundedFlatAffineFullOpenSectionModelMap {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionModel j a ⟶ boundedFlatAffineFullOpenSectionModel j b where
  functor := boundedFlatAffineFullOpenSectionsMap j f
  exact := boundedFlatAffineFullOpenSectionsMap_exact j f
  zero := boundedFlatAffineFullOpenSectionsMap_sectionZero j f

/-- The specified original identity coefficient gives the actual identity Model map. -/
theorem boundedFlatAffineFullOpenSectionModelMap_id (a : Under R) :
    boundedFlatAffineFullOpenSectionModelMap j (𝟙 a) =
      𝟙 (boundedFlatAffineFullOpenSectionModel j a) := by
  apply Model.Hom.ext
  exact underCocartesianReindex_id (boundedFlatAffineFullOpenProjection j) a

/-- Composition retains the original coslice reindexing maps literally. -/
theorem boundedFlatAffineFullOpenSectionModelMap_comp {a b c : Under R}
    (f : a ⟶ b) (g : b ⟶ c) :
    boundedFlatAffineFullOpenSectionModelMap j (f ≫ g) =
      boundedFlatAffineFullOpenSectionModelMap j f ≫
        boundedFlatAffineFullOpenSectionModelMap j g := by
  apply Model.Hom.ext
  exact underCocartesianReindex_comp (boundedFlatAffineFullOpenProjection j) f g

/-- The actual full-open Model diagram uses the unchanged coefficient functors. -/
def boundedFlatAffineFullOpenSectionModelFunctor : Under R ⥤ Model.{u+1} where
  obj := boundedFlatAffineFullOpenSectionModel j
  map := boundedFlatAffineFullOpenSectionModelMap j
  map_id := boundedFlatAffineFullOpenSectionModelMap_id j
  map_comp := boundedFlatAffineFullOpenSectionModelMap_comp j

/-- Its original iterated-S prespectrum diagram, before any Bass seed or endpoint equivalence. -/
def boundedFlatAffineFullOpenSectionPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedFlatAffineFullOpenSectionModelFunctor j ⋙ prespectrumFunctor

end Quillen.PerfectComplexes

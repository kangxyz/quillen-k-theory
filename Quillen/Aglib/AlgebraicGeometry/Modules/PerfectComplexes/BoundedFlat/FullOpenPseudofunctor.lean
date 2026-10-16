/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Functor
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianSections
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# The original full-open bounded-flat coefficient pseudofunctor

We compose the specified fixed-open coefficient functor with the already coherent original
bounded-flat pullback pseudofunctor. Its cocartesian sections therefore reindex strictly and
retain the actual pullback functors at every coefficient. This owner constructs the full-open
category diagram. Waldhausen structures, inherited image-zero sections and the restriction
comparison from the existing coarse section diagram are separate constructions.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.CategoryTheory.StrictSections AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The full-open pseudofunctor uses the original fixed pullbacks and original geometric maps. -/
def boundedFlatAffineFullOpenPseudofunctor : Pseudofunctor (LocallyDiscrete (Under R)) Cat :=
  (openFunctor j).toPseudofunctor.comp boundedFlatPerfectPseudofunctor

/-- Original full-open coefficient categories, before strict section formation. -/
theorem boundedFlatAffineFullOpenPseudofunctor_obj (a : Under R) :
    (boundedFlatAffineFullOpenPseudofunctor j).obj ⟨a⟩ =
      Cat.of (BoundedFlatPerfect (openSpace j a)) := rfl

/-- The original open pullback is unchanged by pseudofunctor composition. -/
theorem boundedFlatAffineFullOpenPseudofunctor_map {a b : Under R} (f : a ⟶ b) :
    ((boundedFlatAffineFullOpenPseudofunctor j).map f.toLoc).toFunctor =
      boundedFlatPerfectPullback (openMap j f) := rfl

/-- The actual total category of the full-open pullback pseudofunctor. -/
abbrev BoundedFlatAffineFullOpenTotal :=
  Pseudofunctor.Grothendieck (boundedFlatAffineFullOpenPseudofunctor j)

/-- Its original coefficient projection. -/
def boundedFlatAffineFullOpenProjection : BoundedFlatAffineFullOpenTotal j ⥤ Under R :=
  Pseudofunctor.Grothendieck.forget (boundedFlatAffineFullOpenPseudofunctor j)

/-- Full-open sections retain every original fiber object and transition. -/
abbrev BoundedFlatAffineFullOpenSections (a : Under R) :=
  underCocartesian (boundedFlatAffineFullOpenProjection j) a

/-- Original coefficient change is literal restriction of the coslice index. -/
def boundedFlatAffineFullOpenSectionsMap {a b : Under R} (f : a ⟶ b) :
    BoundedFlatAffineFullOpenSections j a ⥤ BoundedFlatAffineFullOpenSections j b :=
  underCocartesianReindex (boundedFlatAffineFullOpenProjection j) f

/-- The actual full-open section categories form a strict coefficient functor. -/
def boundedFlatAffineFullOpenSectionsFunctor : Under R ⥤ Cat where
  obj a := Cat.of (BoundedFlatAffineFullOpenSections j a)
  map f := (boundedFlatAffineFullOpenSectionsMap j f).toCatHom
  map_id a := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_id (boundedFlatAffineFullOpenProjection j) a
  map_comp f g := by
    apply Cat.Hom.ext
    exact underCocartesianReindex_comp (boundedFlatAffineFullOpenProjection j) f g

end Quillen.PerfectComplexes

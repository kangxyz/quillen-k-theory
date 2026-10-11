/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Additive

/-! # Additive single-complex functors into bounded-below complexes

The original single cochain complex in any integer degree is bounded below. Its lift remains
additive, as does the original termwise functor on bounded-below complexes.
-/
@[expose] public section
noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
/-- The original single cochain complex in a specified degree, viewed as bounded below. -/
def singleFunctorPlus (n : ℤ) : C ⥤ Plus C :=
  (CochainComplex.plus C).lift (singleFunctor C n) (fun _ => ⟨n, inferInstance⟩)
instance (n : ℤ) : (singleFunctorPlus C n).Additive where
  map_add {A B f g} := by
    apply ObjectProperty.hom_ext
    exact (singleFunctor C n).map_add (f := f) (g := g)
end CochainComplex
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
/-- The original termwise bounded-below complex functor preserves addition. -/
instance mapCochainComplexPlus_additive (F : C ⥤ D) [F.Additive] :
    F.mapCochainComplexPlus.Additive where
  map_add {A B f g} := by
    apply ObjectProperty.hom_ext
    exact (F.mapHomologicalComplex (.up ℤ)).map_add
end CategoryTheory.Functor

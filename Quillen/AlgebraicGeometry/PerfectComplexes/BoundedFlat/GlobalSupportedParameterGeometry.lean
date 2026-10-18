/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Products.IntegerBase
public import Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic

/-! # The actual integer-base open pair at every scheme parameter -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameter

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original product open immersion, with the parameter as its first factor. -/
def openTransformation :
    baseProductFunctor (toIntegerBase P) ⟶ baseProductFunctor (toIntegerBase Q) :=
  baseProductTransformation _ _ f (toIntegerBase_naturality f)

/-- At a genuine scheme parameter the original open arrow defines an open pair. -/
def pair (S : Scheme.{u}) : Scheme.OpenPairs.{u} :=
  ⟨Arrow.mk ((openTransformation f).app S), by
    change IsOpenImmersion ((baseProductTransformation (toIntegerBase P)
      (toIntegerBase Q) f (toIntegerBase_naturality f)).app S)
    infer_instance⟩

/-- The full commutative square induced by an arbitrary parameter map. -/
def pairMap {S T : Scheme.{u}} (g : S ⟶ T) : pair f S ⟶ pair f T :=
  ObjectProperty.homMk (Arrow.homMk
    ((baseProductFunctor (toIntegerBase P)).map g)
    ((baseProductFunctor (toIntegerBase Q)).map g)
    ((openTransformation f).naturality g))

/-- Actual product pairs form a strict covariant diagram; supported pullback is contravariant. -/
def pairs : Scheme.{u} ⥤ Scheme.OpenPairs.{u} where
  obj := pair f
  map := pairMap f
  map_id S := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact (baseProductFunctor (toIntegerBase P)).map_id S
    · exact (baseProductFunctor (toIntegerBase Q)).map_id S
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext
    · exact (baseProductFunctor (toIntegerBase P)).map_comp g h
    · exact (baseProductFunctor (toIntegerBase Q)).map_comp g h

/-- The ambient side is the unchanged product functor map. -/
theorem pairMap_right {S T : Scheme.{u}} (g : S ⟶ T) :
    (pairMap f g).hom.right = (baseProductFunctor (toIntegerBase Q)).map g := rfl

/-- The open side is the unchanged product functor map. -/
theorem pairMap_left {S T : Scheme.{u}} (g : S ⟶ T) :
    (pairMap f g).hom.left = (baseProductFunctor (toIntegerBase P)).map g := rfl

end Quillen.PerfectComplexes.GlobalSupportedParameter

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.Map.RebasePath

/-!
# Consumers of the original exact-functor rebasing comparison

These checks retain the arbitrary supplied categorical base isomorphism and,
for exact functors, the raw Q-map and its actual canonical zero-isomorphism edge.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

open CategoryTheory CategoryTheory.Limits Quillen
open scoped ZeroObject

universe u v

section
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

example (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d)
    (a : HomotopyGroup.Pi 0 (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpaceIsoBasePath F c d e) 0
      (homotopyGroupMap (classifyingSpaceMap F).hom rfl a) =
        homotopyGroupMap (classifyingSpaceMap (rebaseFunctor F c d e)).hom
          (rebaseFunctor_map_point F c d e) a :=
  pathTransport_rebaseFunctor_homotopyGroupMap F c d e 0 a

example (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) (n : ℕ) :
    pointedShiftedHomotopyGroupMap F c d e n =
      (pathTransportMulEquiv (classifyingSpaceIsoBasePath F c d e) n).toMonoidHom.comp
        (piMap n (classifyingSpaceMap F).hom rfl) :=
  pointedShiftedHomotopyGroupMap_eq_pathTransport F c d e n
end

section
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

example (F : ExactFunctor EC ED) (n : ℕ) :
    F.KMap n = (pathTransportMulEquiv F.qZeroBasePath n).toMonoidHom.comp
      (piMap n (classifyingSpaceMap F.mapQ).hom rfl) := F.KMap_eq_pathTransport n

example (F : ExactFunctor EC ED) (e : F.toFunctor.obj (0 : C) ≅ (0 : D)) :
    F.qZeroBasePath = classifyingSpaceIsoBasePath F.mapQ
      (Q.of EC.deflation EC.inflation (0 : C)) (Q.of ED.deflation ED.inflation (0 : D))
      (ED.qIsoOfIso e) := F.qZeroBasePath_eq_of_zeroIso e
end

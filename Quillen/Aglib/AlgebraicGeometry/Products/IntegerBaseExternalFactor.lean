/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Products.IntegerBaseSwapUnits

/-!
# Moving an external factor past two internal factors

Candidate for `Aglib.AlgebraicGeometry.Products.IntegerBaseExternalFactor`. The current
consumer is the external Laurent track over the double Bass interchange. All maps use
original left-nested pullbacks, and the opposite square retains its reversed direction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}

/-- Move the last factor to the first position without changing the two internal factors. -/
def baseProductMoveExternal (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (r : U ⟶ integerBase) (X : Scheme.{u}) :
    (baseProductFunctor r).obj ((baseProductFunctor q).obj ((baseProductFunctor p).obj X)) ⟶
      (baseProductFunctor q).obj ((baseProductFunctor p).obj ((baseProductFunctor r).obj X)) :=
  baseProductSwapMap q r ((baseProductFunctor p).obj X) ≫
    (baseProductFunctor q).map (baseProductSwapMap p r X)

/-- Internal interchange commutes with moving the distinguished external factor. -/
theorem baseProductMoveExternal_swap (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (r : U ⟶ integerBase) (X : Scheme.{u}) :
    (baseProductFunctor r).map (baseProductSwapMap p q X) ≫
        baseProductMoveExternal q p r X =
      baseProductMoveExternal p q r X ≫
        baseProductSwapMap p q ((baseProductFunctor r).obj X) := by
  simpa only [baseProductMoveExternal, Category.assoc] using baseProductSwapMap_braid p q r X

/-- The same index square in the actual contravariant variance. -/
theorem baseProductMoveExternal_swap_op (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (r : U ⟶ integerBase) (X : Scheme.{u}) :
    (baseProductMoveExternal q p r X).op ≫
        ((baseProductFunctor r).map (baseProductSwapMap p q X)).op =
      (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op ≫
        (baseProductMoveExternal p q r X).op :=
  congrArg Quiver.Hom.op (baseProductMoveExternal_swap p q r X)

/-- The complete external projection is unchanged by the two original swaps. -/
theorem baseProductMoveExternal_projection (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (r : U ⟶ integerBase) (X : Scheme.{u}) :
    baseProductMoveExternal p q r X ≫
        pullback.fst (toIntegerBase ((baseProductFunctor p).obj ((baseProductFunctor r).obj X))) q ≫
          pullback.fst (toIntegerBase ((baseProductFunctor r).obj X)) p ≫
            pullback.snd (toIntegerBase X) r =
      pullback.snd
        (toIntegerBase ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) r := by
  simp [baseProductMoveExternal, baseProductSwapMap, baseProductFunctor, Category.assoc]

end AlgebraicGeometry.Scheme.Products

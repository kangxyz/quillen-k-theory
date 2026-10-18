/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Products.IntegerBaseBraid

/-!
# Actual scalar pullback under independent factor swaps

Candidate for `Aglib.AlgebraicGeometry.Products.IntegerBaseSwapUnits`. Arbitrary fixed maps to
the integral terminal scheme are used, with no compactness assumptions. The two literal
three-swap words retain the left-nested pullback objects. The current consumer is scalar
compatibility of independent Laurent variables in the double Bass construction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}

/-- Pulling a unit back along two actual scheme maps retains their literal composite. -/
theorem unitPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (Γ(Z, ⊤))ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom v) =
      Units.map (f ≫ g).appTop.hom.toMonoidHom v := by
  ext
  simp

/-- The original inner-factor unit becomes the final outer-factor unit under the swap. -/
theorem baseProductSwapMap_unit_first (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : Scheme.{u}) (v : (Γ(S, ⊤))ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (Units.map
        (pullback.snd (toIntegerBase ((baseProductFunctor q).obj X)) p).appTop.hom.toMonoidHom v) =
      Units.map ((pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q) ≫
        pullback.snd (toIntegerBase X) p).appTop.hom.toMonoidHom v := by
  exact (unitPullback_comp _ _ v).trans
    (congrArg (fun k => Units.map k.appTop.hom.toMonoidHom v)
      (baseProductSwapMap_snd p q X))

/-- The original outer-factor unit becomes the inner-factor unit under the swap. -/
theorem baseProductSwapMap_unit_second (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : Scheme.{u}) (v : (Γ(T, ⊤))ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (Units.map
        ((pullback.fst (toIntegerBase ((baseProductFunctor q).obj X)) p) ≫
        pullback.snd (toIntegerBase X) q).appTop.hom.toMonoidHom v) =
      Units.map
        (pullback.snd (toIntegerBase ((baseProductFunctor p).obj X)) q).appTop.hom.toMonoidHom v :=
  by
  exact (unitPullback_comp _ _ v).trans
    (congrArg (fun k => Units.map k.appTop.hom.toMonoidHom v)
      (baseProductSwapMap_fst_snd p q X))

end AlgebraicGeometry.Scheme.Products

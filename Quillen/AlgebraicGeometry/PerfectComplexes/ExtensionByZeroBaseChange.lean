/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ExtensionByZero
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ExtensionByZeroBaseChange

/-! # Original termwise extension-by-zero base change -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)

/-- Actual original open-square restriction comparison in each degree. -/
def openSquareRestrictIso : restrict j ⋙ restrict a ≅ restrict k ⋙ restrict b :=
  NatIso.mapHomologicalComplex (SchemeSheaf.openSquareRestrictIso a b j k h) (.up ℤ)

/-- The literal termwise lift of the genuine sheaf base-change mate. -/
def extensionByZeroBaseChange : restrict a ⋙ extensionByZero b ⟶
    extensionByZero j ⋙ restrict k :=
  NatTrans.mapHomologicalComplex (SchemeSheaf.extensionByZeroBaseChange a b j k h) (.up ℤ)

/-- The original complex base-change isomorphism under the actual cartesian condition. -/
def extensionByZeroBaseChangeIso
    (hc : ∀ v : V, k v ∈ Set.range j → v ∈ Set.range b) :
    restrict a ⋙ extensionByZero b ≅ extensionByZero j ⋙ restrict k :=
  NatIso.mapHomologicalComplex (SchemeSheaf.extensionByZeroBaseChangeIso a b j k h hc) (.up ℤ)

/-- The actual original base-change mate satisfies its chain-level counit identity. -/
@[reassoc]
theorem extensionByZeroBaseChange_counit (M : Complex X) :
    (extensionByZeroBaseChange a b j k h).app ((restrict j).obj M) ≫
      (restrict k).map ((extensionByZeroAdjunction j).counit.app M) =
    (extensionByZero b).map ((openSquareRestrictIso a b j k h).hom.app M) ≫
      (extensionByZeroAdjunction b).counit.app ((restrict k).obj M) := by
  ext n : 1
  exact SchemeSheaf.extensionByZeroBaseChange_counit a b j k h (M.X n)

end Quillen.PerfectComplexes

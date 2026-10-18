/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterGeometry

/-! # Strict original supported Models over all open pairs and scheme parameters -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original ambient global Model on every open pair. -/
def pairAmbient : Scheme.OpenPairs.{u}ᵒᵖ ⥤ Model.{u+1} :=
  (Scheme.openPairProperty.ι ⋙ Arrow.rightFunc).op ⋙ globalModel

/-- Supported original global Models form a strict contravariant open-pair diagram. -/
def pairSupported : Scheme.OpenPairs.{u}ᵒᵖ ⥤ Model.{u+1} where
  obj A := supportedModel (X := op A.unop.obj.right) A.unop.obj.hom
  map g := supportedPairModelMap g.unop
  map_id A := by
    apply Model.Hom.ext
    change (supported (X := op A.unop.obj.right) A.unop.obj.hom).lift
      ((supported (X := op A.unop.obj.right) A.unop.obj.hom).ι ⋙
        (globalModel.map (𝟙 (op A.unop.obj.right))).functor) _ =
      (supported (X := op A.unop.obj.right) A.unop.obj.hom).lift
        (supported (X := op A.unop.obj.right) A.unop.obj.hom).ι _
    apply supported_lift_congr
    exact congrArg (fun F =>
      (supported (X := op A.unop.obj.right) A.unop.obj.hom).ι ⋙ F)
      (congrArg Model.Hom.functor (globalModel.map_id _))
  map_comp {A B C} g h := by
    apply Model.Hom.ext
    change (supported (X := op C.unop.obj.right) C.unop.obj.hom).lift
      ((supported (X := op A.unop.obj.right) A.unop.obj.hom).ι ⋙
        (globalModel.map (g.unop.hom.right.op ≫ h.unop.hom.right.op)).functor) _ =
      (supported (X := op C.unop.obj.right) C.unop.obj.hom).lift
        ((supported (X := op A.unop.obj.right) A.unop.obj.hom).ι ⋙
          (globalModel.map g.unop.hom.right.op).functor ⋙
          (globalModel.map h.unop.hom.right.op).functor) _
    apply supported_lift_congr
    exact congrArg (fun F =>
      (supported (X := op A.unop.obj.right) A.unop.obj.hom).ι ⋙ F)
      (congrArg Model.Hom.functor (globalModel.map_comp _ _))

/-- Forgetting support is a strict transformation of the original Model diagrams. -/
def pairForget : pairSupported.{u} ⟶ pairAmbient where
  app A := supportedForget (X := op A.unop.obj.right) A.unop.obj.hom
  naturality _ _ g := supportedPairModelMap_forget g.unop

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The unchanged global ambient Model on the product with fixed right factor. -/
def ambient (Q : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  (baseProductFunctor (toIntegerBase Q)).op ⋙ globalModel

/-- The actual supported family for all scheme parameters, obtained by strict reindexing. -/
def supported : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  (GlobalSupportedParameter.pairs f).op ⋙ pairSupported

/-- The original support-forgetful map for every scheme parameter. -/
def forget : supported f ⟶ ambient Q :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairForget

end ParameterModels
end Quillen.PerfectComplexes.GlobalSectionChangeIndex

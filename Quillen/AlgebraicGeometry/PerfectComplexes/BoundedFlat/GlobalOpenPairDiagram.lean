/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairDiagram
public import Quillen.Waldhausen.SConstruction.Iterated.InverseImageModelDiagram

/-! # The actual relative-open global Model diagram detected by geometric restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original global Model on the open scheme of every pair. -/
def pairOpenAmbient : Scheme.OpenPairs.{u}ᵒᵖ ⥤ Model.{u+1} :=
  (Scheme.openPairProperty.ι ⋙ Arrow.leftFunc).op ⋙ globalModel

/-- Original scheme restriction is strict on the full open-pair category. -/
def pairRestriction : pairAmbient.{u} ⟶ pairOpenAmbient where
  app A := globalModel.map A.unop.obj.hom.op
  naturality A B g := by
    change globalModel.map g.unop.hom.right.op ≫ globalModel.map B.unop.obj.hom.op =
      globalModel.map A.unop.obj.hom.op ≫ globalModel.map g.unop.hom.left.op
    rw [← globalModel.map_comp, ← globalModel.map_comp]
    exact congrArg globalModel.map (congrArg Quiver.Hom.op (Arrow.w g.unop.hom)).symm

/-- Keep the ambient category, cofibrations and original zero, detecting weakness on the open. -/
def pairOpen : Scheme.OpenPairs.{u}ᵒᵖ ⥤ Model.{u+1} :=
  InverseImageModelDiagram.diagram pairRestriction

/-- The identity on original global sections changes only the weak class. -/
def pairChangeWeak : pairAmbient.{u} ⟶ pairOpen :=
  InverseImageModelDiagram.changeWeak pairRestriction

/-- The original geometric restriction is exact for these detected open weak equivalences. -/
def pairOpenRestriction : pairOpen.{u} ⟶ pairOpenAmbient :=
  InverseImageModelDiagram.restriction pairRestriction

/-- The relative-open factorization is the same original global scheme map. -/
theorem pairOpen_factor : pairChangeWeak.{u} ≫ pairOpenRestriction = pairRestriction :=
  InverseImageModelDiagram.factor pairRestriction

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The relative-open Model on each actual integer-base product pair. -/
def openModel : Scheme.{u}ᵒᵖ ⥤ Model.{u+1} :=
  (GlobalSupportedParameter.pairs f).op ⋙ pairOpen

/-- Change only the original weak class in every parameter. -/
def changeWeak : ambient Q ⟶ openModel f :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairChangeWeak

/-- Restrict the actual relative-open global sections to the genuine open product. -/
def openRestriction : openModel f ⟶ ambient P :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairOpenRestriction

end ParameterModels
end Quillen.PerfectComplexes.GlobalSectionChangeIndex

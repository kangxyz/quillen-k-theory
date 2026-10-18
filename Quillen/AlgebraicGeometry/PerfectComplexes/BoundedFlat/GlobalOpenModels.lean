/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionLaurentAction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenSections
public import Quillen.Waldhausen.SConstruction.Iterated.InverseImageModelDiagram

/-!
# Actual coarse-open global section Models

Only the weak class changes: it is the original relative-open class detected after the actual
coefficient restriction. The complete evaluation square identifies this with restriction of the
original global evaluated complex. The coefficient restriction and change-of-weakness square
are actual strict Model maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel boundedFlatCoefficientSectionWaldhausen
  boundedFlatCoefficientOriginalEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Actual original restriction followed by the existing coarse change of weakness. -/
def openSourceTransformation :
    globalRow Q ⟶ boundedFlatCoefficientOpenModelFunctor f :=
  rowRestriction Q ≫ boundedFlatCoefficientOpenChangeWeakModelTransformation f

/-- Global coarse sections detected by their actual original coefficient restriction. -/
def openRow : Under R ⥤ Model.{u+1} :=
  InverseImageModelDiagram.diagram (openSourceTransformation f)

/-- The coarse global Model at an actual coefficient object. -/
def openModel (a : Under R) : Model.{u+1} := (openRow f).obj a

/-- The detected weak structure retains the original category, cofibrations and zero. -/
def openWaldhausen (a : Under R) : Structure ((globalRow Q).obj a) :=
  Structure.withInverseImageWeak ((openSourceTransformation f).app a).exact

/-- Actual coarse restriction to the existing coefficient Model row. -/
def openRowRestriction : openRow f ⟶ boundedFlatCoefficientOpenModelFunctor f :=
  InverseImageModelDiagram.restriction (openSourceTransformation f)

/-- The actual identity change from global fine to global coarse sections. -/
def openRowChangeWeak : globalRow Q ⟶ openRow f :=
  InverseImageModelDiagram.changeWeak (openSourceTransformation f)

/-- Coarse restriction at a fixed coefficient object. -/
def openRestriction (a : Under R) : openModel f a ⟶ boundedFlatCoefficientOpenModel f a :=
  (openRowRestriction f).app a

/-- The original global identity at a fixed coefficient object. -/
def openChangeWeak (a : Under R) : (globalRow Q).obj a ⟶ openModel f a :=
  (openRowChangeWeak f).app a

/-- The actual change-of-weakness restriction square commutes strictly. -/
theorem openRowRestriction_changeWeak :
    openRowChangeWeak f ≫ openRowRestriction f =
      rowRestriction Q ≫ boundedFlatCoefficientOpenChangeWeakModelTransformation f :=
  InverseImageModelDiagram.factor (openSourceTransformation f)

/-- The component square retains both original zero-preserving arrows. -/
theorem openRestriction_changeWeak (a : Under R) :
    openChangeWeak f a ≫ openRestriction f a =
      (rowRestriction Q).app a ≫ boundedFlatCoefficientOpenChangeWeakModelMap f a :=
  congrArg (fun η => η.app a) (openRowRestriction_changeWeak f)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex

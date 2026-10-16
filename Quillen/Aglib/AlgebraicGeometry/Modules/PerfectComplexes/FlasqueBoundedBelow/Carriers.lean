/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Plus
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Plus
public import Quillen.Aglib.CategoryTheory.Functor.UnderlyingIso

/-!
# Original carrier comparisons for lower-bounded and flasque complexes

Only the redundant proof wrappers are forgotten. All comparisons retain the actual complexes, Godement total and original inclusions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.Godement
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
/-- The original lower-bound proof forgetful functor retains the actual input complexes. -/
def toPlusUnderlyingIso (X : Scheme.{u}) :
    FlasqueCoefficients.toPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅
      (FlasqueBoundedBelow.objects X).ι := Iso.refl _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.Godement
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
/-- Forget only the original Plus proof, before applying a total functor. -/
def modelToPlusEraseIso (X : Scheme.{u}) :
    toPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅ (FlasqueBoundedBelow.objects X).ι := Iso.refl _


end Quillen.PerfectComplexes.ProjectiveLine.FirstEndpoint
end
end

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.Godement
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
/-- The original bounded object with only its original bound proof forgotten to Plus. -/
def boundedToPlus (X : Scheme.{u}) : BoundedBelow.Obj X ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (BoundedBelow.objects X).ι (fun K => K.property.2)

/-- The natural identification of the underlying complex after lifting a bounded-below perfect
object to the Plus category.
-/
def boundedToPlusCarrierIso (X : Scheme.{u}) :
    boundedToPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅ (BoundedBelow.objects X).ι :=
  ObjectProperty.liftCompιIso _ _ _

/-- This uses the generic lift carrier, leaving the entire actual total functor opaque. -/
def totalCarrierIso (X : Scheme.{u}) :
    FlasqueBoundedBelow.total X ⋙ (FlasqueBoundedBelow.objects X).ι ≅
      (BoundedBelow.objects X).ι ⋙ godementTotal X := by
  unfold FlasqueBoundedBelow.total
  exact ObjectProperty.liftCompιIso _ _ _

/-- The natural identification of the underlying complex after forgetting flasqueness. -/
def inclusionCarrierIso (X : Scheme.{u}) :
    FlasqueBoundedBelow.inclusion X ⋙ (BoundedBelow.objects X).ι ≅
      (FlasqueBoundedBelow.objects X).ι := by
  unfold FlasqueBoundedBelow.inclusion
  exact Iso.refl _


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueGammaEndpoints
end
end

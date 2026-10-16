/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Plus
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Exactness

/-!
# Additivity of the actual plus-category functors

The original module functor, flasque proof-forgetting functor and Godement total retain addition of the same underlying chain maps.
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
namespace Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
instance mapPlus_additive {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive] :
    F.mapCochainComplexPlus.Additive := by
  unfold Functor.mapCochainComplexPlus
  infer_instance

instance toPlus_additive (X : Scheme.{u}) : (toPlus X).Additive := by
  unfold toPlus
  infer_instance

instance totalPlus_additive (X : Scheme.{u}) : (godementTotalPlus X).Additive := by
  unfold godementTotalPlus
  infer_instance


end Quillen.PerfectComplexes.ProjectiveLine.SecondEndpoint
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
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint
local instance toPlus_additive (X : Scheme.{u}) : (FlasqueCoefficients.toPlus X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    rfl

local instance totalPlus_additive (X : Scheme.{u}) : (godementTotalPlus X).Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (godementTotal X).map (f.hom + g.hom) =
      (godementTotal X).map f.hom + (godementTotal X).map g.hom
    exact (godementTotal X).map_add

local instance plusMap_additive {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] : F.mapCochainComplexPlus.Additive where
  map_add := by
    intro K L f g
    apply ObjectProperty.hom_ext
    change (F.mapHomologicalComplex (.up ℤ)).map (f.hom + g.hom) =
      (F.mapHomologicalComplex (.up ℤ)).map f.hom +
        (F.mapHomologicalComplex (.up ℤ)).map g.hom
    exact (F.mapHomologicalComplex (.up ℤ)).map_add


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueThirdEndpoint
end
end

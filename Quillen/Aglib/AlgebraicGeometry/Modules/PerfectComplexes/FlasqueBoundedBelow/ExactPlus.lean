/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Plus

/-!
# The inherited flasque exact sequence in the plus category

The original proof-forgetting functor preserves the literal underlying short exact sequence.
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
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
local instance toPlus_additive (X : Scheme.{u}) : (toPlus X).Additive := by
  unfold toPlus
  infer_instance

lemma flasqueSequencePlus_shortExact {X : Scheme.{u}}
    (S : ShortComplex (FlasqueBoundedBelow.Obj X))
    (hS : (CategoryTheory.ExactCategory.ExactSubcategory.exactStructure
      (CategoryTheory.ExactCategory.abelianExactStructure (CochainComplex X.Modules ℤ))
      (FlasqueBoundedBelow.objects X)).conflation S) :
    ((S.map (toPlus X)).map (CochainComplex.Plus.ι X.Modules)).ShortExact := hS


end Quillen.PerfectComplexes.ProjectiveLine.Euler
end
end

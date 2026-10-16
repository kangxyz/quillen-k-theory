/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Exact sheaf functors preserve intrinsic perfection

An additive homology-preserving sheaf functor that preserves the actual local-perfect complex
predicate preserves intrinsic perfect objects in the original D-plus category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance standardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The three original incidence-sequence vertices, in their original order. -/
inductive Vertex
  | first | second | third

/-- Exact sheaf functors that preserve actual local perfection preserve intrinsic perfect D+. -/
lemma perfect_exactDerived {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] [F.PreservesHomology]
    (hF : ∀ K : CochainComplex X.Modules ℤ, locallyPerfect X K →
      locallyPerfect Y ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (K : DerivedCategory.Plus X.Modules)
    (hK : perfectDerivedObjects X (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects Y (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj K)) := by
  let := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let := Localization.essSurj DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
  let P := DerivedCategory.Plus.Q.objPreimage K
  let eP := DerivedCategory.Plus.Q.objObjPreimageIso K
  have hP : locallyPerfect X P.obj :=
    (perfectDerivedObjects_toDerived_iff X P.obj).mp
      ((perfectDerivedObjects X).prop_of_iso (DerivedCategory.Plus.ι.mapIso eP.symm) hK)
  let e : DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj P) ≅
      F.rightDerivedFunctorPlus.obj K :=
    asIso (F.rightDerivedFunctorPlusUnit.app P) ≪≫ F.rightDerivedFunctorPlus.mapIso eP
  exact (perfectDerivedObjects Y).prop_of_iso (DerivedCategory.Plus.ι.mapIso e)
    ((perfectDerivedObjects_toDerived_iff Y _).mpr (hF P.obj hP))


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
end
end

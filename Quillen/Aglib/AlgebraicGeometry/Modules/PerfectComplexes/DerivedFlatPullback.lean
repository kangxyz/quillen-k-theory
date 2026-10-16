/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorByLine
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.BaseChange.Derived.OpenImmersion
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.IsomorphismFunctors
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-!
# Flat pullback and cover descent of intrinsic perfect D-plus objects

Actual derived flat pullback preserves the original perfect predicate, and the stated arbitrary
open-immersion cover detects it without a projective-line hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance nativeProjectionPerfectStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Exact derived flat pullback preserves intrinsic perfection on the original D+ category. -/
theorem perfect_derivedFlatPullbackPlus {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (K : DerivedCategory.Plus Y.Modules)
    (hK : perfectDerivedObjects Y (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects X
      (DerivedCategory.Plus.ι.obj ((derivedFlatPullbackPlus f).obj K)) := by
  let := Localization.essSurj DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso Y.Modules)
  let L : CochainComplex.Plus Y.Modules := DerivedCategory.Plus.Q.objPreimage K
  let eL : DerivedCategory.Plus.Q.obj L ≅ K := DerivedCategory.Plus.Q.objObjPreimageIso K
  have hL : locallyPerfect Y L.obj :=
    (perfectDerivedObjects_toDerived_iff Y L.obj).mp
      ((perfectDerivedObjects Y).prop_of_iso (DerivedCategory.Plus.ι.mapIso eL.symm) hK)
  have := isIso_derivedFlatPullbackPlusUnit f
  exact (perfectDerivedObjects X).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso
      (asIso ((Scheme.Modules.pullback f).rightDerivedFunctorPlusUnit.app L) ≪≫
        (derivedFlatPullbackPlus f).mapIso eL))
    ((perfectDerivedObjects_toDerived_iff X ((AlgebraicGeometry.Scheme.Modules.Complex.pullback
      f).obj L.obj)).mpr
      (locallyPerfect_flatPullback f hL))

/-- An open-immersion cover detects intrinsic perfection through the installed D+ pullbacks. -/
theorem perfectDerivedObjects_of_openImmersionCover
    {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (K : DerivedCategory.Plus X.Modules)
    (hK : ∀ i, perfectDerivedObjects (Y i)
      (DerivedCategory.Plus.ι.obj ((derivedFlatPullbackPlus (j i)).obj K))) :
    perfectDerivedObjects X (DerivedCategory.Plus.ι.obj K) := by
  let := Localization.essSurj DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso X.Modules)
  let L : CochainComplex.Plus X.Modules := DerivedCategory.Plus.Q.objPreimage K
  let eL : DerivedCategory.Plus.Q.obj L ≅ K := DerivedCategory.Plus.Q.objObjPreimageIso K
  have hL : locallyPerfect X L.obj := by
    apply locallyPerfect_of_openImmersionCover Y j hc
    intro i
    have := isIso_derivedFlatPullbackPlusUnit (j i)
    have hp : locallyPerfect (Y i) ((AlgebraicGeometry.Scheme.Modules.Complex.pullback (j i)).obj
      L.obj) :=
      (perfectDerivedObjects_toDerived_iff (Y i) _).mp
        ((perfectDerivedObjects (Y i)).prop_of_iso
          (DerivedCategory.Plus.ι.mapIso
            (asIso ((Scheme.Modules.pullback (j i)).rightDerivedFunctorPlusUnit.app L) ≪≫
              (derivedFlatPullbackPlus (j i)).mapIso eL).symm) (hK i))
    exact locallyPerfect_of_iso ((restrictIsoPullbackComplex (j i)).app L.obj).symm hp
  exact (perfectDerivedObjects X).prop_of_iso (DerivedCategory.Plus.ι.mapIso eL)
    ((perfectDerivedObjects_toDerived_iff X L.obj).mpr hL)


end Quillen.PerfectComplexes.ProjectiveLine
end
end

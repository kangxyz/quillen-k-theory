/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RankOne
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback

/-! The original degree-zero structure single commutes with actual flat pullback.
The comparison is the original single/pullback comparison followed by pullbackUnitIso. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Actual flat pullback of the original rank-one structure single. -/
def rankOnePerfectFlatPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (perfectFlatPullback f).obj (rankOnePerfect Y) ≅ rankOnePerfect X :=
  (locallyPerfect X).isoMk
    (((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pullback f) (.up ℤ) 0).app
        (SheafOfModules.unit Y.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor X.Modules 0).mapIso
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f))

end Quillen.PerfectComplexes

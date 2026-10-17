/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Single
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections

/-!
# Rank-one structure-sheaf perfect complex

The genuine structure sheaf in degree zero is locally perfect, and its actual open restriction is
the same structure single.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : Perfect X) (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The genuine rank-one structure sheaf, as its original degree-zero perfect complex. -/
def rankOnePerfect (X : Scheme.{u}) : Perfect X := by
  let M := SheafOfModules.unit X.ringCatSheaf
  letI : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅ M :=
      coproductUniqueIso _
    exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_of_iso e
  exact ⟨(CochainComplex.singleFunctor X.Modules 0).obj M,
    locallyPerfect_of_strictPerfect (single_strictPerfect_int M 0)⟩

/-- The original open restriction of the structure single is canonically the structure single. -/
def rankOnePerfectRestrictIso : (perfectRestrict j).obj (rankOnePerfect X) ≅ rankOnePerfect U :=
  (locallyPerfect U).isoMk
    (((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor j) (.up ℤ) 0).app
        (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor U.Modules 0).mapIso (Scheme.Modules.restrictUnitIso j))

end Quillen.PerfectComplexes

end

end

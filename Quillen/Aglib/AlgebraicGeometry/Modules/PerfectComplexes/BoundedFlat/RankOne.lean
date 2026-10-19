/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalScalarSingle

/-!
# The original rank-one structure single in bounded-flat perfect complexes

The underlying complex is the existing `rankOnePerfect`. Its strict perfection supplies the
actual bounded-above and stalkwise-flat evidence. The coefficient automorphism is the original
single of structure-module multiplication, and agrees with the existing forward scalar.

Intended upstream owner: `Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.RankOne`.
The hypotheses are an arbitrary scheme and, for the automorphism, an actual global unit.
The current consumer is the first coefficient quotient row and its original Waldhausen K-one class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
namespace Quillen.PerfectComplexes

/-- The unchanged structure-sheaf complex in degree zero with its proved bounded-flat property. -/
def boundedFlatRankOne (X : Scheme.{u}) : BoundedFlatPerfect X := by
  let M := SheafOfModules.unit X.ringCatSheaf
  letI : IsFiniteLocallyFree X M := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅ M :=
      coproductUniqueIso _
    exact finiteLocallyFree_of_iso e
  exact ⟨(rankOnePerfect X).obj, strictPerfect_boundedFlatPerfect (single_strictPerfect_int M 0)⟩

/-- The original inclusion retains exactly the already-defined rank-one perfect complex. -/
theorem boundedFlatRankOne_inclusion (X : Scheme.{u}) :
    (boundedFlatPerfectInclusion X).obj (boundedFlatRankOne X) = rankOnePerfect X := rfl

/-- The genuine degree-zero single of multiplication by the chosen unit. -/
def boundedFlatRankOneUnit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedFlatRankOne X ≅ boundedFlatRankOne X :=
  (boundedFlatPerfect X).isoMk
    ((CochainComplex.singleFunctor X.Modules 0).mapIso (unitMulIso X r))

/-- The degree-zero coefficient automorphism is the original forward scalar on the same object. -/
theorem boundedFlatRankOneUnit_global (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    boundedFlatRankOneUnit X r =
      (boundedFlatPerfectGlobalUnitIso X r).app (boundedFlatRankOne X) := by
  apply Iso.ext
  apply (boundedFlatPerfect X).ι.map_injective
  change _ = (boundedFlatPerfect X).ι.map
    ((boundedFlatPerfectGlobalUnitIso X r).hom.app (boundedFlatRankOne X))
  rw [boundedFlatPerfectGlobalUnitIso_hom_original]
  exact ProjectiveLine.single_unitMul_eq_globalScalar X (r : Γ(X, ⊤))

end Quillen.PerfectComplexes

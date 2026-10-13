/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.HomotopyCategory.BoundedProperty
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.DerivedPushforwardVectorBundle

/-! # Derived direct images of bounded projective-line vector-bundle complexes

The original derived pushforward preserves perfection for complexes with explicit finite
term bounds and finite locally free terms over an arbitrary base ring. This does not
assert a global strict representative for every locally perfect object on the line.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine
/-- The standard derived category of the original module sheaves. -/
local instance boundedProjectivePushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u})

/-- A vector bundle in any single degree has perfect original derived direct image. -/
theorem perfect_derivedPushforward_vectorBundle_single (M : (twoChartLine R).Modules)
    [IsFiniteLocallyFree (twoChartLine R) M] (n : ℤ) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules n).obj M))) := by
  let F := derivedPushforwardPlus (projection R) ⋙ DerivedCategory.Plus.ι
  let e := ((DerivedCategory.Plus.singleFunctors (twoChartLine R).Modules).shiftIso
    (-n) n 0 (by omega)).app M
  let e' := ((F.commShiftIso (-n)).app
    ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)).symm ≪≫
      F.mapIso e
  exact (perfectDerivedObjects (Spec R)).prop_of_iso e'
    ((perfectDerivedObjects (Spec R)).le_shift (-n) _
      (perfect_derivedPushforward_vectorBundle R M))

/-- The original derived direct image of an explicitly bounded vector-bundle complex is perfect. -/
theorem perfect_derivedPushforward_of_bounded_vectorBundle_terms
    (K : CochainComplex.Plus (twoChartLine R).Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hterms : ∀ i, IsFiniteLocallyFree (twoChartLine R) (K.obj.X i)) :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj K))) := by
  let J := derivedPushforwardPlus (projection R) ⋙ DerivedCategory.Plus.ι
  let F := DerivedCategory.Plus.Qh ⋙ J
  have hs (n : ℤ) : perfectDerivedObjects (Spec R)
      (F.obj ((HomotopyCategory.Plus.quotient (twoChartLine R).Modules).obj
        (Quillen.CochainComplex.singlePlus (K.obj.X n) n))) := by
    let := hterms n
    exact (perfectDerivedObjects (Spec R)).prop_of_iso
      (J.mapIso ((DerivedCategory.Plus.quotientCompQhIso (twoChartLine R).Modules).app
        (Quillen.CochainComplex.singlePlus (K.obj.X n) n))).symm
      (perfect_derivedPushforward_vectorBundle_single R (K.obj.X n) n)
  let : (perfectDerivedObjects (Spec R)).ContainsZero :=
    instContainsZeroDerivedPerfectDerivedObjects (Spec R)
  let : (perfectDerivedObjects (Spec R)).IsTriangulatedClosed₂ :=
    instIsTriangulatedClosed₂DerivedPerfectDerivedObjects (Spec R)
  let : (perfectDerivedObjects (Spec R)).IsClosedUnderIsomorphisms :=
    instIsClosedUnderIsomorphismsDerivedPerfectDerivedObjects (Spec R)
  have h := HomotopyCategory.Plus.property_obj_of_term_bounds F
    (perfectDerivedObjects (Spec R)) K a b hl hu hs
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    (J.mapIso ((DerivedCategory.Plus.quotientCompQhIso (twoChartLine R).Modules).app K)) h
end Quillen.PerfectComplexes.ProjectiveLine

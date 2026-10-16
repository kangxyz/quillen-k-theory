/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological

/-!
# The first coordinate of the original tautological inclusion

The literal tautological inclusion followed by the first structure-square projection restricts
to one on the positive chart and to the polynomial coordinate on the negative chart, through
the original displayed line and structure-sheaf trivializations. In particular, its positive
restriction is an isomorphism. No regularity or nontriviality assumption on the ring is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

/-- The original first structure-square coordinate of the genuine tautological inclusion. -/
def tautologicalInclusionFirstProjection (R : CommRingCat.{u}) :
    tautologicalLine R ⟶ SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  tautologicalLineInclusion R ≫ prod.fst

/-- On the positive chart, the first coordinate is one through the original trivializations. -/
theorem tautologicalInclusionFirstProjection_plus (R : CommRingCat.{u}) :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalInclusionFirstProjection R) =
      (tautologicalLinePlusIso R).hom ≫ (Scheme.Modules.restrictUnitIso (plusChart R)).inv := by
  rw [tautologicalInclusionFirstProjection, Functor.map_comp, tautologicalLineInclusion_plus,
    Category.assoc, firstColumn_fst]

/-- On the negative chart, the first coordinate is the literal polynomial scalar. -/
theorem tautologicalInclusionFirstProjection_minus (R : CommRingCat.{u}) :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalInclusionFirstProjection R) =
      (tautologicalLineMinusIso R).hom ≫
        unitMul _ (polynomialCoordinate R) ≫
          (Scheme.Modules.restrictUnitIso (minusChart R)).inv := by
  rw [tautologicalInclusionFirstProjection, Functor.map_comp, tautologicalLineInclusion_minus,
    Category.assoc, secondColumn_fst]

/-- The positive restriction of the original first coordinate is an actual isomorphism. -/
instance tautologicalInclusionFirstProjection_plus_isIso (R : CommRingCat.{u}) :
    IsIso ((Scheme.Modules.restrictFunctor (plusChart R)).map
      (tautologicalInclusionFirstProjection R)) := by
  rw [tautologicalInclusionFirstProjection_plus]
  infer_instance

end AlgebraicGeometry.Scheme.ProjectiveLine

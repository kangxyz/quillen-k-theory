/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.SectionStalk
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Exactness
public import Aglib.AlgebraicGeometry.Modules.Stalk.Exactness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalRestrictedStalkExactness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalBundleTensorTriangle
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.DiagonalTensorTriangle

/-!
# Original sheafified diagonal tensor sequence for arbitrary coefficients

The on-diagonal proof uses source-stalk flatness of the quotient and the actual
pullback/tensor/scalar comparisons. Off the original diagonal, the original
incidence stalk is an isomorphism and the original quotient stalk vanishes.
-/
@[expose] public section

open AlgebraicGeometry

open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry SheafOfModulesOfCommRing
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

/-- At an actual diagonal point, the original tensor sequence is short exact
for an arbitrary coefficient sheaf on the first factor. -/
theorem diagonalBundleTensorSequence_stalk_shortExact_on_diagonal
    (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) (x : twoChartLine R) :
    ((diagonalBundleTensorSequence R E).map
      (moduleStalk (relativeSquare R) (relativeDiagonal R x))).ShortExact := by
  let α := (sectionStalkRingMap (relativeDiagonal R) (relativeFirst R)
    (relativeDiagonal_first R) x).hom
  let S := (diagonalBundleTensorSequence R E).map
    (moduleStalk (relativeSquare R) (relativeDiagonal R x))
  have hS : (S.map (ModuleCat.restrictScalars α)).ShortExact := by
    exact ShortComplex.shortExact_of_iso
      ((diagonalIncidenceSequence R).mapNatIso
        (sectionPullbackTensorStalkIso (relativeDiagonal R) (relativeFirst R)
          (relativeDiagonal_first R) x E)).symm
      (diagonalRestrictedStalkSequence_tensor_shortExact R x
        ((moduleStalk (twoChartLine R) x).obj E))
  exact ModuleCat.shortExact_of_restrictScalars α S hS

/-- Away from the actual diagonal, tensoring retains its split stalk sequence. -/
theorem diagonalBundleTensorSequence_stalk_shortExact_off_diagonal
    (R : CommRingCat.{u}) (E : (twoChartLine R).Modules) (y : relativeSquare R)
    (hy : y ∉ Set.range (relativeDiagonal R)) :
    ((diagonalBundleTensorSequence R E).map (moduleStalk (relativeSquare R) y)).ShortExact := by
  let S := (diagonalIncidenceSequence R).map (moduleStalk (relativeSquare R) y)
  let E' := (Scheme.Modules.pullback (relativeFirst R)).obj E
  let T := tensorLeft ((moduleStalk (relativeSquare R) y).obj E')
  let : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hf : IsIso S.f := diagonalIncidence_moduleStalk_isIso_off_image R y hy
  have hq : IsZero S.X₃ := diagonalQuotientModuleStalk_isZero_off_image R y hy
  have hS : (S.map T).ShortExact :=
    ((ShortComplex.Splitting.ofIsIsoOfIsZero S hf hq).map T).shortExact
  exact ShortComplex.shortExact_of_iso
    ((diagonalIncidenceSequence R).mapNatIso
      (moduleTensorLeftStalkIso (relativeSquare R) y E')).symm hS

/-- The literal original sheafified diagonal tensor sequence is short exact
for every module coefficient sheaf on the original projective line. -/
theorem diagonalBundleTensorSequence_shortExact_all (R : CommRingCat.{u})
    (E : (twoChartLine R).Modules) : (diagonalBundleTensorSequence R E).ShortExact := by
  apply shortExact_of_moduleStalk
  intro y
  by_cases hy : y ∈ Set.range (relativeDiagonal R)
  · obtain ⟨x, rfl⟩ := hy
    exact diagonalBundleTensorSequence_stalk_shortExact_on_diagonal R E x
  · exact diagonalBundleTensorSequence_stalk_shortExact_off_diagonal R E y hy

/-- The original base-coefficient tensor sequence is also short exact for every module sheaf. -/
theorem diagonalTensorSequence_shortExact_all (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    (diagonalTensorSequence R M).ShortExact := by
  let e := (Scheme.Modules.pullbackComp (relativeFirst R) (projection R)).app M
  let C := (Scheme.Modules.pullback (projection R) ⋙
    Scheme.Modules.pullback (relativeFirst R)).obj M
  let : ((tensorFunctor (relativeSquare R).sheaf).obj C).Additive :=
    moduleTensorLeftFunctor_additive (relativeSquare R) C
  let : ((tensorFunctor (relativeSquare R).sheaf).obj
      ((Scheme.Modules.pullback (relativeFirst R ≫ projection R)).obj M)).Additive :=
    moduleTensorLeftFunctor_additive (relativeSquare R) _
  exact ShortComplex.shortExact_of_iso
    ((diagonalIncidenceSequence R).mapNatIso ((tensorFunctor (relativeSquare R).sheaf).mapIso e))
    (diagonalBundleTensorSequence_shortExact_all R ((Scheme.Modules.pullback (projection R)).obj M))

end AlgebraicGeometry.Scheme.ProjectiveLine

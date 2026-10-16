/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Aglib.AlgebraicGeometry.Modules.Pullback.TensorCompatibility
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.OpenBaseChange
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological

/-!
# Native pullback-tensor comparison for the original tautological line

For every scheme morphism into the original two-chart projective line and every module sheaf,
pullback commutes with tensor by the actual tautological line. The forward arrow is the mate of
the original two adjunction units and tensor-pushforward map. Its naturality, unit equation,
section formula, braiding square and cartesian open-restriction square retain the original maps.
The inverse-image chart cover reduces invertibility to the original unit comparison. The other
module sheaf is arbitrary, and the scheme morphism has no flatness hypothesis.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (f : Z ⟶ twoChartLine R)

/-- The original tautological line charts prove invertibility for every other module sheaf. -/
instance tautologicalPullbackTensorMap_isIso (E : (twoChartLine R).Modules) :
    IsIso (modulePullbackTensorMap f E (tautologicalLine R)) := by
  apply modulePullbackTensorMap_isIso_of_trivializingCover_right f
    (fun _ : Bool => Spec (.of (Polynomial R))) (polynomialChart R) (polynomialChart_cover R)
    E (tautologicalLine R)
  intro b
  cases b
  · exact tautologicalLineMinusIso R
  · exact tautologicalLinePlusIso R

/-- The actual pullback-tensor mate with the original tautological line is invertible. -/
def tautologicalPullbackTensorIso (E : (twoChartLine R).Modules) :
    (Scheme.Modules.pullback f).obj
        ((moduleTensorLeftFunctor (twoChartLine R) E).obj (tautologicalLine R)) ≅
      (moduleTensorLeftFunctor Z ((Scheme.Modules.pullback f).obj E)).obj
        ((Scheme.Modules.pullback f).obj (tautologicalLine R)) :=
  asIso (modulePullbackTensorMap f E (tautologicalLine R))

/-- Pullback commutes naturally with the original right tensor by the original tautological line. -/
def tautologicalPullbackTensorNatIso :
    moduleTensorRightFunctor (twoChartLine R) (tautologicalLine R) ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙
        moduleTensorRightFunctor Z ((Scheme.Modules.pullback f).obj (tautologicalLine R)) :=
  NatIso.ofComponents (tautologicalPullbackTensorIso R f)
    (fun g => modulePullbackTensorMap_naturality_left f g (tautologicalLine R))

/-- Every forward component is the specified native adjunction/tensor-pushforward mate. -/
lemma tautologicalPullbackTensorNatIso_hom_app (E : (twoChartLine R).Modules) :
    (tautologicalPullbackTensorNatIso R f).hom.app E =
      modulePullbackTensorMap f E (tautologicalLine R) := rfl

end AlgebraicGeometry.Scheme.ProjectiveLine

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeAction
public import Quillen.KTheory.Bass.GeometricConeInvolution
public import
        Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack

/-!
# Actual global Laurent action and independent loop-time regression

The original global-section scalar realization supplies the track without a
compatibility assumption. The permutation retains its specified inverse and
its full action coordinate, independently of a further original loop time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
open GeometricSeedCospan (coefficient)
open scoped Topology unitInterval
universe u w
namespace QuillenTest.GeometricConeAction
open GeometricConeInterchange NaturalTrack

/-- The original global-section forward Laurent scalar track. -/
def originalTrack : Track laurent.op coefficient
    Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.diagram.{u} where
  homotopy := Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.homotopy
  naturality := Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.homotopy_naturality

/-- The actual original global unit supplies the double-cone equivariance without a new input. -/
example :
    Equivariant
      ((originalTrack.cone (c := coefficient) squareFunctor
        (interchange (laurentProjection (.of (ULift.{u} ℤ))))
        (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))).cone (c := coefficient)
        squareFunctor
          (interchange (laurentProjection (.of (ULift.{u} ℤ))))
          (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))))
      ((originalTrack.cone (c := coefficient) squareFunctor
        (interchange (laurentProjection (.of (ULift.{u} ℤ))))
        (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ))))).cone (c := coefficient)
        squareFunctor
          (interchange (laurentProjection (.of (ULift.{u} ℤ))))
          (squareIso_projection (laurentProjection (.of (ULift.{u} ℤ)))))
      (permutationNatIso
        Quillen.PerfectComplexes.GlobalSchemeLaurentTrack.diagram.{u}).hom :=
  permutation_equivariant (laurentProjection (.of (ULift.{u} ℤ))) originalTrack

variable {U : Scheme.{u}} (q : U ⟶ integerBase)
    {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    (A : Track (baseProductFunctor q).op (NatTrans.op (baseProductProjection q)) F)

/-- The specified inverse, rather than a new chosen map, preserves the same original track. -/
example (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (permutation F X).inv ≫
        (((A.cone (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (c := NatTrans.op (baseProductProjection q))
          squareFunctor (interchange q) (squareIso_projection q)).homotopy X).at r =
      (((A.cone (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q)).homotopy X).at r ≫
          (permutation F ((baseProductFunctor q).op.obj X)).inv := by
  let A₂ := (A.cone (c := NatTrans.op (baseProductProjection q))
    squareFunctor (interchange q) (squareIso_projection q)).cone
      (c := NatTrans.op (baseProductProjection q))
      squareFunctor (interchange q) (squareIso_projection q)
  exact (congrArg (fun k => k ≫ (A₂.homotopy X).at r)
    (permutation_inv_eq_hom F X)).trans
      ((permutation_equivariant q A X r).trans
        (congrArg (fun k => (A₂.homotopy X).at r ≫ k)
          (permutation_inv_eq_hom F ((baseProductFunctor q).op.obj X)).symm))

/-- The original action time and an additional based-loop time remain independent. -/
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (γ : Path (((coneFunctor.obj (coneFunctor.obj F)).obj X).point n)
      (((coneFunctor.obj (coneFunctor.obj F)).obj X).point n)) :
    Path.toContinuousMap
      ((((A.cone (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (c := NatTrans.op (baseProductProjection q))
        squareFunctor (interchange q) (squareIso_projection q)).homotopy X).parameterLooping.level n
          (r, (parameterLoopingMap (permutation F X).hom).map n γ)) t =
      Path.toContinuousMap
        ((parameterLoopingMap (permutation F ((baseProductFunctor q).op.obj X)).hom).map n
          ((((A.cone (c := NatTrans.op (baseProductProjection q)) squareFunctor (interchange q)
        (squareIso_projection q)).cone (c := NatTrans.op (baseProductProjection q))
            squareFunctor (interchange q)
            (squareIso_projection q)).homotopy X).parameterLooping.level n (r, γ))) t :=
  permutation_action_apply q A X n r (γ t)

#print axioms GeometricConeInterchange.externalInverse_eq_inv
#print axioms GeometricConeInterchange.externalTransport_overlap_overlap
#print axioms GeometricConeInterchange.externalInverse_swap_op
#print axioms GeometricConeInterchange.permutation_external_square
#print axioms GeometricConeInterchange.permutation_external_naturality
#print axioms GeometricConeInterchange.doubleCone_action_at
#print axioms GeometricConeInterchange.permutation_equivariant
#print axioms QuillenTest.GeometricConeAction.originalTrack

end QuillenTest.GeometricConeAction

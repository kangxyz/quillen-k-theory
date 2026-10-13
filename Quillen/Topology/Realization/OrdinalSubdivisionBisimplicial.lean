/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Realization.OrdinalSubdivisionRealization
public import Quillen.CategoryTheory.TheoremA.Diagonal
public import Quillen.Topology.HomotopyFiber.SourceEquivalence

/-!
# Subdividing one direction of a bisimplicial set

The two simplicial directions can be subdivided separately. Their endpoint
maps induce homotopy equivalences on actual diagonal realizations. The proof
uses two adjacent composites that are ordinary ordinary twofold endpoint maps and
homotopy-level two-out-of-six, rather than assuming a rowwise realization
invariance theorem.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.OrdinalSubdivision
open Quillen.TheoremA

/-- Subdivision in the outer simplicial direction only. -/
def horizontal (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  δ.op ⋙ X

/-- Subdivision in the inner simplicial direction only. -/
def vertical (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  X ⋙ subdivisionFunctor

/-- Restrict the outer direction to the first half. -/
def horizontalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : horizontal X ⟶ X where
  app p := X.map (first.app p.unop).op
  naturality p q f := by
    change X.map (δ.map f.unop).op ≫ X.map (first.app q.unop).op =
      X.map (first.app p.unop).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg X.map (congrArg Quiver.Hom.op (first.naturality f.unop)).symm

/-- Restrict the inner direction to the first half, naturally in the outer degree. -/
def verticalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : vertical X ⟶ X :=
  Functor.whiskerLeft X endpointNatTrans

/-- The double subdivision diagonal is the ordinary subdivision of the diagonal. -/
def doubleDiagonalIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet (horizontal (vertical X)) ≅ subdivision (diagonalSSet X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Restricting the outer and then inner direction is the ordinary endpoint. -/
theorem horizontalEndpoint_verticalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalMap (horizontalEndpoint (vertical X)) ≫ diagonalMap (verticalEndpoint X) =
      (doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X) := by
  ext p z
  rfl

/-- Restricting the inner and then outer direction gives the same ordinary endpoint. -/
theorem verticalEndpoint_horizontalEndpoint (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint X)) ≫
      diagonalMap (horizontalEndpoint X) =
      (doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X) := by
  ext p z
  exact ConcreteCategory.congr_hom
    ((X.map (first.app p.unop).op).naturality (first.app p.unop).op) z

/-- The global ordinary twofold equivalence in double-diagonal coordinates. -/
def doubleDiagonalHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal (vertical X))| |diagonalSSet X| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (doubleDiagonalIso X))).toHomotopyEquiv.trans
    (realizationHomotopyEquiv (diagonalSSet X))

@[simp] theorem doubleDiagonalHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (doubleDiagonalHomotopyEquiv X).toFun =
      (SSet.toTop.map ((doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X))).hom := by
  rw [Functor.map_comp]
  rfl

/-- Inner-direction subdivision preserves the actual diagonal realization homotopy type. -/
def verticalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (vertical X)| |diagonalSSet X| :=
  HomotopyFiber.ofAdjacentComposites
    (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom
    (SSet.toTop.map (diagonalMap (horizontalEndpoint (vertical X)))).hom
    (SSet.toTop.map
      (diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint (vertical X))))).hom
    (doubleDiagonalHomotopyEquiv X) (doubleDiagonalHomotopyEquiv (vertical X))
    (by rw [doubleDiagonalHomotopyEquiv_toFun, ← horizontalEndpoint_verticalEndpoint,
          Functor.map_comp]; rfl)
    (by rw [doubleDiagonalHomotopyEquiv_toFun, ← verticalEndpoint_horizontalEndpoint,
          Functor.map_comp]; rfl)

@[simp] theorem verticalRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (verticalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom := rfl

/-- Outer-direction subdivision likewise preserves diagonal realization. -/
def horizontalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal X)| |diagonalSSet X| :=
  HomotopyFiber.ofAdjacentComposites
    (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom
    (SSet.toTop.map
      (diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint X)))).hom
    (SSet.toTop.map (diagonalMap (horizontalEndpoint (horizontal (vertical X))))).hom
    (doubleDiagonalHomotopyEquiv X) (doubleDiagonalHomotopyEquiv (horizontal X))
    (by rw [doubleDiagonalHomotopyEquiv_toFun, ← verticalEndpoint_horizontalEndpoint,
          Functor.map_comp]; rfl)
    (by rw [doubleDiagonalHomotopyEquiv_toFun, ← horizontalEndpoint_verticalEndpoint,
          Functor.map_comp]; rfl)

@[simp] theorem horizontalRealizationHomotopyEquiv_toFun
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom := rfl

/-- The first-index restriction retains the outer subdivision and restricts
the inner direction to its first half. -/
def firstIndexRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (δ.op ⋙ X ⋙ subdivisionFunctor)| |diagonalSSet (δ.op ⋙ X)| :=
  verticalRealizationHomotopyEquiv (horizontal X)

@[simp] theorem firstIndexRealizationHomotopyEquiv_toFun
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (firstIndexRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap
        (Functor.whiskerLeft (δ.op ⋙ X) endpointNatTrans))).hom := rfl

end Quillen.OrdinalSubdivision

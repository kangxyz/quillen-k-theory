import Quillen.Topology.Realization.MixedOrdinalBisimplicial

/-! # Canonical realization equivalences of the mixed ordinal cylinder -/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.MixedOrdinalCylinder

private def realizationRetractionEquiv {A B : SSet.{u}} (p : A ⟶ B) (i : B ⟶ A)
    (hi : i ≫ p = 𝟙 B) (H : SSet.Homotopy (p ≫ i) (𝟙 A)) :
    ContinuousMap.HomotopyEquiv |A| |B| where
  toFun := (SSet.toTop.map p).hom
  invFun := (SSet.toTop.map i).hom
  left_inv := by
    have h := realizationSimplicialHomotopy H
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
    exact ⟨h⟩
  right_inv := by
    have hi' := congrArg SSet.toTop.map hi
    rw [Functor.map_comp, CategoryTheory.Functor.map_id] at hi'
    have h : (SSet.toTop.map p).hom.comp (SSet.toTop.map i).hom = ContinuousMap.id |B| :=
      congrArg TopCat.Hom.hom hi'
    exact h ▸ ContinuousMap.Homotopic.refl _

/-- First-copy projection is the forward map of a genuine realized equivalence. -/
def projectionRealizationHomotopyEquiv (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv |cylinder X| |X| :=
  realizationRetractionEquiv (projection X) (zeroSection X) (zeroSection_projection X) (contraction X)

@[simp] theorem projectionRealizationHomotopyEquiv_toFun (X : SSet.{u}) :
    (projectionRealizationHomotopyEquiv X).toFun = (SSet.toTop.map (projection X)).hom := rfl

/-- The outer mixed cylinder has the actual diagonal first-copy projection as
its realization-equivalence map, with the inner degree unchanged. -/
def outerProjectionRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (outerCylinder X)| |TheoremA.diagonalSSet X| :=
  realizationRetractionEquiv (TheoremA.diagonalMap (outerProjection X))
    (TheoremA.diagonalMap (outerZeroSection X))
    (by
      have h := congrArg TheoremA.diagonalFunctor.map (outerZeroSection_projection X)
      rw [Functor.map_comp, CategoryTheory.Functor.map_id] at h
      exact h) (outerContraction X)

@[simp] theorem outerProjectionRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerProjectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerProjection X))).hom := rfl

/-- If a composite with a homotopy equivalence is known, its other factor is
also an equivalence, retaining that actual factor as the forward map. -/
private def cancelProjection {A B C : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (j : C(A, B)) (p : ContinuousMap.HomotopyEquiv B C)
    (e : ContinuousMap.HomotopyEquiv A C) (h : e.toFun = p.toFun.comp j) :
    ContinuousMap.HomotopyEquiv A B :=
  HomotopyFiber.replaceForward (e.trans p.symm) j (by
    have H := p.left_inv.comp (ContinuousMap.Homotopic.refl j)
    change (p.invFun.comp (p.toFun.comp j)).Homotopic j at H
    rw [← h] at H
    exact H.symm)

/-- The one-cut ordinary-subdivision endpoint is itself a realization equivalence. -/
def oneSectionRealizationHomotopyEquiv (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv |OrdinalSubdivision.subdivision X| |cylinder X| :=
  cancelProjection (SSet.toTop.map (oneSection X)).hom (projectionRealizationHomotopyEquiv X)
    (OrdinalSubdivision.realizationHomotopyEquiv X) (by
      change (SSet.toTop.map (OrdinalSubdivision.endpoint X)).hom =
        (SSet.toTop.map (projection X)).hom.comp (SSet.toTop.map (oneSection X)).hom
      have h := congrArg SSet.toTop.map (oneSection_projection X)
      simpa only [Functor.map_comp] using! (congrArg TopCat.Hom.hom h).symm)

@[simp] theorem oneSectionRealizationHomotopyEquiv_toFun (X : SSet.{u}) :
    (oneSectionRealizationHomotopyEquiv X).toFun = (SSet.toTop.map (oneSection X)).hom := rfl

/-- The one-cut outer subdivision inclusion also realizes to an equivalence. -/
def outerOneSectionRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ X)|
      |TheoremA.diagonalSSet (outerCylinder X)| :=
  cancelProjection (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection X))).hom
    (outerProjectionRealizationHomotopyEquiv X) (OrdinalSubdivision.horizontalRealizationHomotopyEquiv X) (by
      change (SSet.toTop.map (TheoremA.diagonalMap (OrdinalSubdivision.horizontalEndpoint X))).hom =
        (SSet.toTop.map (TheoremA.diagonalMap (outerProjection X))).hom.comp
          (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection X))).hom
      have h := congrArg (TheoremA.diagonalFunctor ⋙ SSet.toTop).map (outerOneSection_projection X)
      simpa only [Functor.map_comp] using! (congrArg TopCat.Hom.hom h).symm)

@[simp] theorem outerOneSectionRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerOneSectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection X))).hom := rfl

end Quillen.MixedOrdinalCylinder

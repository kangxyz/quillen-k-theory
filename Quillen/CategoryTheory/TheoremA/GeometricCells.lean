/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremA.SkeletalAttachments
public import Quillen.CategoryTheory.TheoremA.EnrichedBoundaryHEP
public import Quillen.Topology.Homeomorph.SigmaCongr

/-!
# Original geometric coordinates on enriched replacement cells

Taking the actual diagonal and realization commutes with the explicit coproduct.
The existing product and boundary homeomorphisms then give coordinates with the
entire arbitrary topological parameter space, retaining the original boundary maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory Convexity
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremA

/-- The actual diagonal of the explicit bisimplicial coproduct. -/
def diagonalSigmaIso {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet (bisimplicialSigma X) ≅
      Quillen.Realization.simplicialSigma (fun i ↦ diagonalSSet (X i)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

@[reassoc (attr := simp)]
theorem diagonalSigmaIso_inclusion {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) :
    diagonalMap (bisimplicialSigmaι X i) ≫ (diagonalSigmaIso X).hom =
      Quillen.Realization.simplicialSigmaι (fun i ↦ diagonalSSet (X i)) i := rfl

/-- The realized diagonal of the displayed coproduct is its categorical coproduct. -/
def realizedDiagonalSigmaIsColimit {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsColimit (Cofan.mk |diagonalSSet (bisimplicialSigma X)|
      (fun i ↦ SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)))) :=
  isColimitCofanMkObjOfIsColimit (diagonalFunctor ⋙ SSet.toTop) X
    (bisimplicialSigmaι X) (bisimplicialSigmaIsColimit X)

/-- The realized diagonal coproduct has its original topological sigma coordinates. -/
def realizedDiagonalSigmaIso {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    |diagonalSSet (bisimplicialSigma X)| ≅ TopCat.of (Σ i, |diagonalSSet (X i)|) :=
  SSet.toTop.mapIso (diagonalSigmaIso X) ≪≫
    Quillen.Realization.realizationSigmaIso (fun i ↦ diagonalSSet (X i))

@[reassoc (attr := simp)]
theorem realizedDiagonalSigmaIso_inclusion {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) :
    SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) ≫
      (realizedDiagonalSigmaIso X).hom =
        TopCat.sigmaι (fun i ↦ |diagonalSSet (X i)|) i := by
  rw [realizedDiagonalSigmaIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, ← Functor.map_comp, diagonalSigmaIso_inclusion,
    Quillen.Realization.realizationSigmaIso_ι]

@[simp]
theorem realizedDiagonalSigmaIso_inclusion_apply {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) (x : |diagonalSSet (X i)|) :
    (realizedDiagonalSigmaIso X).hom
      (SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) x) = ⟨i, x⟩ :=
  ConcreteCategory.congr_hom (realizedDiagonalSigmaIso_inclusion X i) x

@[simp]
theorem realizedDiagonalSigmaIso_inv_apply {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) (x : |diagonalSSet (X i)|) :
    (realizedDiagonalSigmaIso X).inv ⟨i, x⟩ =
      SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) x := by
  rw [← realizedDiagonalSigmaIso_inclusion_apply X i x]
  exact ConcreteCategory.congr_hom (realizedDiagonalSigmaIso X).hom_inv_id _

/-- Geometric coordinates on an individual actual enriched simplex. -/
def realizedEnrichedCellHomeomorph (X : SSet.{u}) (n : ℕ) :
    |diagonalSSet (outerProduct (Δ[n] : SSet.{u}) X)| ≃ₜ
      |X| × StdSimplex ℝ (Fin (n + 1)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (diagonalOuterProductIso Δ[n] X))).trans
    (realizationProductSimplexParameterHomeomorph X n)

/-- Geometric coordinates on an individual actual enriched boundary. -/
def realizedEnrichedBoundaryHomeomorph (X : SSet.{u}) (n : ℕ) :
    |diagonalSSet (outerProduct (∂Δ[n] : SSet.{u}) X)| ≃ₜ |X| × simplexBoundary n :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) X))).trans
    (realizationProductBoundaryHomeomorph X n)

/-- The individual coordinate homeomorphisms preserve the original enriched boundary inclusion. -/
theorem realizedEnrichedBoundary_square (X : SSet.{u}) (n : ℕ) :
    SSet.toTop.map (diagonalMap (outerProductMap (X := X) ∂Δ[n].ι)) ≫
        (TopCat.isoOfHomeo (realizedEnrichedCellHomeomorph X n)).hom =
      (TopCat.isoOfHomeo (realizedEnrichedBoundaryHomeomorph X n)).hom ≫
        Quillen.parameterizedSimplexBoundaryInclusion |X| n := by
  change SSet.toTop.map (diagonalMap (outerProductMap (X := X) ∂Δ[n].ι)) ≫
      (SSet.toTop.map (diagonalOuterProductIso Δ[n] X).hom ≫
        (TopCat.isoOfHomeo (realizationProductSimplexParameterHomeomorph X n)).hom) =
    (SSet.toTop.map (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) X).hom ≫
      (TopCat.isoOfHomeo (realizationProductBoundaryHomeomorph X n)).hom) ≫
      Quillen.parameterizedSimplexBoundaryInclusion |X| n
  rw [← Category.assoc, ← Functor.map_comp, diagonalOuterProductIso_naturality,
    Functor.map_comp, Category.assoc, realizationProductBoundary_square, Category.assoc]

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The arbitrary topological parameter space of all enriched cells in one base dimension. -/
def replacementCellParameters (n : ℕ) : TopCat.{u} :=
  TopCat.of (Σ s : (nerve D).nonDegenerate n, |H.obj (s.val.obj 0)|)

/-- The actual family of realized enriched cells, in parameterized simplex coordinates. -/
def realizedReplacementCellsHomeomorph (n : ℕ) :
    |diagonalSSet (replacementCells H n)| ≃ₜ
      replacementCellParameters H n × StdSimplex ℝ (Fin (n + 1)) :=
  ((TopCat.homeoOfIso (realizedDiagonalSigmaIso
    (fun s : (nerve D).nonDegenerate n ↦ replacementCell H s))).trans
      (Homeomorph.sigmaCongrRight fun s ↦
        realizedEnrichedCellHomeomorph (H.obj (s.val.obj 0)) n)).trans
    Homeomorph.sigmaProdDistrib.symm

/-- The actual family of realized enriched boundaries, in parameterized boundary coordinates. -/
def realizedReplacementBoundariesHomeomorph (n : ℕ) :
    |diagonalSSet (replacementCellBoundaries H n)| ≃ₜ
      replacementCellParameters H n × simplexBoundary n :=
  ((TopCat.homeoOfIso (realizedDiagonalSigmaIso
    (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundary H s))).trans
      (Homeomorph.sigmaCongrRight fun s ↦
        realizedEnrichedBoundaryHomeomorph (H.obj (s.val.obj 0)) n)).trans
    Homeomorph.sigmaProdDistrib.symm

/-- Cell-family coordinates retain the original summand characteristic map. -/
@[simp]
theorem realizedReplacementCellsHomeomorph_inclusion (n : ℕ)
    (s : (nerve D).nonDegenerate n) (x : |diagonalSSet (replacementCell H s)|) :
    realizedReplacementCellsHomeomorph H n
      (SSet.toTop.map (diagonalMap
        (bisimplicialSigmaι (fun s ↦ replacementCell H s) s)) x) =
      (⟨s, (realizedEnrichedCellHomeomorph (H.obj (s.val.obj 0)) n x).1⟩,
        (realizedEnrichedCellHomeomorph (H.obj (s.val.obj 0)) n x).2) := by
  change Homeomorph.sigmaProdDistrib.symm
    ((Homeomorph.sigmaCongrRight fun s ↦
      realizedEnrichedCellHomeomorph (H.obj (s.val.obj 0)) n)
        ((realizedDiagonalSigmaIso (fun s ↦ replacementCell H s)).hom _)) = _
  rw [realizedDiagonalSigmaIso_inclusion_apply]
  rfl

/-- Boundary-family coordinates retain the original summand characteristic map. -/
@[simp]
theorem realizedReplacementBoundariesHomeomorph_inclusion (n : ℕ)
    (s : (nerve D).nonDegenerate n) (x : |diagonalSSet (replacementCellBoundary H s)|) :
    realizedReplacementBoundariesHomeomorph H n
      (SSet.toTop.map (diagonalMap
        (bisimplicialSigmaι (fun s ↦ replacementCellBoundary H s) s)) x) =
      (⟨s, (realizedEnrichedBoundaryHomeomorph (H.obj (s.val.obj 0)) n x).1⟩,
        (realizedEnrichedBoundaryHomeomorph (H.obj (s.val.obj 0)) n x).2) := by
  change Homeomorph.sigmaProdDistrib.symm
    ((Homeomorph.sigmaCongrRight fun s ↦
      realizedEnrichedBoundaryHomeomorph (H.obj (s.val.obj 0)) n)
        ((realizedDiagonalSigmaIso (fun s ↦ replacementCellBoundary H s)).hom _)) = _
  rw [realizedDiagonalSigmaIso_inclusion_apply]
  rfl

end Quillen.TheoremA

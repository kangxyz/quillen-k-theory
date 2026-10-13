/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.SkeletalCartesianBoundary
public import Quillen.CategoryTheory.TheoremB.SkeletalCartesianStageCube
public import Quillen.Topology.Realization.Cartesian.CoproductAssembly

/-! # Actual replacement-stage cartesian cube assembly -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.CartesianRealization.Skeletal
open TheoremA TheoremB

/-- The unique simplex in each degree of the zero-simplex, used to identify point-valued
replacement stages with their base stages. -/
local instance pointSimplexUniqueAssembly (p : SimplexCategoryᵒᵖ) :
    Unique ((Δ[0] : SSet.{u}).obj p) :=
  (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := p)).unique

/-- The point coefficient leaves exactly the prescribed simplicial domain. -/
def pointOuterIso (K : SSet.{u}) :
    diagonalSSet (outerProduct K (Δ[0] : SSet.{u})) ≅ K :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ x.1
      invFun := fun a ↦ ⟨a, (default : (Δ[0] : SSet.{u}).obj p)⟩
      left_inv := fun x ↦ by
        rcases x with ⟨i, x⟩
        exact congrArg (Sigma.mk i)
          (@Subsingleton.elim ((Δ[0] : SSet.{u}).obj p) inferInstance _ _)
      right_inv := fun _ ↦ rfl }) (by intros; rfl)

/-- The homeomorphism from the realization of the diagonal outer product of `K` with the
zero-simplex to the realization of `K`. -/
abbrev pointOuterHomeomorph (K : SSet.{u}) :
    |diagonalSSet (outerProduct K (Δ[0] : SSet.{u}))| ≃ₜ |K| :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (pointOuterIso K))

/-- Realization of an actual bisimplicial coproduct, with its actual injections. -/
abbrev realizedCofan {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Cofan (fun i ↦ realizationFunctor.obj (X i)) :=
  Cofan.mk (realizationFunctor.obj (bisimplicialSigma X))
    (fun i ↦ realizationFunctor.map (bisimplicialSigmaι X i))

/-- Realization preserves the exact componentwise square of an outer product. -/
theorem pointOuter_square {K L X : SSet.{u}} (k : K ⟶ L)
    (f : X ⟶ (Δ[0] : SSet.{u})) :
    realizationFunctor.map (outerProductMap (X := X) k) ≫
      realizationFunctor.map (outerProductCoefficientMap f) =
    realizationFunctor.map (outerProductCoefficientMap f) ≫
      realizationFunctor.map (outerProductMap (X := (Δ[0] : SSet.{u})) k) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Boundary product squares are cartesian for every coefficient, even when
its augmentation to a point is not an equivalence. -/
theorem pointOuter_cartesian {K L X : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (f : X ⟶ (Δ[0] : SSet.{u})) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap (K := K) f)).hom
      (realizationFunctor.map (outerProductCoefficientMap (K := L) f)).hom
      (realizationFunctor.map (outerProductMap (X := X) k)).hom
      (realizationFunctor.map (outerProductMap (X := (Δ[0] : SSet.{u})) k)).hom
      (congrArg TopCat.Hom.hom (pointOuter_square k f)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (SSet.toTop.map (outerProjection K X)).hom
    (SSet.toTop.map (outerProjection L X)).hom
    (SSet.toTop.map (enrichedMap k (𝟙 X))).hom (SSet.toTop.map k).hom
    (congrArg TopCat.Hom.hom (realizedEnrichedMap_square k (𝟙 X)))
    (Homeomorph.refl _) (Homeomorph.refl _)
    (pointOuterHomeomorph K) (pointOuterHomeomorph L)
  · change (SSet.toTop.map (outerProjection K X)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap f)) ≫
        SSet.toTop.map (pointOuterIso K).hom).hom
    rw [← Functor.map_comp]
    rfl
  · change (SSet.toTop.map (outerProjection L X)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap f)) ≫
        SSet.toTop.map (pointOuterIso L).hom).hom
    rw [← Functor.map_comp]
    rfl
  · rfl
  · change (SSet.toTop.map (pointOuterIso K).hom ≫ SSet.toTop.map k).hom =
      (SSet.toTop.map (diagonalMap (outerProductMap k)) ≫ SSet.toTop.map (pointOuterIso L).hom).hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · exact enrichedMap_cartesian k (𝟙 X) (Homeomorph.refl |X|).toHomotopyEquiv
      (by rw [CategoryTheory.Functor.map_id]; rfl)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The incoming boundary-to-cell face of the actual successor cube. -/
theorem replacementBoundary_cartesian (n : ℕ) :
    Cartesian (cellBoundaryProjection (replacementPointAugmentation H) n).hom
      (cellProjection (replacementPointAugmentation H) n).hom
      (boundaryLeg H n).hom (boundaryLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare (replacementPointAugmentation H) n)) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  apply cartesianCofan
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary
      pointDiagram s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell pointDiagram s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCell H))
    (realizedCofan (replacementCellBoundary pointDiagram)) (realizedCofan (replacementCell
      pointDiagram))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (cellBoundaryProjection (replacementPointAugmentation H) n)
    (cellProjection (replacementPointAugmentation H) n)
    (boundaryLeg H n) (boundaryLeg pointDiagram n)
    (cellBoundarySquare (replacementPointAugmentation H) n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (replacementCellBoundaryι H s))
    (fun s ↦ realizationFunctor.map (replacementCellBoundaryι pointDiagram s))
    (fun s ↦ pointOuter_square ∂Δ[n].ι ((replacementPointAugmentation H).app (s.1.obj 0)))
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    exact pointOuter_cartesian ∂Δ[n].ι ((replacementPointAugmentation H).app (s.1.obj 0))


/-- The exact component square before assembling the attaching coproduct. -/
theorem componentAttaching_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (replacementCellAttaching H s) ≫
      stageProjection (replacementPointAugmentation H) n =
    realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))) ≫
      realizationFunctor.map (replacementCellAttaching pointDiagram s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg realizationFunctor.map
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app ((replacementPointAugmentation H).naturality
      (firstVertexEdge x.1.1.down.op s.1)) q) x.2

/-- Finite boundary-chart descent supplies each incoming component square
in the original point-replacement coordinates. -/
theorem componentAttaching_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv)
    (s : (nerve D).nonDegenerate n) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
      (stageProjection (replacementPointAugmentation H) n).hom
      (realizationFunctor.map (replacementCellAttaching H s)).hom
      (realizationFunctor.map (replacementCellAttaching pointDiagram s)).hom
      (congrArg TopCat.Hom.hom (componentAttaching_square H s)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (domainProjection (H.obj (s.1.obj 0)) (∂Δ[n] : SSet.{u})).hom
    (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n))).hom
    (realizationFunctor.map (replacementCellAttaching H s)).hom
    (SSet.toTop.map (boundaryBaseMap s)).hom _
    (Homeomorph.refl _) (Homeomorph.refl _)
    (pointOuterHomeomorph (∂Δ[n] : SSet.{u}))
    (pointRestrictionHomeomorph ((nerve D).skeleton n))
  · change (SSet.toTop.map (outerProjection _ _)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap _)) ≫
        SSet.toTop.map (pointOuterIso _).hom).hom
    rw [← Functor.map_comp]
    rfl
  · exact congrArg TopCat.Hom.hom (pointRestrictionIso_projectionTower H n).symm
  · rfl
  · change (SSet.toTop.map (pointOuterIso _).hom ≫ SSet.toTop.map (boundaryBaseMap s)).hom =
      (SSet.toTop.map (diagonalMap (replacementCellAttaching pointDiagram s)) ≫
        SSet.toTop.map (pointRestrictionIso _).hom).hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · exact replacementCellAttaching_cartesian H htrans n hchart s

/-- The entire incoming attaching face follows from the proved finite
boundary comparisons and the universal property of the actual coproduct. -/
theorem replacementAttaching_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    Cartesian (cellBoundaryProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) n).hom
      (attachingLeg H n).hom (attachingLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellAttachingSquare (replacementPointAugmentation H) n)) := by
  apply cartesianCofanFixedTarget
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary
      pointDiagram s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCellBoundary
      pointDiagram))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (stageProjection (replacementPointAugmentation H) n)
    (cellBoundaryProjection (replacementPointAugmentation H) n)
    (attachingLeg H n) (attachingLeg pointDiagram n)
    (cellAttachingSquare (replacementPointAugmentation H) n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching H s))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching pointDiagram s))
    (fun s ↦ componentAttaching_square H s)
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← Functor.map_comp]
    rfl
  · exact componentAttaching_cartesian H htrans n hchart


/-- Both outgoing faces of the genuine successor cube, with both incoming
faces derived from product geometry and finite boundary-chart assembly. -/
theorem replacementSuccessor_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    Cartesian (stageProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n+1)).hom
      (stageStep H n).hom (stageStep pointDiagram n).hom
      (congrArg TopCat.Hom.hom (stageStepSquare (replacementPointAugmentation H) n)) ∧
    Cartesian (cellProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare (replacementPointAugmentation H) n)) :=
  successor_cartesian_of_incoming (replacementPointAugmentation H) n
    (replacementBoundary_cartesian H n) (replacementAttaching_cartesian H htrans n hchart)

end Quillen.CartesianRealization.Skeletal

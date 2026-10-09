import Quillen.CategoryTheory.TheoremB.SkeletalCartesianDomains
import Quillen.CategoryTheory.TheoremA.SkeletalCofibrations
import Quillen.CategoryTheory.TheoremA.SkeletalNaturality

/-! Simultaneous homotopy-cartesian induction in the actual replacement
skeleton tower. The finite cube is applied only after both incoming
boundary comparisons have been proved. -/
noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB.SkeletalCartesian
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

abbrev realizationFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ TopCat.{u} :=
  diagonalFunctor ⋙ SSet.toTop
abbrev cellProjection (n : ℕ) := realizationFunctor.map (replacementCellsMap η n)
abbrev cellBoundaryProjection (n : ℕ) := realizationFunctor.map (replacementCellBoundariesMap η n)
abbrev stageProjection (n : ℕ) := (realizedReplacementSkeletonMap η).app n
abbrev boundaryLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsBoundaryι H n)
abbrev attachingLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsAttaching H n)
abbrev characteristicLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsCharacteristic H n)
abbrev stageStep (H : D ⥤ SSet.{u}) (n : ℕ) :=
  (realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))

theorem cellBoundarySquare (n : ℕ) :
    boundaryLeg H n ≫ cellProjection η n = cellBoundaryProjection η n ≫ boundaryLeg J n := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp, replacementCellsMap_boundary]

theorem cellAttachingSquare (n : ℕ) :
    attachingLeg H n ≫ stageProjection η n = cellBoundaryProjection η n ≫ attachingLeg J n := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp, replacementCellsMap_attaching]

theorem cellCharacteristicSquare (n : ℕ) :
    characteristicLeg H n ≫ stageProjection η (n+1) = cellProjection η n ≫ characteristicLeg J n := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp, replacementCellsMap_characteristic]

theorem stageStepSquare (n : ℕ) :
    stageStep H n ≫ stageProjection η (n+1) = stageProjection η n ≫ stageStep J n :=
  (realizedReplacementSkeletonMap η).naturality (homOfLE (Nat.le_succ n))

/-- The genuine finite cube gives both outgoing stage/cell comparisons,
without hiding either of the two incoming comparison obligations. -/
theorem successor_cartesian_of_incoming (n : ℕ)
    (hboundary : Cartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom (congrArg TopCat.Hom.hom (cellBoundarySquare η n)))
    (hattaching : Cartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom (congrArg TopCat.Hom.hom (cellAttachingSquare η n))) :
    Cartesian (stageProjection η n).hom (stageProjection η (n+1)).hom
      (stageStep H n).hom (stageStep J n).hom (congrArg TopCat.Hom.hom (stageStepSquare η n)) ∧
    Cartesian (cellProjection η n).hom (stageProjection η (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)) := by
  let sq := (realizedReplacementSkeleton_isPushout H n).flip
  let sq' := (realizedReplacementSkeleton_isPushout J n).flip
  have hi := homotopyExtensionProperty_replacementCellsBoundary H n
  have hi' := homotopyExtensionProperty_replacementCellsBoundary J n
  refine ⟨?_,?_⟩
  · exact ⟨CartesianPushout.rightHomotopyEquiv sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi'
      hboundary.equiv hboundary.equiv_toFun hattaching.equiv hattaching.equiv_toFun,
      CartesianPushout.rightHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact ⟨CartesianPushout.leftHomotopyEquiv sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi'
      hboundary.equiv hboundary.equiv_toFun hattaching.equiv hattaching.equiv_toFun,
      CartesianPushout.leftHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

end Quillen.TheoremB.SkeletalCartesian

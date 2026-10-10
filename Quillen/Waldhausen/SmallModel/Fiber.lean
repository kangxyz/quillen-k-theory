/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.SmallModel.Acyclic
import Quillen.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
import Quillen.Topology.Realization.HomotopyNaturality
import Quillen.Topology.HomotopyFiber.Homeomorph
import Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation
import Quillen.CategoryTheory.TheoremB.VertexWeakAssembly

/-!
# Exact transport of the original canonical fiber comparison

The common-universe model preserves the actual change-of-weak arrow, the
actual acyclic subcategory, and every point of the reversed zero-to-inclusion
nullhomotopy. Weakness therefore transports for the original canonical map.
-/
noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {W : Structure C} (N : NestedWeakEquivalences W)

/-- The original and lifted acyclic cylinders commute strictly, before realization. -/
theorem acyclicSmallCylinder_square :
    (acyclicSmallSSetIso N).hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure N.smallModel) N.smallModel.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.smallModel)
        (zeroToAcyclicInclusion N.smallModel) (zeroToAcyclicInclusion_weak N.smallModel) =
    weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) ≫
        N.coarse.smallModelSSetIso.hom := by
  ext n z : 4
  apply Subtype.ext
  change nerveCylinderDiagram
    (Functor.whiskerLeft (z.1.val ⋙ acyclicSmallUp N) (zeroToAcyclicInclusion N.smallModel)) z.2.down =
      nerveCylinderDiagram (Functor.whiskerLeft z.1.val (zeroToAcyclicInclusion N)) z.2.down ⋙
        (AsSmall.up : C ⥤ SmallModel C)
  rw [nerveCylinderDiagram_postcomp]
  apply nerveCylinderDiagram_congr_app _ _ rfl rfl
  intro p
  exact heq_of_eq (N.smallModel.coarse.isZero.eq_of_src _ _)

/-- Every point of the original reversed acyclic nullhomotopy is preserved. -/
theorem acyclicSmallNullhomotopy (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    N.coarse.smallModelDeloopingHomeomorph (acyclicNullhomotopy N (t,x)) =
      acyclicNullhomotopy N.smallModel (t, acyclicSmallDeloopingHomeomorph N x) := by
  have hs : (acyclicSmallSSetIso N).hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure N.smallModel) N.smallModel.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.smallModel)
        (zeroToAcyclicInclusion N.smallModel) (zeroToAcyclicInclusion_weak N.smallModel) ≫
      N.coarse.smallModelSSetIso.inv =
      weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) := by
    rw [← Category.assoc, acyclicSmallCylinder_square, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy (acyclicStructure N.smallModel) N.smallModel.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.smallModel)
      (zeroToAcyclicInclusion N.smallModel) (zeroToAcyclicInclusion_weak N.smallModel))
    (weakNaturalTransformationHomotopy (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (acyclicSmallSSetIso N).hom N.coarse.smallModelSSetIso.inv hs (unitInterval.symm t) x
  apply N.coarse.smallModelDeloopingHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact hh.symm

/-- The original change-of-weak map commutes with both actual realization homeomorphisms. -/
theorem smallModel_changeWeak_square :
    N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun.comp (changeWeakMap N) =
      (changeWeakMap N.smallModel).comp W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  change (SSet.toTop.map (sSetMap (changeWeak_exact N)) ≫
      SSet.toTop.map N.coarse.smallModelSSetIso.hom).hom =
    (SSet.toTop.map W.smallModelSSetIso.hom ≫
      SSet.toTop.map (sSetMap (changeWeak_exact N.smallModel))).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, smallModelSSetIso_changeWeak]

/-- The homeomorphism of actual original fibers retains the source and entire path. -/
def smallModelChangeWeakFiberHomeomorph :
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint ≃ₜ
      HomotopyFiber (changeWeakMap N.smallModel) N.smallModel.coarse.kBasepoint :=
  (HomotopyFiber.homeomorphOfSquare (changeWeakMap N) (changeWeakMap N.smallModel)
    W.smallModelDeloopingHomeomorph N.coarse.smallModelDeloopingHomeomorph
    (smallModel_changeWeak_square N) N.coarse.kBasepoint).trans
      (HomotopyFiber.congrHomeomorph rfl N.coarse.smallModelDeloopingHomeomorph_basepoint)

@[simp] theorem smallModelChangeWeakFiberHomeomorph_source
    (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (smallModelChangeWeakFiberHomeomorph N z).val.1 = W.smallModelDeloopingHomeomorph z.val.1 := rfl

@[simp] theorem smallModelChangeWeakFiberHomeomorph_path
    (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (smallModelChangeWeakFiberHomeomorph N z).val.2 =
      N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun.comp z.val.2 := rfl

/-- The exact original canonical comparison square, including its full stored path. -/
theorem smallModel_canonicalFiberMap_square :
    (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun.comp (canonicalFiberMap N) =
      (canonicalFiberMap N.smallModel).comp (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have hs := congrArg (fun f ↦ (SSet.toTop.map f).hom) (acyclicSmallSSetIso_inclusion N)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hs
    exact ContinuousMap.congr_fun hs x
  · apply ContinuousMap.ext
    intro t
    exact acyclicSmallNullhomotopy N t x

/-- Weakness in the common-universe model implies weakness of the unchanged original map. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_of_smallModel
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N.smallModel)) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) := by
  have hh := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv)
  rw [← smallModel_canonicalFiberMap_square] at hh
  exact hh.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (smallModelChangeWeakFiberHomeomorph N).toHomotopyEquiv)

end Quillen.Waldhausen.Fibration

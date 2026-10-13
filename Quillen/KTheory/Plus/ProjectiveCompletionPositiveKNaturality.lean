/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveCompletionFiberNaturality
public import Quillen.KTheory.Plus.ProjectiveCompletionPositiveK
public import Quillen.Topology.HomotopyFiber.LoopComparisonNaturality
public import Quillen.Topology.HomotopyGroups.PathComponentPositiveNaturality

/-! # Naturality of the original positive Quillen comparison -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.FiniteProjectiveModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- Naturality of the unchanged completion-to-loop maps with their original based tracks. -/
theorem completionToOriginalQLoops_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    homotopyGroupMap
      (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f))
      (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
      (pathTransport (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
        (StableCompletion.stageObject R 0)) n
        (homotopyGroupMap (completionToOriginalQLoops Rᵐᵒᵖ
          (StableCompletion.stageObject R 0)) rfl a)) =
    pathTransport (completionToOriginalQLoopsBasepointPath Sᵐᵒᵖ
      (StableCompletion.stageObject S 0)) n
      (homotopyGroupMap (completionToOriginalQLoops Sᵐᵒᵖ
        (StableCompletion.stageObject S 0)) rfl
        (pathTransport (completionBaseChangeBasepointPath f) n
          (homotopyGroupMap (completionBaseChangeMap f) rfl a))) := by
  let := localizedExtension_classifyingSpace_contractible Rᵐᵒᵖ
  let := localizedExtension_classifyingSpace_contractible Sᵐᵒᵖ
  have h := HomotopyFiber.loopComparison_naturality_pi
    (classifyingSpaceMapUniversal (localizedExtensionBaseChange f))
    (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
    (completionNormalizedProjectionHomotopy f)
    (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero)
    (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero)
    (completionNormalizedQ_basepoint f)
    (completionToOriginalQHomotopyFiber Rᵐᵒᵖ)
    (completionToOriginalQHomotopyFiber Sᵐᵒᵖ) (completionBaseChangeMap f)
    (completionFiberNaturality f) (StableCompletion.zeroPoint R)
    (StableCompletion.zeroPoint S) (completionBaseChangeBasepointPath f) n a
  have hr := homotopyGroupMap_comp
    (completionToOriginalQHomotopyFiber Rᵐᵒᵖ) rfl
    (originalQLoopFiberHomotopyEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0)).invFun rfl a
  have hs := homotopyGroupMap_comp
    (completionToOriginalQHomotopyFiber Sᵐᵒᵖ) rfl
    (originalQLoopFiberHomotopyEquiv Sᵐᵒᵖ (StableCompletion.stageObject S 0)).invFun rfl
    (pathTransport (completionBaseChangeBasepointPath f) n
      (homotopyGroupMap (completionBaseChangeMap f) rfl a))
  exact (congrArg (fun b ↦ homotopyGroupMap
    (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (completionNormalizedQ_basepoint f))
    (basedLoopMap_refl _ (completionNormalizedQ_basepoint f))
      (pathTransport (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
        (StableCompletion.stageObject R 0)) n b)) hr).trans
    (h.trans (congrArg (pathTransport (completionToOriginalQLoopsBasepointPath Sᵐᵒᵖ
      (StableCompletion.stageObject S 0)) n) hs.symm))

/-- The actual completion comparison commutes with the original exact-functor K-map
in every positive degree, retaining the actual monoidal-unit basepoint edge. -/
theorem completionPositiveKEquiv_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ClassifyingSpace (StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    completionPositiveKEquiv Sᵐᵒᵖ (StableCompletion.stageObject S 0) n
      (pathTransportMulEquiv (completionBaseChangeBasepointPath f) n
        (homotopyGroupMapHom (N := Fin (n + 1)) (completionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1)
      (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a) := by
  apply (loopShiftMulEquiv n).injective
  rw [completionPositiveKEquiv_apply, MulEquiv.apply_symm_apply]
  have hn := completionToOriginalQLoops_baseChange f (n + 1) a
  have hs := loopShiftEquiv_natural (n + 1)
    (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
    (completionNormalizedQ_basepoint f)
    (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a)
  have hr : loopShiftEquiv (n + 1)
      (completionPositiveKEquiv Rᵐᵒᵖ (StableCompletion.stageObject R 0) n a) =
    pathTransport (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ
      (StableCompletion.stageObject R 0)) (n + 1)
      (homotopyGroupMap (completionToOriginalQLoops Rᵐᵒᵖ
        (StableCompletion.stageObject R 0)) rfl a) :=
    (loopShiftMulEquiv n).apply_symm_apply _
  rw [hr] at hs
  exact hn.symm.trans hs.symm

namespace StableCompletion

/-- The unchanged zero-component comparison is natural for the actual ring map and
its actual restricted monoidal-unit path, in every positive original K-degree. -/
theorem zeroCompletionPositiveKEquiv_baseChange (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    zeroCompletionPositiveKEquiv S n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (homotopyGroupMapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a)) =
    (rightBaseChangeExact f).KMap (n + 1) (zeroCompletionPositiveKEquiv R n a) := by
  change completionPositiveKEquiv Sᵐᵒᵖ (stageObject S 0) n
    (pathComponentPiMulEquiv (zeroPoint S) n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (homotopyGroupMapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a))) = _
  exact (congrArg (completionPositiveKEquiv Sᵐᵒᵖ (stageObject S 0) n)
    (pathComponentPiMulEquiv_naturality_apply (completionBaseChangeMap f)
      (zeroPoint R) (zeroPoint S) (completionBaseChangeBasepointPath f) n a)).trans
      (completionPositiveKEquiv_baseChange f n _)

end StableCompletion
end Quillen.FiniteProjectiveModule

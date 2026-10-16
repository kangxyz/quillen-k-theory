/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationPath
public import Quillen.Waldhausen.SConstruction.Iterated.HomotopyTransport
public import Quillen.Waldhausen.SConstruction.ObjectTransformationSquareRealization
public import Quillen.Waldhausen.AutomorphismKOne
public import Quillen.Topology.HomotopyGroups.FundamentalGroupNaturality

/-! # Original self-track evaluation on an actual object

The original object loop is transported by the actual small-model homeomorphism.
The complete level-one transformation is its component weak-arrow square, with
spatial and track times unchanged. Canonical zero rebasing is retained until
its conjugation is removed by the original weak-endomorphism class theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

/-- The literal based image of the original object loop at the original first spectrum level. -/
def originalSmallModelObjectLoop (A : C) :
    Path ((originalPrespectrum W).point 1) ((originalPrespectrum W).point 1) :=
  basedLoopMap W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    W.smallModelDeloopingHomeomorph_basepoint (W.kZeroObjectLoop A)

/-- The original object class has this actual representative; none is selected. -/
theorem originalSmallModelObjectLoop_class (A : C) :
    W.smallModelKEquiv 0 (W.kZeroObjectClass A) =
      ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm (originalSmallModelObjectLoop W A)⟧ := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (piMap 0 W.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
      W.smallModelDeloopingHomeomorph_basepoint (W.kZeroObjectClass A)) = _
  rw [piOneEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (W.kZeroFundamentalGroupEquiv (W.kZeroObjectClass A)) = _
  rw [W.kZeroFundamentalGroupEquiv_objectClass, FundamentalGroup.mapOfEq_apply]
  rfl

variable {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (h0 : F.obj W.zero = V.zero) (η : F ⟶ F) (hη : ∀ A, V.weq (η.app A))

/-- The entire actual level-one object track retains both original times. -/
theorem originalTransformation_object_track_apply (A : C) (s t : unitInterval) :
    (originalPrespectrumTransformationHomotopy W V hF hF h0 h0 η hη).pathSelfTrack 1
        (originalSmallModelObjectLoop W A) s t =
      V.smallModelDeloopingHomeomorph (V.weakObjectSquareLoopPath (η.app A) (hη A) s t) := by
  change (originalPrespectrumTransformationHomotopy W V hF hF h0 h0 η hη).level 1
    (s, W.smallModelDeloopingHomeomorph (W.kZeroObjectLoop A t)) = _
  rw [originalPrespectrumTransformationHomotopy_level_one]
  exact congrArg V.smallModelDeloopingHomeomorph
    (objectTransformationRealization_square W V hF hF η hη h0 h0 A s t)

/-- A strictly zero-preserving transformation evaluates to its original component class. -/
theorem originalKSelfTrackOperation_object_strict (A : C) :
    originalKSelfTrackOperation W V
      (originalPrespectrumTransformationHomotopy W V hF hF h0 h0 η hη) 0
      (W.kZeroObjectClass A) = V.weakEndomorphismKOneClass (η.app A) (hη A) := by
  let H := originalPrespectrumTransformationHomotopy W V hF hF h0 h0 η hη
  let γ := originalSmallModelObjectLoop W A
  let f := originalPrespectrumMap W V hF h0
  let δ := basedLoopMap (f.map 1) (f.map_point 1) γ
  let α := V.weakObjectSquareLoopPath (η.app A) (hη A)
  let L := V.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
  have he : basedLoopMap L V.smallModelDeloopingHomeomorph_basepoint
      (V.kZeroObjectLoop (F.obj A)) = δ := by
    apply Path.ext
    funext t
    have ht := originalTransformation_object_track_apply W V hF h0 η hη A 0 t
    have hs := congrArg (fun p : Path V.kBasepoint V.kBasepoint ↦ p t) α.source
    have hH := congrArg (fun p : Path ((originalPrespectrum V).point 1)
      ((originalPrespectrum V).point 1) ↦ p t) (H.pathSelfTrack 1 γ).source
    exact (congrArg V.smallModelDeloopingHomeomorph hs).symm.trans (ht.symm.trans hH)
  have hp : (α.map (basedLoopMap L V.smallModelDeloopingHomeomorph_basepoint).continuous).cast
      he.symm he.symm = H.pathSelfTrack 1 γ := by
    apply Path.ext
    funext s
    apply Path.ext
    funext t
    exact (originalTransformation_object_track_apply W V hF h0 η hη A s t).symm
  apply (V.smallModelKEquiv 1).injective
  calc
    V.smallModelKEquiv 1 (originalKSelfTrackOperation W V H 0 (W.kZeroObjectClass A)) =
        loopKOneNormalization δ ⟦H.pathSelfTrack 1 γ⟧ :=
      originalKSelfTrackOperation_path W V H _ γ (originalSmallModelObjectLoop_class W A)
    _ = piMap 1 L V.smallModelDeloopingHomeomorph_basepoint
        (loopKOneNormalization (V.kZeroObjectLoop (F.obj A)) ⟦α⟧) := by
      rw [loopKOneNormalization_naturality_of_loopEq L
        V.smallModelDeloopingHomeomorph_basepoint _ δ he α, hp]
      rfl
    _ = V.smallModelKEquiv 1 (V.weakEndomorphismKOneClass (η.app A) (hη A)) := rfl

/-- Canonical zero rebasing preserves the actual component automorphism class. -/
theorem originalKSelfTrackOperation_object (e : F ≅ F) (A : C) :
    originalKSelfTrackOperation W V (exactOriginalPrespectrumIsoHomotopy W V hF hF e) 0
      (W.kZeroObjectClass A) = V.automorphismKOneClass (e.app A) := by
  let e0 := rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)
  let η := normalizedWeakTransformation hF hF e.hom
  let hη := normalizedWeakTransformation_weak hF hF e.hom
    (fun _A ↦ V.weq_iso _ inferInstance)
  have hc := V.weakEndomorphismKOneClass_iso (e0.app A) (e.app A).hom (η.app A)
    (V.weq_iso _ inferInstance) (hη A) (by
      dsimp [η, normalizedWeakTransformation, e0]
      simp only [Iso.hom_inv_id_app_assoc])
  exact (originalKSelfTrackOperation_object_strict W V hF.rebase
    (rebaseFunctor_obj_base _ _ _ _) η hη A).trans hc.symm

end Quillen.Waldhausen.IteratedS

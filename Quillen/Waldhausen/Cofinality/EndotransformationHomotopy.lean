/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Cofinality.Grading
public import Quillen.Waldhausen.SConstruction.Iterated.EndotransformationContraction
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Actual endotransformation tracks in a grading-coarse model

Every zero endomorphism is weak for the original endpoint-grade weak class. The actual
zero endotransformation therefore absorbs any original endotransformation. Its genuine
composition triangle and explicit reverse-track cancellation contract the unchanged
canonically normalized prespectrum self-track, relative to both endpoints and the point.
The zero endotransformation is a self-track, not a nullhomotopy of the underlying map.
No concentration or choice of pointwise contractions is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.Waldhausen.Cofinality.Grading
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} {G : Type w} [AddCommGroup G]
  (d : Grading V G) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq d.coarseStructure.cof d.coarseStructure.weq F)

/-- The original normalized track of any endotransformation is contracted through the
same weak zero endotransformation and its original composition triangle. -/
def exactEndotransformationContraction (η : F ⟶ F) :
    (exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
      (fun _ ↦ rfl)).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (exactOriginalPrespectrumMap W d.coarseStructure hF)) := by
  unfold exactOriginalPrespectrumHomotopy originalPrespectrumTransformationHomotopy
  exact prespectrumEndotransformationContraction _ _ _ (fun _ ↦ rfl)

/-- The prescribed null-conjugate is globally null when its original self-track comes
from an endotransformation in the actual grading-coarse target. Both original null legs
are retained before the genuine relative contractions are applied. -/
def exactEndotransformationNullLoopHomotopy (η : F ⟶ F)
    {T : LoopPrespectrum.{max u v}} (j : originalPrespectrum d.coarseStructure ⟶ T)
    (N : Homotopy (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)
      (zeroHom (originalPrespectrum W) T)) :
    Homotopy (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
      (fun _ ↦ rfl)).postcomp j).nullLoopMap N)
      (zeroHom (originalPrespectrum W) (parameterLooping T)) := by
  let H := (exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
    (fun _ ↦ rfl)).postcomp j
  have J : H.RelHomotopy (LoopPrespectrum.Homotopy.refl
      (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)) :=
    (d.exactEndotransformationContraction W hF η).postcomp j
  have K : (H.conjugateToZero N).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (zeroHom (originalPrespectrum W) T)) :=
    ((LoopPrespectrum.Homotopy.RelHomotopy.refl N.symm).hcomp
      ((J.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl N)).trans
        (LoopPrespectrum.Homotopy.RelHomotopy.reflTrans N))).trans
      (LoopPrespectrum.Homotopy.RelHomotopy.reflSymmTrans N).symm
  exact K.zeroLoopMapHomotopy

end Quillen.Waldhausen.Cofinality.Grading

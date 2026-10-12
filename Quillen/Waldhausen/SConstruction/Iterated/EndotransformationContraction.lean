/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumCompositionHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# Contracting original transformation tracks by the weak zero endotransformation

The actual chosen-zero endotransformation absorbs an original weak endotransformation.
When its components are weak, the original composition triangle and explicit reverse-track
cancellation contract the original Model self-track. Both endpoints, the entire point line,
and the independent structure coordinate are fixed. The zero endotransformation is retained
as a self-track; this does not contract the underlying Model map or its target spectrum.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} (F : V ⟶ W)

/-- The actual endotransformation through the target Model's specified zero object. -/
def modelZeroEndotransformation : F.functor ⟶ F.functor where
  app A := W.waldhausen.isZero.from_ (F.functor.obj A) ≫
    W.waldhausen.isZero.to_ (F.functor.obj A)
  naturality {A B} f := by
    have h₀ := W.waldhausen.isZero.eq_of_tgt
      (F.functor.map f ≫ W.waldhausen.isZero.from_ (F.functor.obj B))
      (W.waldhausen.isZero.from_ (F.functor.obj A))
    have h₁ := W.waldhausen.isZero.eq_of_src
      (W.waldhausen.isZero.to_ (F.functor.obj A) ≫ F.functor.map f)
      (W.waldhausen.isZero.to_ (F.functor.obj B))
    rw [← Category.assoc, h₀, Category.assoc, h₁]

/-- Absorption is an equality of the original transformations, before realization. -/
theorem modelZeroEndotransformation_absorb (η : F.functor ⟶ F.functor) :
    η ≫ modelZeroEndotransformation F = modelZeroEndotransformation F := by
  ext A
  change η.app A ≫ (W.waldhausen.isZero.from_ (F.functor.obj A) ≫
    W.waldhausen.isZero.to_ (F.functor.obj A)) = _
  rw [← Category.assoc, W.waldhausen.isZero.eq_of_tgt
    (η.app A ≫ W.waldhausen.isZero.from_ (F.functor.obj A))
    (W.waldhausen.isZero.from_ (F.functor.obj A))]
  rfl

/-- The specified original triangle compares the weak zero track to the scalar-then-zero
track, without replacing either whole homotopy. -/
def prespectrumEndotransformationAbsorptionTriangle
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) :
    (prespectrumTransformationHomotopy (modelZeroEndotransformation F) hz).RelHomotopy
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy (modelZeroEndotransformation F) hz)) := by
  have J := prespectrumTransformationCompositionHomotopy η
    (modelZeroEndotransformation F) hη hz
  simpa only [modelZeroEndotransformation_absorb F η] using J

/-- A genuine weak zero endotransformation contracts the original whole Model self-track.
Only the supplied weakness of its actual components is used. -/
def prespectrumEndotransformationContraction
    (η : F.functor ⟶ F.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))
    (hz : ∀ A, W.waldhausen.weq ((modelZeroEndotransformation F).app A)) :
    (prespectrumTransformationHomotopy η hη).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (prespectrumMap F)) := by
  let H := prespectrumTransformationHomotopy η hη
  let Z := prespectrumTransformationHomotopy (modelZeroEndotransformation F) hz
  let J := prespectrumEndotransformationAbsorptionTriangle F η hη hz
  exact (LoopPrespectrum.Homotopy.RelHomotopy.transRefl H).symm.trans
    (((LoopPrespectrum.Homotopy.RelHomotopy.refl H).hcomp
      (LoopPrespectrum.Homotopy.RelHomotopy.reflTransSymm Z)).trans
      ((LoopPrespectrum.Homotopy.RelHomotopy.transAssoc H Z Z.symm).symm.trans
        ((J.symm.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl Z.symm)).trans
          (LoopPrespectrum.Homotopy.RelHomotopy.reflTransSymm Z).symm)))

end Quillen.Waldhausen.IteratedS

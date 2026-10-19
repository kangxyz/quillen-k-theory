/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitAction

/-!
# Tensor-unit action on the original geometric pullback

The underlying functor first performs the original termwise geometric pullback and then tensors
by the structure module. Its genuine left unitor identifies the coefficient-unit action with
the existing forward scalar automorphism on pullback, as an equality of natural transformations.

Intended upstream owner:
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitPullback`.
The hypotheses are an arbitrary scheme map and a global unit on its source. The current consumer
is the original restricted tensor-unit iterated-S comparison in Quillen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Original geometric pullback followed by genuine degreewise tensor by the structure module. -/
def boundedFlatPerfectTensorUnitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X :=
  boundedFlatPerfectPullback f ⋙ boundedFlatPerfectTensorUnit X

/-- The actual tensor left unitor on every original pulled-back complex. -/
def boundedFlatPerfectTensorUnitPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatPerfectTensorUnitPullback f ≅ boundedFlatPerfectPullback f :=
  Functor.isoWhiskerLeft (boundedFlatPerfectPullback f) (boundedFlatPerfectTensorUnitIso X) ≪≫
    Functor.rightUnitor _

/-- Tensor the original structure-module unit automorphism on every pulled-back complex. -/
def boundedFlatPerfectTensorUnitPullbackAutomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    boundedFlatPerfectTensorUnitPullback f ≅ boundedFlatPerfectTensorUnitPullback f :=
  Functor.isoWhiskerLeft (boundedFlatPerfectPullback f)
    (boundedFlatPerfectTensorUnitAutomorphism X r)

/-- The unitor retains the actual tensor-unit comparison after arbitrary geometric pullback. -/
theorem boundedFlatPerfectTensorUnitPullbackIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : BoundedFlatPerfect Y) :
    (boundedFlatPerfectTensorUnitPullbackIso f).hom.app K =
      (boundedFlatPerfectTensorUnitIso X).hom.app ((boundedFlatPerfectPullback f).obj K) := by
  simp only [boundedFlatPerfectTensorUnitPullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

/-- This is the original forward scalar, with tensor order and geometric pullback unchanged. -/
theorem boundedFlatPerfectTensorUnitPullbackAutomorphism_unitor {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
        (boundedFlatPerfectTensorUnitPullbackIso f).hom =
      (boundedFlatPerfectTensorUnitPullbackIso f).hom ≫
        (boundedFlatPerfectPullbackUnitIso f r).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedFlatPerfectTensorUnitPullbackAutomorphism,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    boundedFlatPerfectTensorUnitPullbackIso_hom_app, boundedFlatPerfectPullbackUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  exact NatTrans.congr_app (boundedFlatPerfectTensorUnitAutomorphism_unitor X r)
    ((boundedFlatPerfectPullback f).obj K)

end Quillen.PerfectComplexes

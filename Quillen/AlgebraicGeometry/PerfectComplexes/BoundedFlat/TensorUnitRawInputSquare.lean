/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorModelUnit
public import
  Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback

/-! # The genuine tensor-unit square on an original geometric pullback square

This comparison is formed solely from the original geometric pullback composition isomorphisms
and actual tensor unitors. It is independent of section evaluation and its categorical inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes
variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The raw tensor input comparison retains the original pullback comparison and both unitors. -/
def tensorUnitRawInputIso :
    boundedFlatPerfectTensorUnitPullback p ⋙ boundedFlatPerfectPullback a ≅
      boundedFlatPerfectPullback b ⋙ boundedFlatPerfectTensorUnitPullback q :=
  isoWhiskerRight (boundedFlatPerfectTensorUnitPullbackIso p) (boundedFlatPerfectPullback a) ≪≫
    (boundedFlatPerfectPullbackCompIso a p).symm ≪≫
    eqToIso (congrArg boundedFlatPerfectPullback h) ≪≫
    boundedFlatPerfectPullbackCompIso q b ≪≫
    isoWhiskerLeft (boundedFlatPerfectPullback b) (boundedFlatPerfectTensorUnitPullbackIso q).symm

/-- Genuine tensor multiplication respects the original raw input square at the pulled-back unit.
-/
theorem tensorUnitRawInputIso_unit (r : (Γ(A, ⊤))ˣ) :
    whiskerRight (boundedFlatPerfectTensorUnitPullbackAutomorphism p r).hom
        (boundedFlatPerfectPullback a) ≫ (tensorUnitRawInputIso p q a b h).hom =
      (tensorUnitRawInputIso p q a b h).hom ≫
        whiskerLeft (boundedFlatPerfectPullback b)
          (boundedFlatPerfectTensorUnitPullbackAutomorphism q
            (Units.map a.appTop.hom.toMonoidHom r)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [ParameterTensorEvaluationRow.tensorAutomorphism_scalar,
    ParameterTensorEvaluationRow.tensorAutomorphism_scalar,
    boundedFlatPerfectPullback_map_globalUnit]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
    ((boundedFlatPerfectGlobalUnitIso C (Units.map a.appTop.hom.toMonoidHom r)).hom.naturality
      ((tensorUnitRawInputIso p q a b h).hom.app K)).symm

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatRetracts
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Actual projective presheaves and their flat sheafifications

Module presheaves have enough projectives, using the actual free Yoneda
presheaves and their canonical epimorphic coproduct. Exact sheafification sends
these projectives to genuinely stalkwise-flat module sheaves. This provides a
second concrete route to replacing bounded-above complexes before pullback.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual free presheaf on an open representable is projective. -/
instance freeYoneda_projective (X : Scheme.{u}) (U : X.Opens) :
    Projective ((_root_.PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U)) where
  factors q p _ := by
    obtain ⟨s, hs⟩ := _root_.PresheafOfModules.surjective_of_epi p (op U)
      (_root_.PresheafOfModules.freeYonedaEquiv q)
    refine ⟨_root_.PresheafOfModules.freeYonedaEquiv.symm s, ?_⟩
    apply _root_.PresheafOfModules.freeYonedaEquiv.injective
    rw [_root_.PresheafOfModules.freeYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hs

instance freeYonedaCoproduct_projective (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) : Projective P.freeYonedaCoproduct := by
  let (s : P.Elements) : Projective s.freeYoneda := freeYoneda_projective X s.1.unop
  infer_instance

/-- There are enough actual projective module presheaves on any scheme. -/
instance modulePresheaf_enoughProjectives (X : Scheme.{u}) :
    EnoughProjectives (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) where
  presentation P := ⟨{ p := P.freeYonedaCoproduct, f := P.fromFreeYonedaCoproduct }⟩

/-- The actual sheafification of a free-Yoneda coproduct has flat module stalks. -/
theorem stalkwiseFlat_sheafify_freeYonedaCoproduct (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    stalkwiseFlat X ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      P.freeYonedaCoproduct) := by
  apply (stalkwiseFlat X).prop_of_iso
    (PreservesCoproduct.iso (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (_root_.PresheafOfModules.Elements.freeYoneda (M := P))).symm
  exact stalkwiseFlat_coproduct X _ (fun s x => openFree_stalk_flat X x s.1.unop)

/-- Sheafification of an actual projective presheaf is genuinely stalkwise flat. -/
theorem stalkwiseFlat_sheafify_projective (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) [Projective P] :
    stalkwiseFlat X ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let r : Retract P P.freeYonedaCoproduct :=
    { i := Projective.factorThru (𝟙 P) P.fromFreeYonedaCoproduct
      r := P.fromFreeYonedaCoproduct }
  exact stalkwiseFlat_of_retract
    (r.map (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
    (stalkwiseFlat_sheafify_freeYonedaCoproduct X P)

end AlgebraicGeometry.Scheme.Modules

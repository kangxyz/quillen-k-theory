/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ExtensionByZero
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Open base change for the actual extension-by-zero functor

The comparison for a commuting open square is its actual adjunction mate,
with a proved unit equation and compatibility with the original counits.
The pointwise cartesian condition makes this mate invertible, by restriction
and the proved off-image stalk vanishing. The actual scheme-pullback
specialization supplies that condition without any extra premise.

Composition of extension by zero is identified by uniqueness of the genuine
left adjoints; both original unit and counit formulas retain the scalar and
open-restriction coherence maps. All sheaves are ambient module sheaves.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Module-sheaf morphisms are detected on the original abelian-group stalks. -/
lemma isIso_of_stalkFunctor {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x, IsIso ((stalkFunctor X x).map f)) : IsIso f := by
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr hf
  have : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)))
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

/-- An isomorphism on an open is global if both sheaves have zero stalks outside it. -/
lemma isIso_of_restrict_of_stalks_zero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor j).map f)]
    (hM : ∀ x, x ∉ Set.range j → IsZero ((stalkFunctor X x).obj M))
    (hN : ∀ x, x ∉ Set.range j → IsZero ((stalkFunctor X x).obj N)) : IsIso f := by
  apply isIso_of_stalkFunctor
  intro x
  by_cases hx : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hx
    let e := Scheme.Modules.restrictStalkNatIso j y
    have h := e.hom.naturality f
    have : IsIso ((Scheme.Modules.restrictFunctor j ⋙ stalkFunctor U y).map f) := by
      change IsIso ((stalkFunctor U y).map ((Scheme.Modules.restrictFunctor j).map f))
      infer_instance
    have : IsIso (e.hom.app M ≫ (stalkFunctor X (j y)).map f) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left (e.hom.app M) _
  · exact isIso_of_source_target_iso_zero _ (hM x hx).isoZero (hN x hx).isoZero

section Square
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)

/-- The original restrictions around a commuting open square. -/
def openSquareRestrictIso :
    Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.restrictFunctor a ≅
      Scheme.Modules.restrictFunctor k ⋙ Scheme.Modules.restrictFunctor b :=
  (Scheme.Modules.restrictFunctorComp a j).symm ≪≫
    Scheme.Modules.restrictFunctorCongr h ≪≫ Scheme.Modules.restrictFunctorComp b k

/-- The unit-induced comparison on the overlap, retaining the original square. -/
def extensionByZeroBaseChangeUnitIso :
    Scheme.Modules.restrictFunctor a ≅
      (extensionByZero j ⋙ Scheme.Modules.restrictFunctor k) ⋙
        Scheme.Modules.restrictFunctor b :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (extensionByZeroRestrictAdjunction j).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openSquareRestrictIso a b j k h) ≪≫
    (Functor.associator _ _ _).symm

/-- The actual extension-by-zero base-change mate, before assuming cartesianness. -/
def extensionByZeroBaseChange :
    Scheme.Modules.restrictFunctor a ⋙ extensionByZero b ⟶
      extensionByZero j ⋙ Scheme.Modules.restrictFunctor k :=
  (((extensionByZeroRestrictAdjunction b).whiskerRight U.Modules).homEquiv _ _).symm
    (extensionByZeroBaseChangeUnitIso a b j k h).hom

/-- Restricting the actual base-change mate gives exactly its defining unit square. -/
@[reassoc]
lemma extensionByZeroBaseChange_unit (M : U.Modules) :
    (extensionByZeroRestrictAdjunction b).unit.app ((Scheme.Modules.restrictFunctor a).obj M) ≫
      (Scheme.Modules.restrictFunctor b).map ((extensionByZeroBaseChange a b j k h).app M) =
    (extensionByZeroBaseChangeUnitIso a b j k h).hom.app M := by
  have H := (((extensionByZeroRestrictAdjunction b).whiskerRight U.Modules).homEquiv _
    _).apply_symm_apply
    (extensionByZeroBaseChangeUnitIso a b j k h).hom
  exact congr_app H M

instance restrict_extensionByZeroBaseChange_isIso (M : U.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor b).map
      ((extensionByZeroBaseChange a b j k h).app M)) := by
  have : IsIso ((extensionByZeroRestrictAdjunction b).unit.app
      ((Scheme.Modules.restrictFunctor a).obj M) ≫
        (Scheme.Modules.restrictFunctor b).map
          ((extensionByZeroBaseChange a b j k h).app M)) := by
    rw [extensionByZeroBaseChange_unit]
    infer_instance
  exact IsIso.of_isIso_comp_left ((extensionByZeroRestrictAdjunction b).unit.app
    ((Scheme.Modules.restrictFunctor a).obj M)) _

/-- Genuine open base change: the pointwise cartesian condition forces the mate to be invertible. -/
lemma extensionByZeroBaseChange_isIso
    (hcart : ∀ v : V, k v ∈ Set.range j → v ∈ Set.range b) (M : U.Modules) :
    IsIso ((extensionByZeroBaseChange a b j k h).app M) := by
  apply isIso_of_restrict_of_stalks_zero b
  · intro v hv
    exact (forget₂ (ModuleCat (V.presheaf.stalk v)) AddCommGrpCat).map_isZero
      (isZero_extensionByZero_stalk_of_not_mem b v hv _)
  · intro v hv
    have hz := (forget₂ (ModuleCat (X.presheaf.stalk (k v))) AddCommGrpCat).map_isZero
      (isZero_extensionByZero_stalk_of_not_mem j (k v) (fun H => hv (hcart v H)) M)
    exact hz.of_iso ((Scheme.Modules.restrictStalkNatIso k v).app ((extensionByZero j).obj M))

/-- The genuine base-change isomorphism of original module-sheaf functors. -/
def extensionByZeroBaseChangeIso
    (hcart : ∀ v : V, k v ∈ Set.range j → v ∈ Set.range b) :
    Scheme.Modules.restrictFunctor a ⋙ extensionByZero b ≅
      extensionByZero j ⋙ Scheme.Modules.restrictFunctor k := by
  have hM (M : U.Modules) : IsIso ((extensionByZeroBaseChange a b j k h).app M) :=
    extensionByZeroBaseChange_isIso a b j k h hcart M
  have : IsIso (extensionByZeroBaseChange a b j k h) := NatIso.isIso_of_isIso_app _
  exact asIso (extensionByZeroBaseChange a b j k h)

/-- The actual base-change mate is compatible with the original counits. -/
@[reassoc]
lemma extensionByZeroBaseChange_counit (M : X.Modules) :
    (extensionByZeroBaseChange a b j k h).app ((Scheme.Modules.restrictFunctor j).obj M) ≫
      (Scheme.Modules.restrictFunctor k).map ((extensionByZeroRestrictAdjunction j).counit.app M) =
    (extensionByZero b).map ((openSquareRestrictIso a b j k h).hom.app M) ≫
      (extensionByZeroRestrictAdjunction b).counit.app ((Scheme.Modules.restrictFunctor k).obj M) :=
        by
  apply ((extensionByZeroRestrictAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  have H := extensionByZeroBaseChange_unit a b j k h ((Scheme.Modules.restrictFunctor j).obj M)
  change ((extensionByZeroRestrictAdjunction b).homEquiv _ _)
    ((extensionByZeroBaseChange a b j k h).app ((Scheme.Modules.restrictFunctor j).obj M)) = _ at H
  rw [H]
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj]
  have Hb := (extensionByZeroRestrictAdjunction b).right_triangle_components
    ((Scheme.Modules.restrictFunctor k).obj M)
  change (extensionByZeroRestrictAdjunction b).unit.app _ ≫
    (Scheme.Modules.restrictFunctor b).map _ = 𝟙 _ at Hb
  erw [Hb, Category.comp_id]
  change (Scheme.Modules.restrictFunctor a).map
    ((extensionByZeroRestrictAdjunction j).unit.app ((Scheme.Modules.restrictFunctor j).obj M)) ≫
      (openSquareRestrictIso a b j k h).hom.app
        ((extensionByZero j).obj ((Scheme.Modules.restrictFunctor j).obj M)) ≫ _ = _
  have Hn := (openSquareRestrictIso a b j k h).hom.naturality
    ((extensionByZeroRestrictAdjunction j).counit.app M)
  change (Scheme.Modules.restrictFunctor a).map ((Scheme.Modules.restrictFunctor j).map _) ≫
    (openSquareRestrictIso a b j k h).hom.app M =
      (openSquareRestrictIso a b j k h).hom.app _ ≫
        (Scheme.Modules.restrictFunctor b).map ((Scheme.Modules.restrictFunctor k).map _) at Hn
  erw [← Hn, ← Functor.map_comp_assoc]
  erw [Adjunction.right_triangle_components]
  exact ((Scheme.Modules.restrictFunctor a).map_id _ =≫
    (openSquareRestrictIso a b j k h).hom.app M).trans (Category.id_comp _)

end Square
/-- Base change for the actual scheme pullback of two arbitrary open immersions. -/
def extensionByZeroPullbackIso {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    Scheme.Modules.restrictFunctor (pullback.fst j k) ⋙ extensionByZero (pullback.snd j k) ≅
      extensionByZero j ⋙ Scheme.Modules.restrictFunctor k :=
  extensionByZeroBaseChangeIso _ _ j k pullback.condition (by
    intro v hv
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hv)

/-- Extension by zero along a composite, retaining the genuine restriction adjunctions. -/
def extensionByZeroComp {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] :
    extensionByZero (a ≫ j) ≅ extensionByZero a ⋙ extensionByZero j :=
  Adjunction.leftAdjointUniq (extensionByZeroRestrictAdjunction (a ≫ j))
    (((extensionByZeroRestrictAdjunction a).comp (extensionByZeroRestrictAdjunction
      j)).ofNatIsoRight
      (Scheme.Modules.restrictFunctorComp a j).symm)

/-- The composition comparison retains the original extension-by-zero counits. -/
@[reassoc]
lemma extensionByZeroComp_hom_counit {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : X.Modules) :
    (extensionByZeroComp a j).hom.app ((Scheme.Modules.restrictFunctor (a ≫ j)).obj M) ≫
      (extensionByZero j).map ((extensionByZero a).map
        ((Scheme.Modules.restrictFunctorComp a j).hom.app M)) ≫
      (extensionByZero j).map ((extensionByZeroRestrictAdjunction a).counit.app
        ((Scheme.Modules.restrictFunctor j).obj M)) ≫
      (extensionByZeroRestrictAdjunction j).counit.app M =
    (extensionByZeroRestrictAdjunction (a ≫ j)).counit.app M := by
  exact Adjunction.leftAdjointUniq_hom_app_counit
    (extensionByZeroRestrictAdjunction (a ≫ j))
    (((extensionByZeroRestrictAdjunction a).comp (extensionByZeroRestrictAdjunction
      j)).ofNatIsoRight
      (Scheme.Modules.restrictFunctorComp a j).symm) M

/-- The composition comparison also retains the actual units, including ring/open coherence. -/
@[reassoc]
lemma extensionByZeroComp_unit {W U X : Scheme.{u}} (a : W ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (M : W.Modules) :
    (extensionByZeroRestrictAdjunction (a ≫ j)).unit.app M ≫
      (Scheme.Modules.restrictFunctor (a ≫ j)).map ((extensionByZeroComp a j).hom.app M) ≫
      (Scheme.Modules.restrictFunctorComp a j).hom.app
        ((extensionByZero j).obj ((extensionByZero a).obj M)) =
    (extensionByZeroRestrictAdjunction a).unit.app M ≫
      (Scheme.Modules.restrictFunctor a).map ((extensionByZeroRestrictAdjunction j).unit.app
        ((extensionByZero a).obj M)) := by
  have H := Adjunction.unit_leftAdjointUniq_hom_app
    (extensionByZeroRestrictAdjunction (a ≫ j))
    (((extensionByZeroRestrictAdjunction a).comp (extensionByZeroRestrictAdjunction
      j)).ofNatIsoRight
      (Scheme.Modules.restrictFunctorComp a j).symm) M
  change _ = ((extensionByZeroRestrictAdjunction a).unit.app M ≫
    (Scheme.Modules.restrictFunctor a).map ((extensionByZeroRestrictAdjunction j).unit.app
      ((extensionByZero a).obj M))) ≫ (Scheme.Modules.restrictFunctorComp a j).inv.app
        ((extensionByZero j).obj ((extensionByZero a).obj M)) at H
  simpa only [extensionByZeroComp, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using
    H =≫ (Scheme.Modules.restrictFunctorComp a j).hom.app
      ((extensionByZero j).obj ((extensionByZero a).obj M))

end AlgebraicGeometry.Scheme.Modules

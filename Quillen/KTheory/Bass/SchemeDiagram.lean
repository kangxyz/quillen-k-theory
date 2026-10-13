/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurentBaseChange
public import Quillen.KTheory.Bass.PolynomialLaurent

/-!
The actual prime-spectrum functor into qc schemes opposite and its polynomial/Laurent natural
diagram identifications. The two original chart transformations retain literal commuting squares in
the variance used by K-theory.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.Scheme.Bass

/-- The genuine prime-spectrum functor, landing in the opposite of qc schemes. -/
def affineSchemeFunctor : CommRingCat.{u} ⥤ QuasiCompactSchemes.{u}ᵒᵖ where
  obj R := op ⟨Spec R,inferInstance⟩
  map f := Quiver.Hom.op ⟨Spec.map f⟩
  map_id R := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Spec.map_id R
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Spec.map_comp f g

/-- The actual natural polynomial comparison in the category used by scheme K-theory. -/
def polynomialDiagramIso :
    Quillen.Bass.polynomialFunctor ⋙ affineSchemeFunctor.{u} ≅
      affineSchemeFunctor ⋙ polynomialFunctor.op :=
  NatIso.ofComponents (fun R ↦
    (ObjectProperty.isoMk quasiCompactSchemeProperty (polynomialSpecIso R)).symm.op) (by
    intro R S f
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    change (polynomialSpecIso S).inv ≫ Spec.map (Quillen.PolynomialBaseChange.polynomialMap f) =
      (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map (Spec.map f) ≫
        (polynomialSpecIso R).inv
    apply (Iso.inv_comp_eq (polynomialSpecIso S)).2
    rw [← Category.assoc,←
      polynomialSpecIso_naturality,Category.assoc,Iso.hom_inv_id,Category.comp_id])

/-- The actual natural Laurent comparison, with its original coefficient-map action. -/
def laurentDiagramIso :
    Quillen.Bass.laurentFunctor ⋙ affineSchemeFunctor.{u} ≅
      affineSchemeFunctor ⋙ laurentFunctor.op :=
  NatIso.ofComponents (fun R ↦
    (ObjectProperty.isoMk quasiCompactSchemeProperty (laurentSpecIso R)).symm.op) (by
    intro R S f
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    change (laurentSpecIso S).inv ≫ Spec.map (Quillen.PolynomialBaseChange.laurentMap f) =
      (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).map (Spec.map f) ≫
        (laurentSpecIso R).inv
    apply (Iso.inv_comp_eq (laurentSpecIso S)).2
    rw [← Category.assoc,←
      laurentSpecIso_naturality,Category.assoc,Iso.hom_inv_id,Category.comp_id])

/-- The original plus transformation is preserved by the full natural diagram comparison. -/
@[reassoc] lemma diagramIso_plus (R : CommRingCat.{u}) :
    affineSchemeFunctor.map (Quillen.Bass.plus.app R) ≫ laurentDiagramIso.hom.app R =
      polynomialDiagramIso.hom.app R ≫ (NatTrans.op plus).app (affineSchemeFunctor.obj R) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentSpecIso R).inv ≫ PolynomialLaurent.laurentPlus R =
    (baseProductTransformation _ _ (PolynomialLaurent.laurentPlus integerRing)
      (PolynomialLaurent.laurentPlus_projection integerRing)).app (Spec R) ≫ (polynomialSpecIso
        R).inv
  apply (Iso.inv_comp_eq (laurentSpecIso R)).2
  rw [← Category.assoc,←
    polynomialLaurentSpecIso_plus,Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- The original inverse-coordinate transformation is preserved as well. -/
@[reassoc] lemma diagramIso_minus (R : CommRingCat.{u}) :
    affineSchemeFunctor.map (Quillen.Bass.minus.app R) ≫ laurentDiagramIso.hom.app R =
      polynomialDiagramIso.hom.app R ≫ (NatTrans.op minus).app (affineSchemeFunctor.obj R) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentSpecIso R).inv ≫ PolynomialLaurent.laurentMinus R =
    (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus integerRing)
      (PolynomialLaurent.laurentMinus_projection integerRing)).app (Spec R) ≫ (polynomialSpecIso
        R).inv
  apply (Iso.inv_comp_eq (laurentSpecIso R)).2
  rw [← Category.assoc,←
    polynomialLaurentSpecIso_minus,Category.assoc,Iso.hom_inv_id,Category.comp_id]

end Quillen.Scheme.Bass

end

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeDoubleContractionSwap
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.NaturalDiagram
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine parameters for the actual double-contraction sign

The actual Laurent swap is natural under parameter isomorphisms. Consequently,
a sign theorem on literal spectra of integral algebras extends to affine
quasi-compact parameters through the canonical spectrum of global sections.
The canonical comparison retains its actual scheme maps, and the original
Laurent product preserves this affine family. No sign hypothesis on arbitrary
quasi-compact parameters is required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)

/-- The actual double-contraction sign transports through a parameter isomorphism. -/
theorem doubleContractionSwap_neg_of_iso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (e : X ≅ Y)
    (h : doubleContractionSwap F Y = -𝟙 ((C (C F)).obj Y)) :
    doubleContractionSwap F X = -𝟙 ((C (C F)).obj X) := by
  apply (cancel_mono ((C (C F)).map e.hom)).1
  rw [← doubleContractionSwap_naturality, h]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp,
    Category.comp_id]

/-- Global sections with their canonical integral algebra structure. -/
def parameterGlobalSectionsAlgebra (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    Under integerRing :=
  Under.mk (integerMap Γ(X.unop.obj, ⊤))

/-- The actual map on global sections, with the unique integral structure square. -/
def parameterGlobalSectionsAlgebraMap {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    parameterGlobalSectionsAlgebra X ⟶ parameterGlobalSectionsAlgebra Y :=
  Under.homMk f.unop.hom.appTop (CommRingCat.isInitial.hom_ext _ _)

/-- The integral algebra map keeps the original map of global sections. -/
@[simp]
theorem parameterGlobalSectionsAlgebraMap_right
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    (parameterGlobalSectionsAlgebraMap f).right = f.unop.hom.appTop := rfl

/-- The canonical affine comparison uses exactly the original quasi-compact Spec object. -/
def affineParameterSpecIso (X : QuasiCompactSchemes.{u}ᵒᵖ) [IsAffine X.unop.obj] :
    X ≅ op (⟨Spec (parameterGlobalSectionsAlgebra X).right,
      inferInstance⟩ : QuasiCompactSchemes.{u}) :=
  (ObjectProperty.isoMk quasiCompactSchemeProperty X.unop.obj.isoSpec).symm.op

/-- The canonical comparison retains the actual inverse of the scheme's Spec isomorphism. -/
@[simp]
theorem affineParameterSpecIso_hom_unop (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [IsAffine X.unop.obj] :
    (affineParameterSpecIso X).hom.unop.hom = X.unop.obj.isoSpec.inv := rfl

/-- Naturality of the canonical affine comparison, with the literal coefficient map. -/
@[reassoc]
theorem affineParameterSpecIso_naturality
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} [IsAffine X.unop.obj] [IsAffine Y.unop.obj]
    (f : X ⟶ Y) :
    f ≫ (affineParameterSpecIso Y).hom =
      (affineParameterSpecIso X).hom ≫
        Scheme.Bass.affineSchemeFunctor.map (parameterGlobalSectionsAlgebraMap f).right := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact (Scheme.isoSpec_inv_naturality f.unop.hom).symm

/-- A sign theorem on the actual integral Spec parameters implies the affine-family sign. -/
theorem doubleContractionSwap_neg_affine_of_under_spec
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : ∀ a : Under integerRing,
      doubleContractionSwap F (op (⟨Spec a.right, inferInstance⟩ : QuasiCompactSchemes.{u})) =
        -𝟙 ((C (C F)).obj (op (⟨Spec a.right, inferInstance⟩ : QuasiCompactSchemes.{u}))))
    (X : QuasiCompactSchemes.{u}ᵒᵖ) [IsAffine X.unop.obj] :
    doubleContractionSwap F X = -𝟙 ((C (C F)).obj X) :=
  doubleContractionSwap_neg_of_iso F (affineParameterSpecIso X)
    (h (parameterGlobalSectionsAlgebra X))

/-- The original Laurent product preserves the affine family of quasi-compact parameters. -/
theorem isAffine_laurent_parameter (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : IsAffine X.unop.obj) :
    IsAffine ((laurentFunctor.op.obj X).unop.obj) := by
  let := h
  change IsAffine (pullback (toIntegerBase X.unop.obj)
    (PolynomialLaurent.laurentProjection integerRing))
  infer_instance

/-- The same closure statement for the original Laurent functor on all schemes. -/
theorem isAffine_global_laurent_parameter (X : Scheme.{u}ᵒᵖ) (h : IsAffine X.unop) :
    IsAffine ((GlobalIndex.laurent.op.obj X).unop) := by
  let := h
  change IsAffine (pullback (toIntegerBase X.unop)
    (PolynomialLaurent.laurentProjection integerRing))
  infer_instance

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

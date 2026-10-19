/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitEdge
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitHomotopy
public import Quillen.Waldhausen.SConstruction.NerveCylinderInterchange

/-!
# A restricted tensor action constructed before the nerve comparison

The actual coefficient arrow `O --μr--> O` is first tensored with an independent input grid by
uncurrying the genuine degreewise coefficient tensor functor. This construction is then identified
with the original nerve-direction cylinder on bounded-flat perfect complexes. Every S-row keeps
its original tensor map, and the original quotient squares remain actual Waldhausen pushouts.

This establishes the raw quotient-grid comparison. Canonical zero normalization, recursive
quotient-row prolongation and the spectrum structure operators are separate consumers.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- Uncurry the actual coefficient tensor edge against an independent original complex grid. -/
def complexTensorUnitPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ)
    (τ : m ⟶ ⦋1⦌) : Grid₂ n m ⥤ CochainComplex X.Modules ℤ :=
  (nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj (complexTensorUnitCoefficientEdge X r)

private theorem complexTensorUnitCoefficientEdge_whisker (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ) :
    complexTensorUnitCoefficientEdge X r ⋙
        (whiskeringLeft _ _ _).obj A =
      ComposableArrows.mk₁ (whiskerLeft A (complexTensorUnitAutomorphism X r).hom) := by
  rw [complexTensorUnitCoefficientEdge_eq]
  apply ComposableArrows.ext₁
    (F := ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom ⋙
      (whiskeringLeft _ _ _).obj A)
    (G := ComposableArrows.mk₁ (whiskerLeft A (complexTensorUnitAutomorphism X r).hom)) rfl rfl
  simp

/-- The independently uncurried tensor edge is the actual original nerve prism. -/
theorem complexTensorUnitPrism_eq_nerve (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ CochainComplex X.Modules ℤ)
    (τ : m ⟶ ⦋1⦌) :
    complexTensorUnitPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (complexTensorUnitAutomorphism X r).hom) τ := by
  unfold complexTensorUnitPrism nerveCylinderDiagram
  rw [← complexTensorUnitCoefficientEdge_whisker]
  rfl

/-- The bounded-flat nerve cylinder retains the independent tensor-edge construction after the
literal inclusion into ordinary complexes. -/
theorem boundedFlatPerfectTensorUnitPrism_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom) τ ⋙
        (boundedFlatPerfect X).ι =
      complexTensorUnitPrism X r (A ⋙ (boundedFlatPerfect X).ι) τ := by
  rw [← iteratedNerveCylinderDiagram_postcomp, complexTensorUnitPrism_eq_nerve]
  congr 1
  apply NatTrans.ext
  funext p
  exact boundedFlatPerfectTensorUnitAutomorphism_hom_original X r (A.obj p)

/-- Every input quotient grid remains a genuine grid under the restricted tensor-unit prism. -/
theorem boundedFlatPerfectTensorUnitPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (hA : IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (nerveCylinderDiagram
        (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom) τ) :=
  nerveCylinderDiagram_isSimplex₂ (boundedFlatPerfectWaldhausen X) _
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (hA.postcomp _ _ (boundedFlatPerfectTensorUnit_exact X))
    (hA.postcomp _ _ (boundedFlatPerfectTensorUnit_exact X)) τ

/-- Along each original S-row the tensor prism uses exactly its selected endpoint map. -/
theorem boundedFlatPerfectTensorUnitPrism_rowMap (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X) (τ : m ⟶ ⦋1⦌)
    (t : Fin (m.len + 1)) (i j k l : Fin (n.len + 1)) (hij : i ≤ j) (hkl : k ≤ l)
    (f : grid₂ t i j hij ⟶ grid₂ t k l hkl) :
    (nerveCylinderDiagram
      (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom) τ).map f =
      ((ComposableArrows.mk₁
        (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom)).obj
          (τ.toOrderHom t)).map f :=
  nerveCylinderDiagram_rowMap _ τ t i j k l hij hkl f

/-- At the original diagonal S-level, the entire cylinder is the tensor-edge times input-grid
construction, with the original simplex and nerve time retained. -/
theorem boundedFlatPerfectTensorUnitCylinder_original (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq).obj n) (τ : (Δ[1]).obj n) :
    ((weakNaturalTransformationCylinder (boundedFlatPerfectWaldhausen X)
      (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectTensorUnit_exact X)
      (boundedFlatPerfectTensorUnit_exact X)
      (boundedFlatPerfectTensorUnitAutomorphism X r).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).app n (A, τ)).val ⋙
        (boundedFlatPerfect X).ι =
      complexTensorUnitPrism X r (A.val ⋙ (boundedFlatPerfect X).ι) τ.down :=
  boundedFlatPerfectTensorUnitPrism_original X r A.val τ.down

end Quillen.PerfectComplexes

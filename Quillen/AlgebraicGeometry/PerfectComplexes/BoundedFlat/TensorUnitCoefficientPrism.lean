/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientAutomorphism
public import Quillen.Waldhausen.SConstruction.NerveCylinderIsomorphism
public import Quillen.Waldhausen.SConstruction.Iterated.NaturalHomotopy

/-!
# The first coefficient row times an independent second-input grid

Uncurry the actual automorphism of the independently tensored `0, O, 0` row against an arbitrary
original second-input quotient grid. Its whole diagram is isomorphic to the original tensor-unit
nerve prism followed by the original one-step row. Restricting the first row along an independent
ordinal parameter identifies the whole slice with the original suspension row, including the
actual zero endpoints. The coefficient object-row time and coefficient automorphism-nerve time
remain separate from the second-input grid. No loop transpose or K-one product is implicit here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- The genuine first tensor-row edge uncurried against an unchanged second-input grid. -/
def tensorUnitFirstRowPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X) (τ : m ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedFlatPerfectWaldhausen X) ⦋1⦌ :=
  (nerveTimeFunctor n τ).prod' A ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ (tensorUnitFirstRowAutomorphism X r).hom)

/-- The independent coefficient edge is the original cylinder on its genuine tensor rows. -/
theorem tensorUnitFirstRowPrism_eq_nerve (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X) (τ : m ⟶ ⦋1⦌) :
    tensorUnitFirstRowPrism X r A τ =
      nerveCylinderDiagram (whiskerLeft A (tensorUnitFirstRowAutomorphism X r).hom) τ :=
  (nerveCylinderDiagram_whiskerLeft (tensorUnitFirstRowAutomorphism X r).hom A τ).symm

/-- The whole coefficient edge, including every crossing, respects the actual first-row iso. -/
def tensorUnitFirstRowPrismIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X) (τ : m ⟶ ⦋1⦌) :
    tensorUnitFirstRowPrism X r A τ ≅
      nerveCylinderDiagram (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom) τ ⋙
        oneEmbedding (boundedFlatPerfectWaldhausen X) := by
  let η := whiskerLeft A (tensorUnitFirstRowAutomorphism X r).hom
  let η' := whiskerRight
    (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom)
    (oneEmbedding (boundedFlatPerfectWaldhausen X))
  let e := Functor.isoWhiskerLeft A (tensorUnitFirstRowIso X)
  have h : η ≫ e.hom = e.hom ≫ η' := by
    apply NatTrans.ext
    funext p
    exact congrArg (fun α => α.app (A.obj p))
      (tensorUnitFirstRowAutomorphism_comparison X r)
  exact eqToIso (tensorUnitFirstRowPrism_eq_nerve X r A τ) ≪≫
    nerveCylinderDiagramIso η η' e e h τ ≪≫
      eqToIso (iteratedNerveCylinderDiagram_postcomp
        (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom)
        (oneEmbedding (boundedFlatPerfectWaldhausen X)) τ)

/-- The full first-row tensor prism preserves all original second-grid quotient conditions. -/
theorem tensorUnitFirstRowPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (hA : IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).cof
      (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).weq
      (tensorUnitFirstRowPrism X r A τ) := by
  rw [tensorUnitFirstRowPrism_eq_nerve]
  exact nerveCylinderDiagram_isSimplex₂
    (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌) _
    (fun _ => (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).weq_iso _ inferInstance)
    (tensorUnitFirstRow_grid X A hA) (tensorUnitFirstRow_grid X A hA) τ

/-- Restrict the actual first coefficient row by a parameter independent of nerve and input grid. -/
def tensorUnitCoefficientPrism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedFlatPerfectWaldhausen X) k :=
  tensorUnitFirstRowPrism X r A τ ⋙ reindex (boundedFlatPerfectWaldhausen X) θ

/-- The whole first coefficient slice is the actual tensor prism with the original suspension row.
-/
def tensorUnitCoefficientPrismIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitCoefficientPrism X r A τ θ ≅
      nerveCylinderDiagram (whiskerLeft A (boundedFlatPerfectTensorUnitAutomorphism X r).hom) τ ⋙
        suspensionRow (boundedFlatPerfectWaldhausen X) θ :=
  Functor.isoWhiskerRight (tensorUnitFirstRowPrismIso X r A τ)
    (reindex (boundedFlatPerfectWaldhausen X) θ)

/-- Every coefficient ordinal restriction remains exact on the entire second-input prism. -/
theorem tensorUnitCoefficientPrism_isSimplex₂ (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (hA : IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq A) (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    IsSimplex₂ (waldhausenStructure (boundedFlatPerfectWaldhausen X) k).cof
      (waldhausenStructure (boundedFlatPerfectWaldhausen X) k).weq
      (tensorUnitCoefficientPrism X r A τ θ) :=
  (tensorUnitFirstRowPrism_isSimplex₂ X r A hA τ).postcomp _ _
    (reindex_exact (boundedFlatPerfectWaldhausen X) θ)

/-- First-S reindexing changes only the displayed coefficient-row parameter. -/
theorem tensorUnitCoefficientPrism_reindex (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {l k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) (α : l ⟶ k) :
    tensorUnitCoefficientPrism X r A τ (α ≫ θ) =
      tensorUnitCoefficientPrism X r A τ θ ⋙ reindex (boundedFlatPerfectWaldhausen X) α := by
  rw [tensorUnitCoefficientPrism, reindex_comp]
  rfl

/-- Both coefficient object-row endpoints carry their actual tensor-zero isomorphisms. -/
def tensorUnitCoefficientPrismEndpointIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (τ : m ⟶ ⦋1⦌) (c : Fin 2) :
    tensorUnitCoefficientPrism X r A τ (SimplexCategory.const k ⦋1⦌ c) ≅
      (Functor.const (Grid₂ n m)).obj (QuotientRows.zero (boundedFlatPerfectWaldhausen X) k) :=
  tensorUnitCoefficientPrismIso X r A τ (SimplexCategory.const k ⦋1⦌ c) ≪≫
    eqToIso (by rw [suspensionRow_const]; rfl)

end Quillen.PerfectComplexes

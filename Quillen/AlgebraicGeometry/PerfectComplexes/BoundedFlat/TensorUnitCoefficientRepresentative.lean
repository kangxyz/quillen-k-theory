/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientSingle
public import Quillen.Waldhausen.GrothendieckComparison.WeakRelations

/-!
# The actual coefficient square and the original weak one-row representative

The actual single of the coefficient automorphism acts on the independently constructed
coefficient row. Transporting its two endpoints by the displayed zero/identity/zero row
isomorphism gives exactly the original `oneWeakArrow` of the forward unit automorphism.
This identifies the whole quotient/nerve square before applying any realization or K-one class map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- Apply the actual degree-zero single to every map of the original coefficient automorphism. -/
def tensorUnitCoefficientSingleAutomorphism (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientSingle X ≅ tensorUnitCoefficientSingle X :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerRight (tensorUnitCoefficientRowAutomorphism X r)
      (CochainComplex.singleFunctor X.Modules 0))

/-- Faithful inclusion retains the actual single map at each coefficient interval position. -/
theorem tensorUnitCoefficientSingleAutomorphism_original (X : Scheme.{u})
    (r : (Γ(X, ⊤))ˣ) (p : Interval ⦋1⦌) :
    (boundedFlatPerfect X).ι.map ((tensorUnitCoefficientSingleAutomorphism X r).hom.app p) =
      (CochainComplex.singleFunctor X.Modules 0).map
        ((tensorUnitCoefficientRowAutomorphism X r).hom.app p) := by
  simp only [tensorUnitCoefficientSingleAutomorphism, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]

/-- The coefficient single and canonical rank-one row have the same entire forward unit square. -/
theorem tensorUnitCoefficientSingleAutomorphism_comparison (X : Scheme.{u})
    (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitCoefficientSingleAutomorphism X r).hom ≫ (tensorUnitCoefficientSingleIso X).hom =
      (tensorUnitCoefficientSingleIso X).hom ≫
        ((oneEmbedding (boundedFlatPerfectWaldhausen X)).map
          (boundedFlatRankOneUnit X r).hom).hom := by
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact (tensorUnitCoefficientSingle_zero X 0).eq_of_src _ _
  | exact (tensorUnitCoefficientSingle_zero X 1).eq_of_src _ _
  | change (tensorUnitCoefficientSingleAutomorphism X r).hom.app
        (interval 0 1 (by decide)) ≫ 𝟙 _ = 𝟙 _ ≫ (boundedFlatRankOneUnit X r).hom
    simp only [Category.comp_id, Category.id_comp]
    apply (boundedFlatPerfect X).ι.map_injective
    rw [tensorUnitCoefficientSingleAutomorphism_original]
    rfl

/-- The displayed actual zero isomorphisms normalize the original coefficient-row square. -/
def tensorUnitCoefficientNormalizedArrow (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (oneEmbedding (boundedFlatPerfectWaldhausen X)).obj (boundedFlatRankOne X) ⟶
      (oneEmbedding (boundedFlatPerfectWaldhausen X)).obj (boundedFlatRankOne X) :=
  (objects (boundedFlatPerfectWaldhausen X) ⦋1⦌).homMk
    ((tensorUnitCoefficientSingleIso X).inv ≫
      (tensorUnitCoefficientSingleAutomorphism X r).hom ≫ (tensorUnitCoefficientSingleIso X).hom)

/-- Normalization gives exactly the original one-row map of the original forward unit. -/
theorem tensorUnitCoefficientNormalizedArrow_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientNormalizedArrow X r =
      (oneEmbedding (boundedFlatPerfectWaldhausen X)).map (boundedFlatRankOneUnit X r).hom := by
  apply ObjectProperty.hom_ext
  change (tensorUnitCoefficientSingleIso X).inv ≫
      ((tensorUnitCoefficientSingleAutomorphism X r).hom ≫
        (tensorUnitCoefficientSingleIso X).hom) = _
  rw [tensorUnitCoefficientSingleAutomorphism_comparison]
  simp

/-- The original coefficient square is pointwise weak after its displayed zero normalization. -/
def tensorUnitCoefficientWeakArrow (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (⟨(oneEmbedding (boundedFlatPerfectWaldhausen X)).obj
      (boundedFlatRankOne X)⟩ : WeakRows (boundedFlatPerfectWaldhausen X) ⦋1⦌) ⟶
    ⟨(oneEmbedding (boundedFlatPerfectWaldhausen X)).obj (boundedFlatRankOne X)⟩ :=
  ⟨tensorUnitCoefficientNormalizedArrow X r, by
    rw [tensorUnitCoefficientNormalizedArrow_eq]
    exact (oneEmbedding_exact (boundedFlatPerfectWaldhausen X)).weak _
      ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)⟩

/-- The weak coefficient arrow is the pre-existing original automorphism representative. -/
theorem tensorUnitCoefficientWeakArrow_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientWeakArrow X r =
      (boundedFlatPerfectWaldhausen X).oneWeakArrow (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) := by
  apply WideSubcategory.hom_ext
  exact tensorUnitCoefficientNormalizedArrow_eq X r

/-- The entire original coefficient quotient/nerve square, not merely its middle automorphism. -/
def tensorUnitCoefficientSquare (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (sSet (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq) _⦋1⦌ :=
  ⟨weakChainToGrid (boundedFlatPerfectWaldhausen X)
      (ComposableArrows.mk₁ (tensorUnitCoefficientWeakArrow X r)),
    (isSimplex₂_diagonal_iff _ _ _).mp
      (weakChainToGrid_isSimplex₂ (boundedFlatPerfectWaldhausen X) _)⟩

/-- The normalized tensor coefficient square is exactly the original forward weak-object square. -/
theorem tensorUnitCoefficientSquare_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientSquare X r =
      (boundedFlatPerfectWaldhausen X).weakObjectSimplex (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) := by
  apply Subtype.ext
  change weakChainToGrid _ (ComposableArrows.mk₁ _) = _
  rw [tensorUnitCoefficientWeakArrow_eq]
  rfl

end Quillen.PerfectComplexes

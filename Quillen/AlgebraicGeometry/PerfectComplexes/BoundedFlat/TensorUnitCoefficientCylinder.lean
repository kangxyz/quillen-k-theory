/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientNormalization

/-!
# The simplicial fixed coefficient tensor cell

The independently constructed coefficient row, after its two explicit zero normalizations, is
assembled into a genuine double simplicial cylinder. The first interval is the forward unit
nerve edge and the second is its first coefficient S-row. Equality with the original normalized
transformation cylinder followed by the original suspension cylinder proves all simplicial
operators simultaneously. Neither interval is transposed or identified with the other.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The original normalized tensor-pullback transformation cylinder. -/
def tensorUnitPullbackNormalizedCylinder :
    sSet (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq ⊗ Δ[1] ⟶
      sSet (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq :=
  weakNaturalTransformationCylinder _ _ (boundedFlatPerfectTensorUnitPullback_exact f).rebase
    (boundedFlatPerfectTensorUnitPullback_exact f).rebase
    (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
    (normalizedWeakTransformation_weak (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullback_exact f)
      (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom
      (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance))

/-- A genuine diagonal simplex of the actual normalized fixed coefficient cell. -/
def tensorUnitPullbackCoefficientSimplex (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedFlatPerfectWaldhausen Y).cof
      (boundedFlatPerfectWaldhausen Y).weq).obj n) (τ θ : (Δ[1]).obj n) :
    (doubleDiagonal (boundedFlatPerfectWaldhausen X)).obj n :=
  ⟨tensorUnitPullbackNormalizedCoefficientPrism f r A.val τ.down θ.down, by
    rw [tensorUnitPullbackNormalizedCoefficientPrism_eq]
    exact ((tensorUnitPullbackNormalizedCylinder f r).app n (A, τ)).property.postcomp
      (suspensionRow_exact (boundedFlatPerfectWaldhausen X) θ.down)⟩

/-- The entire actual cell is the original normalized unit prism with its first coefficient row. -/
theorem tensorUnitPullbackCoefficientSimplex_eq (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedFlatPerfectWaldhausen Y).cof
      (boundedFlatPerfectWaldhausen Y).weq).obj n) (τ θ : (Δ[1]).obj n) :
    tensorUnitPullbackCoefficientSimplex f r n A τ θ =
      (suspensionCylinder (boundedFlatPerfectWaldhausen X)).app n
        ((tensorUnitPullbackNormalizedCylinder f r).app n (A, τ), θ) := by
  apply Subtype.ext
  exact tensorUnitPullbackNormalizedCoefficientPrism_eq f r A.val τ.down θ.down

/-- Assemble the actual normalized fixed-cell values into the original simplicial double cylinder.
-/
def tensorUnitPullbackCoefficientCylinder :
    (sSet (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq ⊗ Δ[1]) ⊗
      Δ[1] ⟶ doubleDiagonal (boundedFlatPerfectWaldhausen X) where
  app n := ↾fun z => tensorUnitPullbackCoefficientSimplex f r n z.1.1 z.1.2 z.2
  naturality n m α := by
    ext z : 3
    have h := ConcreteCategory.congr_hom
      (((tensorUnitPullbackNormalizedCylinder f r ▷ Δ[1]) ≫
        suspensionCylinder (boundedFlatPerfectWaldhausen X)).naturality α) z
    change tensorUnitPullbackCoefficientSimplex f r m
        (((sSet (boundedFlatPerfectWaldhausen Y).cof
          (boundedFlatPerfectWaldhausen Y).weq).map α) z.1.1)
        (((Δ[1] : SSet).map α) z.1.2) (((Δ[1] : SSet).map α) z.2) =
      ((doubleDiagonal (boundedFlatPerfectWaldhausen X)).map α)
        (tensorUnitPullbackCoefficientSimplex f r n z.1.1 z.1.2 z.2)
    rw [tensorUnitPullbackCoefficientSimplex_eq, tensorUnitPullbackCoefficientSimplex_eq]
    exact h

/-- Equality of the whole simplicial fixed cell, including every quotient and nerve operator. -/
theorem tensorUnitPullbackCoefficientCylinder_eq :
    tensorUnitPullbackCoefficientCylinder f r =
      (tensorUnitPullbackNormalizedCylinder f r ▷ Δ[1]) ≫
        suspensionCylinder (boundedFlatPerfectWaldhausen X) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorUnitPullbackCoefficientSimplex_eq f r n z.1.1 z.1.2 z.2

end Quillen.PerfectComplexes

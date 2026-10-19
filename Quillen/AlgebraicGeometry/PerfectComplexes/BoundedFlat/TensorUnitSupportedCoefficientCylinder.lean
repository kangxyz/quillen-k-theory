/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientNormalization

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
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.obj.right, ⊤))ˣ)

/-- The original normalized tensor-pullback transformation cylinder. -/
def tensorSupportedPairNormalizedCylinder :
    sSet (boundedFlatPerfectSupportedWaldhausen T.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).weq ⊗ Δ[1] ⟶
      sSet (boundedFlatPerfectSupportedWaldhausen S.obj.hom).cof
        (boundedFlatPerfectSupportedWaldhausen S.obj.hom).weq :=
  weakNaturalTransformationCylinder _ _ (tensorSupportedPair_exact p).rebase
    (tensorSupportedPair_exact p).rebase
    (normalizedWeakTransformation (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom)
    (normalizedWeakTransformation_weak (tensorSupportedPair_exact p)
      (tensorSupportedPair_exact p)
      (tensorSupportedPairAutomorphism p r).hom
      (fun _ => (boundedFlatPerfectSupportedWaldhausen S.obj.hom).weq_iso _ inferInstance))

/-- A genuine diagonal simplex of the actual normalized fixed coefficient cell. -/
def tensorSupportedPairCoefficientSimplex (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedFlatPerfectSupportedWaldhausen T.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).weq).obj n) (τ θ : (Δ[1]).obj n) :
    (doubleDiagonal (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).obj n :=
  ⟨tensorSupportedPairNormalizedCoefficientPrism p r A.val τ.down θ.down, by
    rw [tensorSupportedPairNormalizedCoefficientPrism_eq]
    exact ((tensorSupportedPairNormalizedCylinder p r).app n (A, τ)).property.postcomp
      (suspensionRow_exact (boundedFlatPerfectSupportedWaldhausen S.obj.hom) θ.down)⟩

/-- The entire actual cell is the original normalized unit prism with its first coefficient row. -/
theorem tensorSupportedPairCoefficientSimplex_eq (n : SimplexCategoryᵒᵖ)
    (A : (sSet (boundedFlatPerfectSupportedWaldhausen T.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).weq).obj n) (τ θ : (Δ[1]).obj n) :
    tensorSupportedPairCoefficientSimplex p r n A τ θ =
      (suspensionCylinder (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).app n
        ((tensorSupportedPairNormalizedCylinder p r).app n (A, τ), θ) := by
  apply Subtype.ext
  exact tensorSupportedPairNormalizedCoefficientPrism_eq p r A.val τ.down θ.down

/-- Assemble the actual normalized fixed-cell values into the original simplicial double cylinder.
-/
def tensorSupportedPairCoefficientCylinder :
    (sSet (boundedFlatPerfectSupportedWaldhausen T.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).weq ⊗ Δ[1]) ⊗
      Δ[1] ⟶ doubleDiagonal (boundedFlatPerfectSupportedWaldhausen S.obj.hom) where
  app n := ↾fun z => tensorSupportedPairCoefficientSimplex p r n z.1.1 z.1.2 z.2
  naturality n m α := by
    ext z : 3
    have h := ConcreteCategory.congr_hom
      (((tensorSupportedPairNormalizedCylinder p r ▷ Δ[1]) ≫
        suspensionCylinder (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).naturality α) z
    change tensorSupportedPairCoefficientSimplex p r m
        (((sSet (boundedFlatPerfectSupportedWaldhausen T.obj.hom).cof
          (boundedFlatPerfectSupportedWaldhausen T.obj.hom).weq).map α) z.1.1)
        (((Δ[1] : SSet).map α) z.1.2) (((Δ[1] : SSet).map α) z.2) =
      ((doubleDiagonal (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).map α)
        (tensorSupportedPairCoefficientSimplex p r n z.1.1 z.1.2 z.2)
    rw [tensorSupportedPairCoefficientSimplex_eq, tensorSupportedPairCoefficientSimplex_eq]
    exact h

/-- Equality of the whole simplicial fixed cell, including every quotient and nerve operator. -/
theorem tensorSupportedPairCoefficientCylinder_eq :
    tensorSupportedPairCoefficientCylinder p r =
      (tensorSupportedPairNormalizedCylinder p r ▷ Δ[1]) ≫
        suspensionCylinder (boundedFlatPerfectSupportedWaldhausen S.obj.hom) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  exact tensorSupportedPairCoefficientSimplex_eq p r n z.1.1 z.1.2 z.2

end Quillen.PerfectComplexes

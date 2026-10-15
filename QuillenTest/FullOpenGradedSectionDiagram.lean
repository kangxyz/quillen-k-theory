/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionDiagram

/-! The graded diagram retains actual coefficient functors, zeros and fine-to-coarse squares. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenGradedSectionDiagram

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The graded Model map still has precisely the original section reindexing functor. -/
theorem original_coefficient_functor {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenGradedSectionModelMap j f).functor =
      boundedFlatAffineFullOpenSectionsMap j f := rfl

/-- The original coefficient map carries the inherited global zero to itself literally. -/
theorem original_coefficient_zero {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenGradedSectionModelMap j f).functor.obj
        (boundedFlatAffineFullOpenSectionZero j a) =
      boundedFlatAffineFullOpenSectionZero j b :=
  (boundedFlatAffineFullOpenGradedSectionModelMap j f).zero

/-- The actual original fine-to-grade square commutes as a square of Model arrows. -/
theorem original_change_weak_square {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineFullOpenSectionModelMap j f ≫
        boundedFlatAffineFullOpenSectionGradingModelMap j b =
      boundedFlatAffineFullOpenSectionGradingModelMap j a ≫
        boundedFlatAffineFullOpenGradedSectionModelMap j f :=
  (boundedFlatAffineFullOpenSectionGradingModelTransformation j).naturality f

/-- The genuine original iterated-S diagram retains coefficient composition strictly. -/
theorem original_prespectrum_coefficient_comp {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map (f ≫ g) =
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f ≫
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map g :=
  (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map_comp f g

end QuillenTest.FullOpenGradedSectionDiagram

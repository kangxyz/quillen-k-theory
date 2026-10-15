/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionModel

/-! Original inherited-zero, coefficient-square and structure-time consumers of full-open models. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.AffineOpenPair Quillen.Waldhausen.IteratedS
open scoped unitInterval
universe u
namespace QuillenTest.FullOpenSectionModel

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation
  boundedFlatAffineFullOpenSectionsMap

/-- The actual model zero evaluates to the specified original coarse restriction image. -/
theorem originalImageZero (a : Under R) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).obj
        (boundedFlatAffineFullOpenSectionModel j a).waldhausen.zero =
      boundedFlatAffineSectionFullOpenImageZero j a :=
  boundedFlatAffineFullOpenOriginalEvaluation_sectionZero j a

/-- An arbitrary original coefficient arrow retains that same literal chosen zero. -/
theorem originalCoefficientZero {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionModelMap j f).functor.obj
        (boundedFlatAffineFullOpenSectionModel j a).waldhausen.zero =
      (boundedFlatAffineFullOpenSectionModel j b).waldhausen.zero :=
  (boundedFlatAffineFullOpenSectionModelMap j f).zero

/-- The actual Model arrow retains the original coefficient functor. -/
theorem originalCoefficientFunctor {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineFullOpenSectionModelMap j f).functor =
      boundedFlatAffineFullOpenSectionsMap j f := rfl

/-- Evaluation of the unchanged coefficient functor retains its original pullback comparison. -/
theorem originalCoefficientSquare {a b : Under R} (f : a ⟶ b)
    {s t : BoundedFlatAffineFullOpenSections j a} (k : s ⟶ t) :
    (boundedFlatAffineFullOpenOriginalEvaluation j b).map
        ((boundedFlatAffineFullOpenSectionsMap j f).map k) ≫
        (boundedFlatAffineFullOpenSectionCoefficientIso j f).hom.app t =
      (boundedFlatAffineFullOpenSectionCoefficientIso j f).hom.app s ≫
        (boundedFlatPerfectPullback (openMap j f)).map
          ((boundedFlatAffineFullOpenOriginalEvaluation j a).map k) :=
  (boundedFlatAffineFullOpenSectionCoefficientIso j f).hom.naturality k

/-- The source and target coefficient arrows compose as the literal Model maps. -/
theorem originalCoefficientComposite {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    boundedFlatAffineFullOpenSectionModelMap j (f ≫ g) =
      boundedFlatAffineFullOpenSectionModelMap j f ≫
        boundedFlatAffineFullOpenSectionModelMap j g :=
  boundedFlatAffineFullOpenSectionModelMap_comp j f g

/-- The original iterated-S map preserves the structure path at every specified time. -/
theorem originalStructureTime {a b : Under R} (f : a ⟶ b) (n : ℕ)
    (x : (prespectrum (boundedFlatAffineFullOpenSectionModel j a)).space n) (t : I) :
    (prespectrumMap (boundedFlatAffineFullOpenSectionModelMap j f)).map (n+1)
        ((prespectrum (boundedFlatAffineFullOpenSectionModel j a)).structureMap n x t) =
      (prespectrum (boundedFlatAffineFullOpenSectionModel j b)).structureMap n
        ((prespectrumMap (boundedFlatAffineFullOpenSectionModelMap j f)).map n x) t := by
  exact congrArg (fun p => p t)
    ((prespectrumMap (boundedFlatAffineFullOpenSectionModelMap j f)).comm n x)

end QuillenTest.FullOpenSectionModel

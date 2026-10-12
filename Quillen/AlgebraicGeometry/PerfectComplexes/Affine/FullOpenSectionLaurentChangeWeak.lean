/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionDiagramLaurent
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingPrespectrum

/-!
# Original full-open Laurent tracks commute with changeWeak

The accepted identity-on-sections Model transformation preserves the same original forward-T
unit along the actual Laurent coefficient arrow. Its literal Model and automorphism squares
therefore preserve the complete iterated-S track at the identical action time. No contraction,
restriction comparison, or normalized localization null is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The actual changeWeak Model arrow preserves the original Laurent coefficient square. -/
theorem boundedFlatAffineFullOpenSectionLaurentChangeWeakModelSquare (a : Under R) :
    (boundedFlatAffineFullOpenSectionModelFunctor j).map
        ((laurentUnderCoefficient R).app a) ≫
        boundedFlatAffineFullOpenSectionGradingModelMap j ((laurentUnderFunctor R).obj a) =
      boundedFlatAffineFullOpenSectionGradingModelMap j a ≫
        (boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app a) :=
  (boundedFlatAffineFullOpenSectionGradingModelTransformation j).naturality
    ((laurentUnderCoefficient R).app a)

/-- The identity section functors intertwine the same forward-T automorphism literally. -/
theorem boundedFlatAffineFullOpenSectionLaurentChangeWeakUnitSquare (a : Under R) :
    Functor.whiskerRight
        (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a).hom
        (boundedFlatAffineFullOpenSectionGradingModelMap j
          ((laurentUnderFunctor R).obj a)).functor ≫
        eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenSectionLaurentChangeWeakModelSquare j a)) =
      eqToHom (congrArg Model.Hom.functor
          (boundedFlatAffineFullOpenSectionLaurentChangeWeakModelSquare j a)) ≫
        Functor.whiskerLeft (boundedFlatAffineFullOpenSectionGradingModelMap j a).functor
          (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom := by
  have he : Functor.whiskerRight (boundedFlatAffineFullOpenSectionLaurentUnitIso j a).hom
      (𝟭 (BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a))) =
      Functor.whiskerLeft
        (𝟭 (BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)))
        (boundedFlatAffineFullOpenSectionLaurentUnitIso j a).hom := by
    apply NatTrans.ext
    funext s
    simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.id_map, Functor.id_obj]
  exact Quillen.FunctorIdentityAutomorphism.onFunctor_whisker_square
    (C := BoundedFlatAffineFullOpenSections j a)
    (D := BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a))
    (E := BoundedFlatAffineFullOpenSections j a)
    (H := BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a))
    (boundedFlatAffineFullOpenSectionsMap j ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineFullOpenSectionsMap j ((laurentUnderCoefficient R).app a))
    (𝟭 (BoundedFlatAffineFullOpenSections j a))
    (𝟭 (BoundedFlatAffineFullOpenSections j ((laurentUnderFunctor R).obj a)))
    (eqToHom (congrArg Model.Hom.functor
      (boundedFlatAffineFullOpenSectionLaurentChangeWeakModelSquare j a)))
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a)
    (boundedFlatAffineFullOpenSectionLaurentUnitIso j a) he

/-- Every original action-time value survives the actual fine-to-graded prespectrum map. -/
theorem boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app
        ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n
        (t, ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a).map n x) :=
  prespectrumIsoHomotopy_square_apply
    ((boundedFlatAffineFullOpenSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineFullOpenSectionGradingModelMap j a)
    (boundedFlatAffineFullOpenSectionGradingModelMap j ((laurentUnderFunctor R).obj a))
    (boundedFlatAffineFullOpenSectionDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a)
    (boundedFlatAffineFullOpenSectionLaurentChangeWeakModelSquare j a)
    (boundedFlatAffineFullOpenSectionLaurentChangeWeakUnitSquare j a) n t x

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionDiagramLaurent
public import Quillen.Waldhausen.SConstruction.Iterated.EndotransformationContraction

/-!
# The chosen contraction of the actual quotient-graded Laurent track

The original chosen-zero endotransformation of the actual Laurent coefficient Model arrow
is weak because its two endpoint grades coincide. The accepted forward-T automorphism track
is literally the original transformation track, with the original isomorphism weakness proof.
The existing chosen endotransformation contraction therefore contracts this whole track,
relative to both action endpoints and the point line, with independent structure time.
No coefficient naturality, Bass-seed contraction, or localization-null comparison is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The actual chosen-zero endotransformation is weak in the original quotient grading. -/
theorem boundedFlatAffineFullOpenGradedSectionLaurentZero_weak (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenGradedSectionModel j
      ((laurentUnderFunctor R).obj a)).waldhausen.weq
      ((modelZeroEndotransformation
        ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
          ((laurentUnderCoefficient R).app a))).app S) := rfl

/-- The original forward-T track is exactly the transformation track of the same iso hom. -/
theorem boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy_eq_transformation
    (a : Under R) :
    boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a =
      prespectrumTransformationHomotopy
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
        (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
          ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
          (NatIso.hom_app_isIso
            (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S)) := rfl

/-- The existing chosen contraction contracts the unchanged whole graded Laurent self-track. -/
def boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).RelHomotopy
      (LoopPrespectrum.Homotopy.refl
        ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
          ((laurentUnderCoefficient R).app a))) :=
  prespectrumEndotransformationContraction
    ((boundedFlatAffineFullOpenGradedSectionModelFunctor j).map
      ((laurentUnderCoefficient R).app a))
    (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a).hom
    (fun S ↦ (boundedFlatAffineFullOpenGradedSectionModel j
      ((laurentUnderFunctor R).obj a)).waldhausen.weq_iso _
      (NatIso.hom_app_isIso
        (boundedFlatAffineFullOpenGradedSectionDiagramLaurentPullbackUnitIso j a) S))
    (boundedFlatAffineFullOpenGradedSectionLaurentZero_weak j a)

end Quillen.PerfectComplexes

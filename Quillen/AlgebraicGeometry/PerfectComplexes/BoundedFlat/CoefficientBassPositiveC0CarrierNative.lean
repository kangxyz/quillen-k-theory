/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierAttachment
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedRoutes

/-! Native evaluation of the original ordinary and shifted C0 projection strips. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Full finite product evaluation, with independent coefficient and projection times. -/
theorem positiveProjection_family_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (BassMReferences.middleNodes P p q) n
      (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
        StdSimplex.map BassProjectionPath.plusFace.toOrderHom
          (binaryPath (k := 2) 0 1 2 s)), x) =
    (boundedFlatCoefficientLaurentPlusHomotopy P c).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  rw [prespectrumFamily_eq, BassMReferences.middle_original]
  refine (CommonReferenceProduct.prespectrum_comp (BassMComponents.coefficientSource P p q)
    (fun i ↦ (BassMComponents.coefficientNodes P p q i).1)
    (fun i ↦ (BassMComponents.coefficientNodes P p q i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) n x
    (binaryPath (k := 2) 0 1 2 r)
    (StdSimplex.map BassProjectionPath.plusFace.toOrderHom
      (binaryPath (k := 2) 0 1 2 s))).trans ?_
  change prespectrumSimplexFamily (BassProjectionPath.simplex P c) n
    (StdSimplex.map BassProjectionPath.plusFace.toOrderHom (binaryPath (k := 2) 0 1 2 s),
      prespectrumSimplexFamily
        (ModelSimplex.ofIsos (BassMComponents.coefficientSource P p q)
          (fun i ↦ (BassMComponents.coefficientNodes P p q i).1)
          (fun i ↦ (BassMComponents.coefficientNodes P p q i).2)) n
        (binaryPath (k := 2) 0 1 2 r, x)) = _
  rw [BassMComponents.coefficient_native, prespectrumSimplexFamily_face,
    BassProjectionPath.plus_face]
  exact BinaryNormalizationSimplex.native_path _ _ n s _

/-- The actual compact carrier is evaluated without changing either geometric coordinate. -/
theorem positiveProjectionParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (positiveProjectionParameter P p q)
      n ((r, s), x) =
    (boundedFlatCoefficientLaurentPlusHomotopy P c).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (BassMReferences.middleNodes P p q)
    (r, s) (SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
      StdSimplex.map BassProjectionPath.plusFace.toOrderHom
        (binaryPath (k := 2) 0 1 2 s))) rfl n x).trans
    (positiveProjection_family_native P p q n r s x)

/-- Shifting the complete reference changes the attachment, while preserving this entire
native projection strip. This is diagram reanchoring, not inference from endpoint equality. -/
theorem shiftedProjectionParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (shiftedProjectionParameter P p q)
      n ((r, s), x) =
    (boundedFlatCoefficientLaurentPlusHomotopy P c).level n
      (s, (boundedFlatCoefficientCompositionHomotopy P p q).level n (r, x)) := by
  let z := SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 r,
    StdSimplex.map BassProjectionPath.plusFace.toOrderHom (binaryPath (k := 2) 0 1 2 s))
  have hp : shiftedProjectionParameter P p q (r, s) =
      parameter (laurentReference P p q)
        (fun i ↦ BassH0Merge.anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q)
          (BassMReferences.middleNodes P p q i)) z :=
    mapParameter_parameter (BassH0Merge.anchorNode
      (LaurentUnitReferenceSpecialization.commonUnit P p q))
      (BassMReferences.middleNodes P p q) z
  rw [compactPrespectrumFamily_eq_simplex _ _ _ (r, s) z hp n x, prespectrumFamily_eq]
  change prespectrumSimplexFamily
    (ModelSimplex.reanchorSimplex (LaurentUnitReferenceSpecialization.commonUnit P p q)
      (BassMReferences.middleNodes P p q)) n (z, x) = _
  rw [ModelSimplex.reanchorSimplex_eq, ← prespectrumFamily_eq]
  exact positiveProjection_family_native P p q n r s x

/-- Structure time is a third independent variable, for every n including zero. -/
theorem positiveProjectionParameter_structure (n : ℕ) (r s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P p q) (positiveProjectionParameter P p q)
      (n + 1) ((r, s),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
      (compactPrespectrumFamily (laurentReference P p q) (positiveProjectionParameter P p q)
        n ((r, s), x)) t :=
  compactPrespectrumFamily_structure _ _ n (r, s) x t

/-- The native zero-level input loop has its own independent coordinate. -/
theorem positiveProjectionParameter_zero_apply (r s t : I)
    (γ : Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c))))) from
      compactPrespectrumFamily (laurentReference P p q) (positiveProjectionParameter P p q)
        0 ((r, s), γ)) t =
    compactStageFamily (laurentReference P p q) 0 (positiveProjectionParameter P p q)
      ((r, s), γ t) :=
  compactPrespectrumFamily_zero_apply _ _ (r, s) γ t

variable (a : Under R)

/-- Keep the specific p;q=l source cast visible in the actual C0 specialization. -/
def actualCoefficientTrack : Quillen.LoopPrespectrum.Homotopy
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderCoefficient R).app a)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app a)) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((underToLaurent R).app a))) :=
  (boundedFlatCoefficientCompositionHomotopy P
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)).cast
      (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
        (polynomialUnderCoefficient_toLaurent R a)) rfl

/-- This casted original coefficient track is precisely the prescribed C0 native track. -/
theorem actualCoefficientTrack_level (n : ℕ) :
    (actualCoefficientTrack P a).level n =
      (boundedFlatCoefficientLaurentPlusHomotopy P a).level n := rfl

/-- Specialization retains the original C0 and the final-fiber positive projection,
independently. -/
theorem actualProjectionParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily
      (laurentReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      (positiveProjectionParameter P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a)) n ((r, s), x) =
    (boundedFlatCoefficientLaurentPlusHomotopy P ((laurentUnderFunctor R).obj a)).level n
      (s, (boundedFlatCoefficientLaurentPlusHomotopy P a).level n (r, x)) := by
  have h := positiveProjectionParameter_native P
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) n r s x
  change _ =
    (boundedFlatCoefficientLaurentPlusHomotopy P ((laurentUnderFunctor R).obj a)).level n
      (s, (actualCoefficientTrack P a).level n (r, x)) at h
  rw [actualCoefficientTrack_level] at h
  exact h

/-- The actual supportedRight C0 block has one reversal, on r alone; s is unchanged. -/
theorem actualProjectionParameter_reversed_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily
      (laurentReference P ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      (positiveProjectionParameter P
        ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a))
      n ((unitInterval.symm r, s), x) =
    (boundedFlatCoefficientLaurentPlusHomotopy P ((laurentUnderFunctor R).obj a)).level n
      (s, ((boundedFlatCoefficientLaurentPlusHomotopy P a).symm).level n (r, x)) :=
  actualProjectionParameter_native P a n (unitInterval.symm r) s x

end Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierNative

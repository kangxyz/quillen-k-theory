/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondStep

/-!
# The literal positive-cone support of the original coefficient Bass seed

The positive chart cone maps into the original two-chart cone by its strict inl/identity
square. This map preserves the whole original cone cylinder without a pause. The original
positive source null and the original forward-unit conjugate factor through it exactly.

The fixed first-step composition is restricted to this genuine support with its unchanged
moving-null-square construction. These support statements do not construct the mixed
C0/J0/C1 projection pasting required for the second tower transition.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual strict positive-chart square, with the original inl and identity target map. -/
def boundedFlatCoefficientBassPositiveConeSquare :
    Arrow.mk (boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ⟶
      Arrow.mk (boundedFlatCoefficientBassSquareComparison P a) :=
  Arrow.homMk
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) (𝟙 _)
    (by simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.comp_id,
      boundedFlatCoefficientBassSquareComparison] using
      (HomotopyPushout.inl_desc
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
        (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
        (boundedFlatCoefficientBassSquareHomotopy P a)))

/-- The positive subcone enters the original Bass cone by its literal strict square map. -/
def boundedFlatCoefficientBassPositiveConeInclusion :
    mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ⟶
      mappingCone (boundedFlatCoefficientBassSquareComparison P a) :=
  mappingConeMap (boundedFlatCoefficientBassPositiveConeSquare P a)

/-- The target inclusion remains the same Laurent inclusion, with no extra homotopy segment. -/
theorem boundedFlatCoefficientBassPositiveConeInclusion_inclusion :
    mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ≫
      boundedFlatCoefficientBassPositiveConeInclusion P a =
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- Every positive-cone cylinder point retains its own time and actual polynomial-chart point. -/
theorem boundedFlatCoefficientBassPositiveConeInclusion_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P a).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) := rfl

/-- The original positive composition and source projection null the same Laurent map already
inside the positive chart cone. -/
def boundedFlatCoefficientBassPositiveConeNull :
    Homotopy
      (boundedFlatPerfectPrespectrumMap (laurentProjection P a) ≫
        mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
      (zeroHom (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))
        (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))) := by
  have N := Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
  change Homotopy
    ((boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ≫
        mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
    (zeroHom _ _) at N
  exact ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).trans N

/-- The entire positive null factors to the original null with its two original time halves. -/
theorem boundedFlatCoefficientBassPositiveConeNull_factor (n : ℕ) :
    ((boundedFlatCoefficientBassPositiveConeNull P a).postcomp
      (boundedFlatCoefficientBassPositiveConeInclusion P a)).level n =
      (boundedFlatCoefficientBassLaurentNullHomotopy P a).level n := by
  change (((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P a))))
    |>.postcomp (boundedFlatCoefficientBassPositiveConeInclusion P a)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- This auxiliary factor uses exactly the original forward unit and positive null. Its image,
proved below, is the existing seed; it is not a new tower transition. -/
def boundedFlatCoefficientBassPositiveConeSeed :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      parameterLooping (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))) :=
  ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).nullLoopMap
    (boundedFlatCoefficientBassPositiveConeNull P a)

/-- The positive-cone factor gives literally the accepted original unit-conjugated seed. -/
theorem boundedFlatCoefficientBassPositiveConeSeed_factor :
    boundedFlatCoefficientBassPositiveConeSeed P a ≫
      parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P a) =
        boundedFlatCoefficientBassTransition P a := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))))
    (boundedFlatCoefficientBassPositiveConeInclusion P a)
    ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a))))
    ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)))
    (boundedFlatCoefficientBassPositiveConeNull P a)
    (boundedFlatCoefficientBassLaurentNullHomotopy P a)
    (fun _ ↦ rfl) (fun n ↦ boundedFlatCoefficientBassPositiveConeNull_factor P a n)
  simpa only [Category.id_comp, boundedFlatCoefficientBassPositiveConeSeed,
    boundedFlatCoefficientBassTransition] using h

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The fixed whole composition is restricted along the genuine strict positive-cone inclusion.
Its target and both endpoint maps are the original full cone maps. -/
def boundedFlatCoefficientBassPositiveConeComposition :=
  Homotopy.precomp (boundedFlatCoefficientBassPositiveConeInclusion P a)
    (BassMWhole.coneComposition P u v)

section BoundaryTemplate
variable {E F E' F' E'' F'' : LoopPrespectrum.{v}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a' : E ⟶ E') (b' : F ⟶ F') (c' : E' ⟶ E'') (d' : F' ⟶ F'')
  (H : Homotopy (f ≫ b') (a' ≫ g)) (K : Homotopy (g ≫ d') (c' ≫ h))
  {e : E ⟶ E''} {l : F ⟶ F''} (T : Homotopy (f ≫ l) (e ≫ h))
  (A : Homotopy e (a' ≫ c')) (B : Homotopy l (b' ≫ d'))
  (Q : T.Square (coneSquarePastedHomotopy f g h a' b' c' d' H K)
    (Homotopy.precomp f B) (A.postcomp h))

/-- The unchanged moving-null relative boundary, with an explicit type suitable for native
instantiation without unfolding geometric cube data. -/
def positiveSupportBoundaryTemplate :
    (mappingConeSquareNullHomotopy f h e l T).RelHomotopy
      (((Homotopy.precomp f (B.postcomp (mappingConeInclusion h))).trans
        (coneSquareCompositeNullHomotopy f g h a' b' c' d' H K)).trans
          (Quillen.LoopPrespectrum.Homotopy.refl (zeroHom E (mappingCone h))).symm) :=
  let J := coneSquareNullMovingSquare f h T
    (coneSquarePastedHomotopy f g h a' b' c' d' H K) A B Q
  let N := coneSquareCompositionNullComparison f g h a' b' c' d' H K
  J.toBoundary.trans
    (((Homotopy.RelHomotopy.refl
      (Homotopy.precomp f (B.postcomp (mappingConeInclusion h)))).hcomp N).hcomp
      (Homotopy.RelHomotopy.refl
        (Quillen.LoopPrespectrum.Homotopy.refl (zeroHom E (mappingCone h)))).symm)

/-- The abstract collapse identity prevents unfolding the entire native cube during elaboration. -/
theorem positiveSupportBoundaryTemplate_collapse (n : ℕ)
    (z : unitInterval × unitInterval) (x : E.space n) :
    (coneSquareCompositionMovingNullSquare f g h a' b' c' d' H K T A B Q).level n
      ((Quillen.ThreeSideSquare.collapse z).1, ((Quillen.ThreeSideSquare.collapse z).2, x)) =
    (positiveSupportBoundaryTemplate f g h a' b' c' d' H K T A B Q).level n
      (z.1, (z.2, x)) :=
  Homotopy.RelHomotopy.toSquare_collapse
    (positiveSupportBoundaryTemplate f g h a' b' c' d' H K T A B Q) n z x

end BoundaryTemplate

/-- The exact relative boundary used by the fixed composition on positive support. The whole
original comparison square is followed by its actual null-comparison reassociation. In
particular, this is not just the comparison square followed by the Laurent inclusion. -/
def boundedFlatCoefficientBassPositiveSupportBoundary :=
  positiveSupportBoundaryTemplate
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (BassMWhole.comparisonSquare P u v)

/-- The actual composition null square keeps the boundary-collapse and square-lift operations.
The independent cylinder time is not replaced by the comparison time. -/
def boundedFlatCoefficientBassPositiveSupportSquare :=
  coneSquareCompositionMovingNullSquare
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (BassMWhole.comparisonSquare P u v)

/-- The Laurent inclusion face is exactly the original Laurent composition homotopy. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_inclusion
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
      (r, (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).map n x) =
      (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, x) := rfl

/-- Every point of the positive cylinder uses the entire original moving-null square,
including its relative reassociation and square lift. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_cylinder
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
      (r, ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (s, x)) =
      (boundedFlatCoefficientBassPositiveSupportSquare P u v).level n
        (r, (s, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := rfl

/-- Pullback along the actual two-parameter collapse recovers the full relative boundary
pasting on positive support, with all its null-comparison pieces still present. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_cylinder_collapse
    (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
      ((Quillen.ThreeSideSquare.collapse z).1, ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n)
        ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatCoefficientBassPositiveSupportBoundary P u v).level n
        (z.1, (z.2, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  rw [boundedFlatCoefficientBassPositiveConeComposition_cylinder]
  exact positiveSupportBoundaryTemplate_collapse
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (BassMWhole.comparisonSquare P u v) n z _

/-- The chosen original seed only probes the genuine positive support of the fixed composition.
The output-loop coordinate remains independent of the composition coordinate. -/
theorem boundedFlatCoefficientBassPositiveConeComposition_seed
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
        (BassMWhole.stepComposition P u v)).level n (r, x)) s =
      (boundedFlatCoefficientBassPositiveConeComposition P u v).level n
        (r, Path.toContinuousMap
          ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x) s) := by
  have h := congrArg (fun k ↦ Path.toContinuousMap (k.map n x) s)
    (boundedFlatCoefficientBassPositiveConeSeed_factor P a)
  exact congrArg (fun y ↦ (BassMWhole.coneComposition P u v).level n (r, y)) h.symm

end Quillen.PerfectComplexes

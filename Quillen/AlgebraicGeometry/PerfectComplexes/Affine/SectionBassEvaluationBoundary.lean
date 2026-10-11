/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting

/-!
# The original strict-section Bass evaluation boundary

Cancel the common actual Laurent evaluation track in the two proved chart pastings. The
source is the original strict square's constant cylinder, and the target keeps both original
coefficient evaluation tracks and the original bounded-flat Bass cylinder.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The central two-chart boundary retains the original polynomial evaluation tracks. -/
def boundedFlatAffineSectionBassEvaluationBoundaryMiddle :
    Quillen.LoopPrespectrum.Homotopy
      ((boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedFlatPerfectPrespectrumMap (laurentPlus R))
      ((boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedFlatPerfectPrespectrumMap (laurentMinus R)) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : coefficient R ≫ kp = laurentCoefficient R :=
    coefficient_toLaurent R
  let hm : coefficient R ≫ km = laurentCoefficient R :=
    coefficient_toLaurent_invert R
  (boundedFlatAffineSectionChartSecondTrack R kp).trans
    ((((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatAffineSectionChartGeometricTrack R kp hp)).cast rfl
        (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
        (boundedFlatAffineSectionChartGeometricTrack R km hm)).cast rfl
          (Category.assoc _ _ _).symm)).trans
      (boundedFlatAffineSectionChartSecondTrack R km).symm)

/-- The explicit loop obtained by pasting the two original chart evaluation boundaries. -/
def boundedFlatAffineSectionBassEvaluationBoundaryTarget :
    Quillen.LoopPrespectrum.Homotopy
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : coefficient R ≫ kp = laurentCoefficient R :=
    coefficient_toLaurent R
  let hm : coefficient R ≫ km = laurentCoefficient R :=
    coefficient_toLaurent_invert R
  ((boundedFlatAffineSectionChartFirstTrack R kp hp).trans
    (boundedFlatAffineSectionBassEvaluationBoundaryMiddle R)).trans
      (boundedFlatAffineSectionChartFirstTrack R km hm).symm

/-- Both genuine Laurent-chart pastings cancel their one common evaluation track. -/
def boundedFlatAffineSectionBassEvaluationBoundary :
    (Quillen.LoopPrespectrum.Homotopy.refl
      (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).RelHomotopy
      (boundedFlatAffineSectionBassEvaluationBoundaryTarget R) :=
  let kp : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom Polynomial.toLaurent
  let km : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R) :=
    CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)
  let hp : coefficient R ≫ kp = laurentCoefficient R :=
    coefficient_toLaurent R
  let hm : coefficient R ≫ km = laurentCoefficient R :=
    coefficient_toLaurent_invert R
  Homotopy.RelHomotopy.pasteStrictSourceSquares
    (T := boundedFlatAffineSectionEvaluationCoefficientHomotopy (laurentCoefficient R))
    (Lp := boundedFlatAffineSectionChartFirstTrack R kp hp)
    (Pp := boundedFlatAffineSectionChartSecondTrack R kp)
    (Kp := (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatAffineSectionChartGeometricTrack R kp hp)).cast rfl
        (Category.assoc _ _ _).symm)
    (Lm := boundedFlatAffineSectionChartFirstTrack R km hm)
    (Pm := boundedFlatAffineSectionChartSecondTrack R km)
    (Km := (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatAffineSectionChartGeometricTrack R km hm)).cast rfl
        (Category.assoc _ _ _).symm)
    (boundedFlatAffineSectionChartFirstPasting R kp hp)
    (boundedFlatAffineSectionChartFirstPasting R km hm)

/-- The actual strict Bass cylinder is followed by unchanged original Laurent evaluation. -/
def boundedFlatAffineSectionBassEvaluationSourceTrack :=
  (StrictSquare.track (boundedFlatAffineSectionBassSquare R)).postcomp
    (boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))

/-- The target cylinder keeps the original polynomial evaluation tracks and raw Bass square. -/
def boundedFlatAffineSectionBassEvaluationTargetTrack :=
  ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R)).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus R))).trans
    (((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatBassSquareHomotopy R)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R)).postcomp
        (boundedFlatPerfectPrespectrumMap (laurentMinus R))).symm)

/-- The positive moving boundary retains the entire original Laurent coefficient track. -/
def boundedFlatAffineSectionBassEvaluationPlusTrack :=
  boundedFlatAffineSectionChartMovingTrack R (CommRingCat.ofHom Polynomial.toLaurent)

/-- The other moving boundary retains the distinct inverse-coordinate track. -/
def boundedFlatAffineSectionBassEvaluationMinusTrack :=
  boundedFlatAffineSectionChartMovingTrack R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

/-- The complete three-sided evaluation boundary has the exact moving-square association. -/
def boundedFlatAffineSectionBassEvaluationPastedTrack :=
  ((boundedFlatAffineSectionBassEvaluationPlusTrack R).trans
    (boundedFlatAffineSectionBassEvaluationTargetTrack R)).trans
      (boundedFlatAffineSectionBassEvaluationMinusTrack R).symm

/-- The boundary begins at the literal original constant strict-square cylinder. -/
theorem boundedFlatAffineSectionBassEvaluationSourceTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationSourceTrack R).level n =
      (Quillen.LoopPrespectrum.Homotopy.refl
        (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
          boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R)))).level n
        := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change (((boundedFlatAffineSectionBassSquare R).left.hom ≫
      (boundedFlatAffineSectionBassSquare R).hom.right) ≫
        boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n x =
    (boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))).map n x
  rw [boundedFlatAffineSectionBassSquare_source]
  rfl

/-- The middle geometric square keeps the two original Laurent chart tracks and their signs. -/
theorem boundedFlatAffineSectionBassEvaluationMiddleTrack_level (n : ℕ) :
    ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatBassSquareHomotopy R)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).level n =
    (((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
      (boundedFlatAffineSectionChartGeometricTrack R (CommRingCat.ofHom Polynomial.toLaurent)
        (coefficient_toLaurent R))).cast rfl
          (Category.assoc _ _ _).symm).symm.trans
      ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
        (boundedFlatAffineSectionChartGeometricTrack R
          (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
          (coefficient_toLaurent_invert R))).cast rfl
            (Category.assoc _ _ _).symm)).level n := by
  simp only [Homotopy.cast_level, boundedFlatBassSquareHomotopy,
    Homotopy.precomp_trans, Homotopy.precomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (boundedFlatAffineSectionChartGeometricTrack_plus R).symm
  · apply Homotopy.precomp_level_congr
    exact congrArg (fun H => H.level n) (boundedFlatAffineSectionChartGeometricTrack_minus R).symm

/-- The central boundary is the whole original target Bass comparison track. -/
theorem boundedFlatAffineSectionBassEvaluationTargetTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationTargetTrack R).level n =
      (boundedFlatAffineSectionBassEvaluationBoundaryMiddle R).level n := by
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · exact boundedFlatAffineSectionBassEvaluationMiddleTrack_level R n
    · rfl

/-- The positive moving side retains the original whole chart evaluation track. -/
theorem boundedFlatAffineSectionBassEvaluationPlusTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationPlusTrack R).level n =
      (boundedFlatAffineSectionChartFirstTrack R (CommRingCat.ofHom Polynomial.toLaurent)
        (coefficient_toLaurent R)).level n := rfl

/-- The negative moving side separately retains the whole inverse-coordinate chart track. -/
theorem boundedFlatAffineSectionBassEvaluationMinusTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationMinusTrack R).level n =
      (boundedFlatAffineSectionChartFirstTrack R
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
        (coefficient_toLaurent_invert R)).level n :=
  boundedFlatAffineSectionChartMovingTrack_level R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
    (coefficient_toLaurent_invert R) n

/-- The final boundary keeps both original coefficient tracks and the original Bass cylinder. -/
theorem boundedFlatAffineSectionBassEvaluationPastedTrack_level (n : ℕ) :
    (boundedFlatAffineSectionBassEvaluationPastedTrack R).level n =
      (boundedFlatAffineSectionBassEvaluationBoundaryTarget R).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · exact boundedFlatAffineSectionBassEvaluationPlusTrack_level R n
    · exact boundedFlatAffineSectionBassEvaluationTargetTrack_level R n
  · apply Homotopy.symm_level_congr
    exact boundedFlatAffineSectionBassEvaluationMinusTrack_level R n

/-- The proved chart geometry supplies the full original Bass evaluation pasted relation. -/
def boundedFlatAffineSectionBassEvaluationPasting :
    (boundedFlatAffineSectionBassEvaluationSourceTrack R).RelHomotopy
      (boundedFlatAffineSectionBassEvaluationPastedTrack R) :=
  (boundedFlatAffineSectionBassEvaluationBoundary R).ofLevels _ _
    (boundedFlatAffineSectionBassEvaluationSourceTrack_level R)
    (boundedFlatAffineSectionBassEvaluationPastedTrack_level R)

end Quillen.PerfectComplexes

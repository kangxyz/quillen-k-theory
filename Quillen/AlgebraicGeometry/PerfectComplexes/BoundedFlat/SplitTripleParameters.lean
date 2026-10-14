/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftOperations

/-! Actual compatible scalar surfaces for the six old triangles of one split triple. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

def leftFirstParameter := triangle (triangleFace 0 1 2 (by decide) (by decide))
def leftSecondParameter := triangle (triangleFace 2 3 7 (by decide) (by decide))
def normalizedLeftParameter := triangle (triangleFace 0 2 7 (by decide) (by decide))
def rightFirstParameter := triangle (triangleFace 0 4 5 (by decide) (by decide))
def rightSecondParameter := triangle (triangleFace 5 6 7 (by decide) (by decide))
def normalizedRightParameter := triangle (triangleFace 0 5 7 (by decide) (by decide))

/-- The fully split left path has precisely the old two-by-two association. -/
def splitLeftPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 7) :=
  ((edge 0 1).trans (edge 1 2)).trans ((edge 2 3).trans (edge 3 7))

/-- The fully split right path retains its separate pair of old binary comparisons. -/
def splitRightPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 7) :=
  ((edge 0 4).trans (edge 4 5)).trans ((edge 5 6).trans (edge 6 7))

/-- An explicit compatible scalar lift candidate of the full old split-triple surface.
The six whole native triangle identities below are its geometric inputs. -/
def comparisonParameter : splitLeftPath.Homotopy splitRightPath :=
  (leftFirstParameter.hcomp leftSecondParameter).symm.trans
    ((normalizedLeftParameter.symm.trans normalizedRightParameter).trans
      (rightFirstParameter.hcomp rightSecondParameter))

theorem leftFirstParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (leftFirstParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftFirstGeometric f g h).hom (leftFirstNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (left_first_face f g h) n r s x

theorem leftSecondParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (leftSecondParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftSecondGeometric f g h).hom (leftSecondNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (left_second_face f g h) n r s x

theorem normalizedLeftParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (normalizedLeftParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (NormalizedTripleSimplex.leftFirst f g h).hom
        (NormalizedTripleSimplex.leftSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (normalized_left_face f g h) n r s x

theorem rightFirstParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (rightFirstParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightFirstGeometric f g h).hom (rightFirstNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (right_first_face f g h) n r s x

theorem rightSecondParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (rightSecondParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightSecondGeometric f g h).hom (rightSecondNormalization f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (right_second_face f g h) n r s x

theorem normalizedRightParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (normalizedRightParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (NormalizedTripleSimplex.rightFirst f g h).hom
        (NormalizedTripleSimplex.rightSecond f g h).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (normalized_right_face f g h) n r s x

end Quillen.PerfectComplexes.SplitTripleSimplex

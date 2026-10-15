/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassPasting

/-! The genuine coefficient Bass boundary, with original maps and prescribed associations. -/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The right-associated target cylinder retains both original polynomial-square tracks. -/
def boundedFlatBassCoefficientTargetTrack :=
  ((boundedFlatPolynomialSquareHomotopy f).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus S))).trans
    (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
      (boundedFlatBassSquareHomotopy S)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedFlatPolynomialSquareHomotopy f).symm.postcomp
        (boundedFlatPerfectPrespectrumMap (laurentMinus S))))

/-- The precise outer left association required by the moving-square conversion. -/
def boundedFlatBassCoefficientPastedTrack :=
  (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPlusSquareHomotopy f)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (boundedFlatBassCoefficientTargetTrack f)).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatMinusSquareHomotopy f)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- The initial boundary is the entire original Bass square under coefficient change. -/
theorem boundedFlatBassCoefficientBoundary_source_level (n : ℕ) :
    ((boundedFlatBassSquareHomotopy R).postcomp
      (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).level n =
      ((boundedFlatBassCoefficientBoundary f).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [boundedFlatBassSquareHomotopy, Homotopy.postcomp_trans, Homotopy.postcomp_symm]

/-- The constructed boundary ends at the original Bass target cylinder with exact associations. -/
theorem boundedFlatBassCoefficientBoundary_target_level (n : ℕ) :
    (boundedFlatBassCoefficientPastedTrack f).level n =
      ((boundedFlatBassCoefficientBoundary f).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold boundedFlatBassSquareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            rfl
          · rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm (boundedFlatPolynomialSquareHomotopy f)
              (boundedFlatPerfectPrespectrumMap (laurentMinus S)))
  · rfl

/-- The original Bass square satisfies the actual coefficient pasted-track relation. -/
def boundedFlatBassCoefficientPasting :
    ((boundedFlatBassSquareHomotopy R).postcomp
      (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).RelHomotopy
      (boundedFlatBassCoefficientPastedTrack f) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatBassCoefficientBoundary f) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      boundedFlatBassCoefficientBoundary_source_level f n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      boundedFlatBassCoefficientBoundary_target_level f n)

/-- Regroup the source endpoint maps to the literal span-comparison composition maps. -/
def boundedFlatBassCoefficientSourceDescTrack :=
  ((boundedFlatBassSquareHomotopy R).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the target endpoints to the literal polynomial-coefficient composite maps. -/
def boundedFlatBassCoefficientTargetDescTrack :=
  (boundedFlatBassCoefficientTargetTrack f).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The exact boundary now uses the untransported precompositions of both Laurent squares. -/
def boundedFlatBassCoefficientPastedDescTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPlusSquareHomotopy f)).trans (boundedFlatBassCoefficientTargetDescTrack f)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatMinusSquareHomotopy f)).symm

/-- The genuine geometric boundary filler in the exact moving-pushout descent interface. -/
def boundedFlatBassCoefficientDescPasting :
    (boundedFlatBassCoefficientSourceDescTrack f).RelHomotopy
      (boundedFlatBassCoefficientPastedDescTrack f) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatBassCoefficientPasting f) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · apply Homotopy.symm_level_congr
        rfl)

end Quillen.PerfectComplexes

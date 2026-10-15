/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutHomotopyStableEquivalence

/-!
# Actual Laurent whole-track pushout consumers

The original Laurent coefficient square, its unchanged corner maps and both independently
supplied whole tracks define the exact existing reduced-pushout map. Stable corners suffice,
including in negative degrees. Endpoint, entire cylinder and first-track interval values remain
literal, at every original level including zero.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassPushoutHomotopyStableEquivalence

open Quillen

/-- The original Laurent square at the actual finite section stage. -/
def originalLaurentSquare (i : ℕ) (R : CommRingCat.{u}) :
    Arrow (Arrow LoopPrespectrum.{u + 1}) :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R)

/-- The actual original coefficient map of Laurent squares. -/
def originalLaurentSquareMap (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    originalLaurentSquare i R ⟶ originalLaurentSquare i S :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.map f)

variable (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
  (Hf : Homotopy
    ((originalLaurentSquare i R).left.hom ≫ (originalLaurentSquareMap i f).left.right)
    ((originalLaurentSquareMap i f).left.left ≫ (originalLaurentSquare i S).left.hom))
  (Hg : Homotopy
    ((originalLaurentSquare i R).hom.left ≫ (originalLaurentSquareMap i f).right.left)
    ((originalLaurentSquareMap i f).left.left ≫ (originalLaurentSquare i S).hom.left))

/-- The existing whole-track map, with no strict-square replacement. -/
def originalWholeTrackMap : StrictSquare.span (originalLaurentSquare i R) ⟶
    StrictSquare.span (originalLaurentSquare i S) :=
  HomotopyPushout.mapOfHomotopies (originalLaurentSquare i R).left.hom
    (originalLaurentSquare i R).hom.left (originalLaurentSquare i S).left.hom
    (originalLaurentSquare i S).hom.left (originalLaurentSquareMap i f).left.left
    (originalLaurentSquareMap i f).left.right (originalLaurentSquareMap i f).right.left Hf Hg

/-- Actual stable coefficient corners preserve the same supplied-track Laurent pushout map. -/
theorem actual_whole_track_laurent_stable
    (ha : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (hb : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (hc : IsStableEquivalence (originalLaurentSquareMap i f).right.left) :
    IsStableEquivalence (originalWholeTrackMap i f Hf Hg) :=
  boundedFlatAffineSectionBass_wholeTrackPushout_isStableEquivalence i i
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).right.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).right.left
    _ _ _ _ _ _ _ Hf Hg ha hb hc

/-- The original whole-track map is invertible in every negative signed stable degree. -/
theorem actual_whole_track_negative_iso
    (ha : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (hb : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (hc : IsStableEquivalence (originalLaurentSquareMap i f).right.left) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map (originalWholeTrackMap i f Hf Hg)) :=
  actual_whole_track_laurent_stable i f Hf Hg ha hb hc _

/-- The actual right inclusion and the unchanged original corner map are retained literally. -/
theorem actual_whole_track_right_inclusion :
    HomotopyPushout.inr (originalLaurentSquare i R).left.hom (originalLaurentSquare i R).hom.left ≫
        originalWholeTrackMap i f Hf Hg =
      (originalLaurentSquareMap i f).right.left ≫ HomotopyPushout.inr
        (originalLaurentSquare i S).left.hom (originalLaurentSquare i S).hom.left :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ Hf Hg

/-- The complete cylinder records the first track, original overlap and reversed second track. -/
theorem actual_whole_track_cylinder (n : ℕ) (t : unitInterval)
    (x : (originalLaurentSquare i R).left.left.space n) :
    (originalWholeTrackMap i f Hf Hg).map n
      (HomotopyPushout.cylinder (originalLaurentSquare i R).left.hom
        (originalLaurentSquare i R).hom.left n (t, x)) =
      ((Hf.postcomp (HomotopyPushout.inl (originalLaurentSquare i S).left.hom
        (originalLaurentSquare i S).hom.left)).trans
          ((Homotopy.precomp (originalLaurentSquareMap i f).left.left
            (HomotopyPushout.glue (originalLaurentSquare i S).left.hom
              (originalLaurentSquare i S).hom.left)).trans
            (Hg.symm.postcomp (HomotopyPushout.inr (originalLaurentSquare i S).left.hom
              (originalLaurentSquare i S).hom.left)))).level n (t, x) := rfl

/-- Every original first-track value appears with its literal half-cylinder parameter. -/
theorem actual_whole_track_first_half (n : ℕ) (t : unitInterval)
    (x : (originalLaurentSquare i R).left.left.space n) :
    (originalWholeTrackMap i f Hf Hg).map n
      (HomotopyPushout.cylinder (originalLaurentSquare i R).left.hom
        (originalLaurentSquare i R).hom.left n
          (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) =
      (HomotopyPushout.inl (originalLaurentSquare i S).left.hom
        (originalLaurentSquare i S).hom.left).map n (Hf.level n (t, x)) :=
  HomotopyPushout.mapOfHomotopies_first_half _ _ _ _ _ _ _ Hf Hg n t x

end QuillenTest.SectionBassPushoutHomotopyStableEquivalence

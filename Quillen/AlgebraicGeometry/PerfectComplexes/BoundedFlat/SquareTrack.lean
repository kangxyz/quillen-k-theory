/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyThreeRoutes
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! Composition of actual bounded-flat pullback squares from genuine three-map coherence. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

namespace DoubleSquareTrack
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

include hq in
/-- The first commuting square identifies the two original triple composites. -/
theorem middle_eq : q' ≫ b ≫ p = c ≫ q ≫ p := by
  rw [← Category.assoc, ← hq, Category.assoc]

include hp hq in
/-- Both commuting squares identify the original outer triple composite. -/
theorem total_eq : (q' ≫ p') ≫ a = c ≫ q ≫ p := by
  rw [Category.assoc, ← hp]
  exact middle_eq p q q' b c hq

/-- The original sourceTotal track in the double-square diagram. -/
def sourceTotal :=
  boundedFlatPerfectPrespectrumCompHomotopy c (q ≫ p)

/-- The original sourceChart track in the double-square diagram. -/
def sourceChart :=
  (boundedFlatPerfectPrespectrumCompHomotopy q p).postcomp
  (boundedFlatPerfectPrespectrumMap c)

/-- The original firstIntermediate track in the double-square diagram. -/
def firstIntermediate :=
  (boundedFlatPerfectPrespectrumCompHomotopy (c ≫ q) p).cast
  (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc c q p)) rfl

/-- The original firstRestriction track in the double-square diagram. -/
def firstRestriction :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap p)
  (boundedFlatPerfectPrespectrumCompHomotopy c q)).cast rfl (Category.assoc _ _ _).symm

/-- The original middleTotal track in the double-square diagram. -/
def middleTotal :=
  (boundedFlatPerfectPrespectrumCompHomotopy q' (b ≫ p)).cast
  (congrArg boundedFlatPerfectPrespectrumMap (middle_eq p q q' b c hq)) rfl

/-- The original middleChart track in the double-square diagram. -/
def middleChart :=
  (boundedFlatPerfectPrespectrumCompHomotopy b p).postcomp
  (boundedFlatPerfectPrespectrumMap q')

/-- The original secondRestriction track in the double-square diagram. -/
def secondRestriction :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap p)
  (boundedFlatPerfectPrespectrumCompHomotopy q' b)).cast
  (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap p ≫
    boundedFlatPerfectPrespectrumMap k) hq.symm) (Category.assoc _ _ _).symm

/-- The original targetTotal track in the double-square diagram. -/
def targetTotal :=
  (boundedFlatPerfectPrespectrumCompHomotopy (q' ≫ p') a).cast
  (congrArg boundedFlatPerfectPrespectrumMap (total_eq p q p' q' a b c hp hq)) rfl

/-- The original targetChart track in the double-square diagram. -/
def targetChart :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap a)
  (boundedFlatPerfectPrespectrumCompHomotopy q' p')).cast rfl (Category.assoc _ _ _).symm

/-- The original lastRestriction track in the double-square diagram. -/
def lastRestriction :=
  ((boundedFlatPerfectPrespectrumCompHomotopy p' a).postcomp
  (boundedFlatPerfectPrespectrumMap q')).cast
  (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap k ≫
    boundedFlatPerfectPrespectrumMap q') hp.symm) rfl

/-- The first actual triple comparison, with the shared original route components. -/
def firstTriple : ((sourceTotal (p := p) (q := q) (c := c)).trans
      (sourceChart (p := p) (q := q) (c := c))).RelHomotopy
     ((firstIntermediate (p := p) (q := q) (c := c)).trans
      (firstRestriction (p := p) (q := q) (c := c))) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatTripleTrackComparison c q p) _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The middle comparison source retains its entire original level. -/
theorem middle_left_level (n : ℕ) :
    ((middleTotal p q q' b c hq).trans (middleChart p q' b)).level n =
      (boundedFlatTripleLeftTrack q' b p).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The middle comparison target uses only the actual commuting-square equation. -/
theorem middle_right_level (n : ℕ) :
    ((firstIntermediate p q c).trans (secondRestriction p q q' b c hq)).level n =
      (boundedFlatTripleRightTrack q' b p).level n := by
  apply Homotopy.trans_level_congr
  · change (boundedFlatPerfectPrespectrumCompHomotopy (c ≫ q) p).level n =
      (boundedFlatPerfectPrespectrumCompHomotopy (q' ≫ b) p).level n
    exact congrArg (fun k ↦ (boundedFlatPerfectPrespectrumCompHomotopy k p).level n) hq
  · rfl

/-- The middle actual triple comparison uses the genuine first commuting-square equation. -/
def middleTriple : ((middleTotal p q q' b c hq).trans (middleChart p q' b)).RelHomotopy
    ((firstIntermediate p q c).trans (secondRestriction p q q' b c hq)) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatTripleTrackComparison q' b p) _ _
    (middle_left_level p q q' b c hq) (middle_right_level p q q' b c hq)

/-- The last comparison source uses only the actual second commuting-square equation. -/
theorem last_left_level (n : ℕ) :
    ((middleTotal p q q' b c hq).trans (lastRestriction p p' q' a b hp)).level n =
      (boundedFlatTripleLeftTrack q' p' a).level n := by
  apply Homotopy.trans_level_congr
  · change (boundedFlatPerfectPrespectrumCompHomotopy q' (b ≫ p)).level n =
      (boundedFlatPerfectPrespectrumCompHomotopy q' (p' ≫ a)).level n
    exact congrArg (fun k ↦ (boundedFlatPerfectPrespectrumCompHomotopy q' k).level n) hp
  · rfl

/-- The last comparison target retains its entire original level. -/
theorem last_right_level (n : ℕ) :
    ((targetTotal p q p' q' a b c hp hq).trans (targetChart p' q' a)).level n =
      (boundedFlatTripleRightTrack q' p' a).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The last actual triple comparison uses the genuine second commuting-square equation. -/
def lastTriple :
    ((middleTotal p q q' b c hq).trans (lastRestriction p p' q' a b hp)).RelHomotopy
      ((targetTotal p q p' q' a b c hp hq).trans (targetChart p' q' a)) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatTripleTrackComparison q' p' a) _ _
    (last_left_level p q p' q' a b c hp hq) (last_right_level p q p' q' a b c hp hq)

end DoubleSquareTrack

/-- Three genuine geometric triple comparisons supply the actual double-square pasting filler. -/
def boundedFlatDoubleSquareTrackComparison
    {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :=
  Homotopy.RelHomotopy.threeRoutes
    (DoubleSquareTrack.firstTriple (p := p) (q := q) (c := c))
    (DoubleSquareTrack.middleTriple (p := p) (q := q) (q' := q') (b := b) (c := c) (hq := hq))
    (DoubleSquareTrack.lastTriple (p := p) (q := q) (p' := p') (q' := q')
      (a := a) (b := b) (c := c) (hp := hp) (hq := hq))

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyThreeRoutes
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Contravariant composition tracks and double squares

`ContravariantCompositionTracks` retains an object assignment, contravariant maps, their whole
binary composition homotopies, and a relative comparison of the two triple-composition routes.
It requires no identity law. Commuting squares give actual square homotopies by reversing one
binary track and following the other. Three supplied associativity cells then give
`projectionComparison`, the double-square pasting comparison through specified common projections.
All transports preserve entire continuous levels and the independent prespectrum structure time.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Quillen.LoopPrespectrum

/-- Contravariant maps with binary composition tracks and their whole associativity cells.
The associativity input compares the actual whiskered binary tracks, including both transports. -/
structure ContravariantCompositionTracks (C : Type v) [Category.{w} C] where
  /-- The prespectrum assigned to an object. -/
  obj : C → LoopPrespectrum.{u}
  /-- The contravariant map assigned to an arrow. -/
  map {X Y : C} (f : X ⟶ Y) : obj Y ⟶ obj X
  /-- The actual binary composition homotopy. -/
  composition {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (map (f ≫ g)) (map g ≫ map f)
  /-- A relative comparison of the two complete triple-composition routes. -/
  associativity {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    ((composition f (g ≫ h)).trans ((composition g h).postcomp (map f))).RelHomotopy
      (((composition (f ≫ g) h).trans
        (Homotopy.precomp (map h) (composition f g))).cast
          (congrArg map (Category.assoc f g h)) (Category.assoc _ _ _).symm)

namespace ContravariantCompositionTracks
variable {𝒞 : Type v} [Category.{w} 𝒞] (T : ContravariantCompositionTracks.{u} 𝒞)

/-- The first complete triple route, using the actual postcomposed binary track. -/
def tripleLeft {X Y Z W : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Homotopy (T.map (f ≫ g ≫ h)) ((T.map h ≫ T.map g) ≫ T.map f) :=
  (T.composition f (g ≫ h)).trans ((T.composition g h).postcomp (T.map f))

/-- The second complete triple route, with explicit category associativity transports. -/
def tripleRight {X Y Z W : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Homotopy (T.map (f ≫ g ≫ h)) ((T.map h ≫ T.map g) ≫ T.map f) :=
  ((T.composition (f ≫ g) h).trans (Homotopy.precomp (T.map h) (T.composition f g))).cast
    (congrArg T.map (Category.assoc f g h)) (Category.assoc _ _ _).symm

/-- A commuting square supplies the actual reversed-and-followed composition tracks. -/
def square {X Y Z W : 𝒞} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ W) (w : W ⟶ Z)
    (h : p ≫ v = q ≫ w) : Homotopy (T.map v ≫ T.map p) (T.map w ≫ T.map q) :=
  (T.composition p v).symm.trans
    ((T.composition q w).cast (congrArg T.map h).symm rfl)

variable {A B C A' B' C' : 𝒞}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

include hq in
/-- The lower commuting square identifies the middle triple composite. -/
theorem middle_eq : q' ≫ b ≫ p = c ≫ q ≫ p := by
  rw [← Category.assoc, ← hq, Category.assoc]

include hp hq in
/-- Both commuting squares identify the total triple composite. -/
theorem total_eq : (q' ≫ p') ≫ a = c ≫ q ≫ p := by
  rw [Category.assoc, ← hp]
  exact middle_eq p q q' b c hq

/-- The source total-composition track. -/
def sourceTotal : Homotopy (T.map (c ≫ q ≫ p)) (T.map (q ≫ p) ≫ T.map c) :=
  T.composition c (q ≫ p)

/-- The source chart-composition track, postcomposed by the restriction. -/
def sourceChart :
    Homotopy (T.map (q ≫ p) ≫ T.map c) ((T.map p ≫ T.map q) ≫ T.map c) :=
  (T.composition q p).postcomp (T.map c)

/-- The first intermediate track, retaining its association transport. -/
def firstIntermediate :
    Homotopy (T.map (c ≫ q ≫ p)) (T.map p ≫ T.map (c ≫ q)) :=
  (T.composition (c ≫ q) p).cast (congrArg T.map (Category.assoc c q p)) rfl

/-- The first restriction track, with its codomain explicitly associated. -/
def firstRestriction :
    Homotopy (T.map p ≫ T.map (c ≫ q)) ((T.map p ≫ T.map q) ≫ T.map c) :=
  (Homotopy.precomp (T.map p) (T.composition c q)).cast rfl (Category.assoc _ _ _).symm

/-- The middle total track, using the lower commuting-square equality. -/
def middleTotal : Homotopy (T.map (c ≫ q ≫ p)) (T.map (b ≫ p) ≫ T.map q') :=
  (T.composition q' (b ≫ p)).cast (congrArg T.map (middle_eq p q q' b c hq)) rfl

/-- The middle chart-composition track. -/
def middleChart :
    Homotopy (T.map (b ≫ p) ≫ T.map q') ((T.map p ≫ T.map b) ≫ T.map q') :=
  (T.composition b p).postcomp (T.map q')

/-- The second restriction track, transported by the lower commuting square. -/
def secondRestriction :
    Homotopy (T.map p ≫ T.map (c ≫ q)) ((T.map p ≫ T.map b) ≫ T.map q') :=
  (Homotopy.precomp (T.map p) (T.composition q' b)).cast
    (congrArg (fun k ↦ T.map p ≫ T.map k) hq.symm) (Category.assoc _ _ _).symm

/-- The target total-composition track, transported by both commuting squares. -/
def targetTotal :
    Homotopy (T.map (c ≫ q ≫ p)) (T.map a ≫ T.map (q' ≫ p')) :=
  (T.composition (q' ≫ p') a).cast
    (congrArg T.map (total_eq p q p' q' a b c hp hq)) rfl

/-- The target chart-composition track, precomposed by the restriction. -/
def targetChart :
    Homotopy (T.map a ≫ T.map (q' ≫ p')) ((T.map a ≫ T.map p') ≫ T.map q') :=
  (Homotopy.precomp (T.map a) (T.composition q' p')).cast rfl (Category.assoc _ _ _).symm

/-- The last restriction track, transported by the upper commuting square. -/
def lastRestriction :
    Homotopy (T.map (b ≫ p) ≫ T.map q') ((T.map a ≫ T.map p') ≫ T.map q') :=
  ((T.composition p' a).postcomp (T.map q')).cast
    (congrArg (fun k ↦ T.map k ≫ T.map q') hp.symm) rfl

/-- The first supplied associativity cell, with the shared route components. -/
def firstTriple :
    ((T.sourceTotal p q c).trans (T.sourceChart p q c)).RelHomotopy
      ((T.firstIntermediate p q c).trans (T.firstRestriction p q c)) :=
  Homotopy.RelHomotopy.ofLevels (T.associativity c q p) _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The middle route retains every point of the first triple route. -/
theorem middle_left_level (n : ℕ) :
    ((T.middleTotal p q q' b c hq).trans (T.middleChart p q' b)).level n =
      (T.tripleLeft q' b p).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The other middle route uses only the lower commuting-square equality. -/
theorem middle_right_level (n : ℕ) :
    ((T.firstIntermediate p q c).trans (T.secondRestriction p q q' b c hq)).level n =
      (T.tripleRight q' b p).level n := by
  apply Homotopy.trans_level_congr
  · change (T.composition (c ≫ q) p).level n = (T.composition (q' ≫ b) p).level n
    exact congrArg (fun k ↦ (T.composition k p).level n) hq
  · rfl

/-- The middle supplied associativity cell, preserving its whole levels. -/
def middleTriple :
    ((T.middleTotal p q q' b c hq).trans (T.middleChart p q' b)).RelHomotopy
      ((T.firstIntermediate p q c).trans (T.secondRestriction p q q' b c hq)) :=
  Homotopy.RelHomotopy.ofLevels (T.associativity q' b p) _ _
    (T.middle_left_level p q q' b c hq) (T.middle_right_level p q q' b c hq)

/-- The last comparison source uses only the upper commuting-square equality. -/
theorem last_left_level (n : ℕ) :
    ((T.middleTotal p q q' b c hq).trans (T.lastRestriction p p' q' a b hp)).level n =
      (T.tripleLeft q' p' a).level n := by
  apply Homotopy.trans_level_congr
  · change (T.composition q' (b ≫ p)).level n = (T.composition q' (p' ≫ a)).level n
    exact congrArg (fun k ↦ (T.composition q' k).level n) hp
  · rfl

/-- The last comparison target retains the complete second triple route. -/
theorem last_right_level (n : ℕ) :
    ((T.targetTotal p q p' q' a b c hp hq).trans (T.targetChart p' q' a)).level n =
      (T.tripleRight q' p' a).level n := by
  apply Homotopy.trans_level_congr <;> rfl

/-- The last supplied associativity cell, preserving its whole levels. -/
def lastTriple :
    ((T.middleTotal p q q' b c hq).trans (T.lastRestriction p p' q' a b hp)).RelHomotopy
      ((T.targetTotal p q p' q' a b c hp hq).trans (T.targetChart p' q' a)) :=
  Homotopy.RelHomotopy.ofLevels (T.associativity q' p' a) _ _
    (T.last_left_level p q p' q' a b c hp hq) (T.last_right_level p q p' q' a b c hp hq)

/-- Three associativity cells give the route-level double-square comparison. -/
def doubleSquareComparison :
    (((T.firstRestriction p q c).symm.trans (T.secondRestriction p q q' b c hq)).trans
      ((T.middleChart p q' b).symm.trans (T.lastRestriction p p' q' a b hp))).RelHomotopy
    ((T.sourceChart p q c).symm.trans
      (((T.sourceTotal p q c).symm.trans (T.targetTotal p q p' q' a b c hp hq)).trans
        (T.targetChart p' q' a))) :=
  Homotopy.RelHomotopy.threeRoutes (T.firstTriple p q c)
    (T.middleTriple p q q' b c hq) (T.lastTriple p q p' q' a b c hp hq)

/-- Paste the two original square tracks, retaining the explicit association. -/
def originalLeft :
    Homotopy ((T.map p ≫ T.map q) ≫ T.map c) ((T.map a ≫ T.map p') ≫ T.map q') :=
  ((Homotopy.precomp (T.map p) (T.square c q q' b hq)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((T.square b p p' a hp).postcomp (T.map q'))

/-- Compare through the source chart, original outer square, and target chart. -/
def originalRight :
    Homotopy ((T.map p ≫ T.map q) ≫ T.map c) ((T.map a ≫ T.map p') ≫ T.map q') :=
  (T.sourceChart p q c).symm.trans
    ((T.square c (q ≫ p) (q' ≫ p') a (total_eq p q p' q' a b c hp hq).symm).trans
      (T.targetChart p' q' a))

/-- The initial route retains both entire original square homotopies. -/
theorem originalLeft_level (n : ℕ) :
    (T.originalLeft p q p' q' a b c hp hq).level n =
      ((T.doubleSquareComparison p q p' q' a b c hp hq).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold originalLeft square
  rw [Homotopy.precomp_trans, Homotopy.precomp_symm,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr <;> rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The final route retains the entire original outer square homotopy. -/
theorem originalRight_level (n : ℕ) :
    (T.originalRight p q p' q' a b c hp hq).level n =
      ((T.doubleSquareComparison p q p' q' a b c hp hq).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold originalRight square
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- Double-square pasting for the actual exported square tracks. -/
def originalComparison :
    (T.originalLeft p q p' q' a b c hp hq).RelHomotopy
      (T.originalRight p q p' q' a b c hp hq) :=
  Homotopy.RelHomotopy.ofLevels (T.doubleSquareComparison p q p' q' a b c hp hq) _ _
    (by intro n; simpa using T.originalLeft_level p q p' q' a b c hp hq n)
    (by intro n; simpa using T.originalRight_level p q p' q' a b c hp hq n)

variable (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')

include hp hq hr hr' in
/-- The two commuting squares induce a square between the specified common projections. -/
theorem outer_eq : c ≫ r = r' ≫ a := by
  rw [← hr, ← hr']
  exact (total_eq p q p' q' a b c hp hq).symm

/-- The source chart-composition track, transported to its specified projection. -/
def sourceProjection : Homotopy (T.map r) (T.map p ≫ T.map q) :=
  (T.composition q p).cast (congrArg T.map hr) rfl

/-- The target chart-composition track, transported to its specified projection. -/
def targetProjection : Homotopy (T.map r') (T.map p' ≫ T.map q') :=
  (T.composition q' p').cast (congrArg T.map hr') rfl

/-- The entire outer square of specified common projections. -/
def outerProjectionSquare : Homotopy (T.map r ≫ T.map c) (T.map a ≫ T.map r') :=
  T.square c r r' a (outer_eq p q p' q' a b c hp hq r r' hr hr')

/-- The outer route retains both chart-composition tracks and the common projection square. -/
def reducedRight :
    Homotopy ((T.map p ≫ T.map q) ≫ T.map c) ((T.map a ≫ T.map p') ≫ T.map q') :=
  ((T.sourceProjection p q r hr).postcomp (T.map c)).symm.trans
    ((T.outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').trans
      ((Homotopy.precomp (T.map a) (T.targetProjection p' q' r' hr')).cast
        rfl (Category.assoc _ _ _).symm))

/-- Identifying projections preserves every point of the outer square track. -/
theorem outerProjectionSquare_level (n : ℕ) :
    (T.outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').level n =
      (T.square c (q ≫ p) (q' ≫ p') a (total_eq p q p' q' a b c hp hq).symm).level n := by
  unfold outerProjectionSquare square
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    exact congrArg (fun k ↦ (T.composition c k).level n) hr.symm
  · change (T.composition r' a).level n = (T.composition (q' ≫ p') a).level n
    exact congrArg (fun k ↦ (T.composition k a).level n) hr'.symm

/-- The reduced route preserves the full original comparison boundary. -/
theorem reducedRight_level (n : ℕ) :
    (T.reducedRight p q p' q' a b c hp hq r r' hr hr').level n =
      (T.originalRight p q p' q' a b c hp hq).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.postcomp_level_congr
    rfl
  · apply Homotopy.trans_level_congr
    · exact T.outerProjectionSquare_level p q p' q' a b c hp hq r r' hr hr' n
    · apply Homotopy.precomp_level_congr
      rfl

/-- Double-square pasting through specified common projections, using the whole triple cells. -/
def projectionComparison :
    (T.originalLeft p q p' q' a b c hp hq).RelHomotopy
      (T.reducedRight p q p' q' a b c hp hq r r' hr hr') :=
  Homotopy.RelHomotopy.ofLevels (T.originalComparison p q p' q' a b c hp hq) _ _
    (fun _ ↦ rfl) (T.reducedRight_level p q p' q' a b c hp hq r r' hr hr')

end ContravariantCompositionTracks
end Quillen.LoopPrespectrum

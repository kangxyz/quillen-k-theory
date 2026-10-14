/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrack

/-! One genuine common-reference diagram for the three native double-square triples.
Repeated slots are retained: this statement alone does not identify shared scalar boundaries. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes.DoubleSquareCommonSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The actual first square transports the middle triple's reference functor. -/
def middleSourceIso : (NormalizedTripleSimplex.sourceMap c q p).functor ≅
    (NormalizedTripleSimplex.sourceMap q' b p).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.middle_eq p q q' b c hq).symm)) AsSmall.up)

/-- Both actual square equations, with the displayed scheme association,
transport the last source. -/
def lastSourceIso : (NormalizedTripleSimplex.sourceMap c q p).functor ≅
    (NormalizedTripleSimplex.sourceMap q' p' a).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))) AsSmall.up)

/-- An existing exact functor equipped with its reference from the actual total source. -/
abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen A) ⟶
    modelOf (boundedFlatPerfectWaldhausen C'),
      (NormalizedTripleSimplex.sourceMap c q p).functor ≅ F.functor

/-- Each slot stores an actual existing exact functor and its displayed source isomorphism. -/
def nodes : Fin 24 → Node p q c := fun i ↦
  Fin.addCases (m := 8) (n := 16) (motive := fun _ ↦ Node p q c)
    (fun j ↦ ⟨SplitTripleSimplex.vertices c q p j, SplitTripleSimplex.references c q p j⟩)
    (fun j ↦ Fin.addCases (m := 8) (n := 8) (motive := fun _ ↦ Node p q c)
      (fun k ↦ ⟨SplitTripleSimplex.vertices q' b p k,
        middleSourceIso p q q' b c hq ≪≫ SplitTripleSimplex.references q' b p k⟩)
      (fun k ↦ ⟨SplitTripleSimplex.vertices q' p' a k,
        lastSourceIso p q p' q' a b c hp hq ≪≫ SplitTripleSimplex.references q' p' a k⟩) j) i

theorem first_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.castAdd 16 i) =
      ⟨SplitTripleSimplex.vertices c q p i, SplitTripleSimplex.references c q p i⟩ := by
  unfold nodes
  rw [Fin.addCases_left]

theorem middle_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 i)) =
      ⟨SplitTripleSimplex.vertices q' b p i,
        middleSourceIso p q q' b c hq ≪≫ SplitTripleSimplex.references q' b p i⟩ := by
  unfold nodes
  rw [Fin.addCases_right, Fin.addCases_left]

theorem last_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 i)) =
      ⟨SplitTripleSimplex.vertices q' p' a i,
        lastSourceIso p q p' q' a b c hp hq ≪≫ SplitTripleSimplex.references q' p' a i⟩ := by
  unfold nodes
  rw [Fin.addCases_right, Fin.addCases_right]

/-- A common 23-simplex contains all three eight-slot native comparison diagrams. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen A))
    (modelOf (boundedFlatPerfectWaldhausen C')) 23 :=
  ModelSimplex.ofIsos (NormalizedTripleSimplex.sourceMap c q p)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).1)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).2)

def firstFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.castAdd 16, fun _ _ h ↦ h⟩

def middleFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ Fin.natAdd 8 (Fin.castAdd 8 i), by
    intro i j hij
    exact Nat.add_le_add_left hij 8⟩

def lastFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ Fin.natAdd 8 (Fin.natAdd 8 i), by
    intro i j hij
    exact Nat.add_le_add_left (Nat.add_le_add_left hij 8) 8⟩

/-- The whole first original split-triple diagram is the displayed common face. -/
theorem first_face : (simplex p q p' q' a b c hp hq).face firstFace =
    SplitTripleSimplex.simplex c q p := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨SplitTripleSimplex.vertices c q p i, SplitTripleSimplex.references c q p i⟩)
    (first_nodes p q p' q' a b c hp hq)

/-- The whole middle diagram retains the first actual square equality in its reference. -/
theorem middle_face : (simplex p q p' q' a b c hp hq).face middleFace =
    SplitTripleSimplex.simplex q' b p := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨SplitTripleSimplex.vertices q' b p i,
      middleSourceIso p q q' b c hq ≪≫ SplitTripleSimplex.references q' b p i⟩)
    (middle_nodes p q p' q' a b c hp hq)).trans
      (ModelSimplex.ofIsos_change_reference (middleSourceIso p q q' b c hq) _ _)

/-- The whole last diagram retains both square equalities and the original association. -/
theorem last_face : (simplex p q p' q' a b c hp hq).face lastFace =
    SplitTripleSimplex.simplex q' p' a := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨SplitTripleSimplex.vertices q' p' a i,
      lastSourceIso p q p' q' a b c hp hq ≪≫ SplitTripleSimplex.references q' p' a i⟩)
    (last_nodes p q p' q' a b c hp hq)).trans
      (ModelSimplex.ofIsos_change_reference (lastSourceIso p q p' q' a b c hp hq) _ _)

end Quillen.PerfectComplexes.DoubleSquareCommonSimplex

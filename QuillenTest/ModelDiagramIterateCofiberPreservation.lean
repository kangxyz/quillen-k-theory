/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.ModelDiagramIterateCofiberPreservation

/-!
# Original iterated cofiber and whole-null consumers

These clients retain the supplied stage-zero track, every original successor point map and
cylinder time, same-time coefficient naturality, and signed boundary. The only stability input
is the initial original geometric cone descent. No finite-stage stabilization is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
universe u v w
namespace QuillenTest.ModelDiagramIterateCofiberPreservation

open Quillen
section WholeTracks
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}
    (H : DiagramNullHomotopy a b)

/-- Stage zero retains every value of the original supplied null homotopy. -/
theorem originalInitialTrack (X : C) (m : ℕ) (r : unitInterval) (x : (F.obj X).space m) :
    ((strictDiagramIterateNull Q H 0).homotopy X).level m (r, x) =
      (H.homotopy X).level m (r, x) := rfl

/-- Successors retain the original successor maps and identical whole Bass-null time. -/
theorem originalSuccessorTrack (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q (n + 1)).obj F).obj X).space m) :
    ((strictDiagramIterateNull Q H (n + 1)).homotopy X).level m (r, x) =
      ((inv (strictDiagramSuccessorMap Q K n)).app X).map m
        ((strictDiagramNullHomotopy ((strictDiagramIterate Q n).map a)
          ((strictDiagramIterate Q n).map b) (strictDiagramIterateNull Q H n).homotopy
          (strictDiagramIterateNull Q H n).naturality Q X).level m
            (r, ((strictDiagramSuccessorMap Q F n).app X).map m x)) :=
  strictDiagramIterateNull_succ_level Q H n X m r x

/-- The original successor cone transports source points without changing the cylinder height. -/
theorem originalSuccessorCylinder (n : ℕ) (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q (n + 1)).obj F).obj X).space m) :
    (strictDiagramSuccessorConeIso Q (a := a) n X).hom.map m
      (ReducedMappingCone.cylinder
        ((((strictDiagramIterate Q (n + 1)).obj F).obj X).point m)
        ((((strictDiagramIterate Q (n + 1)).obj G).obj X).point m)
        ((((strictDiagramIterate Q (n + 1)).map a).app X).map m) (r, x)) =
      ReducedMappingCone.cylinder
        ((((strictDiagramFunctor Q).obj ((strictDiagramIterate Q n).obj F)).obj X).point m)
        ((((strictDiagramFunctor Q).obj ((strictDiagramIterate Q n).obj G)).obj X).point m)
        ((((strictDiagramFunctor Q).map ((strictDiagramIterate Q n).map a)).app X).map m)
        (r, ((strictDiagramSuccessorMap Q F n).app X).map m x) := rfl

/-- All actual coefficient arrows commute with every iterated whole null track at the same time. -/
theorem originalCoefficientTrack (n : ℕ) {X Y : C} (f : X ⟶ Y) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q n).obj F).obj X).space m) :
    (((strictDiagramIterate Q n).obj K).map f).map m
        (((strictDiagramIterateNull Q H n).homotopy X).level m (r, x)) =
      ((strictDiagramIterateNull Q H n).homotopy Y).level m
        (r, (((strictDiagramIterate Q n).obj F).map f).map m x) :=
  (strictDiagramIterateNull Q H n).naturality f m r x
end WholeTracks

section Models
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F G K : C ⥤ Model.{w}) (a : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
    (b : G ⋙ prespectrumFunctor ⟶ K ⋙ prespectrumFunctor) (H : DiagramNullHomotopy a b)
    (hdesc : ∀ X, IsStableEquivalence
      (mappingConeDesc (a.app X) (b.app X) (H.homotopy X)))

include hdesc in
/-- Initial geometric excision supplies every signed stable bijection at every actual iterate. -/
theorem originalIteratedSignedBijective (n : ℕ) (X : C) (d : ℤ) :
    Function.Bijective ((stableHomotopyFunctor d).map
      (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
        (((strictDiagramIterate Q n).map b).app X)
        ((strictDiagramIterateNull Q H n).homotopy X))) := by
  let := modelDiagramIterateCofiberDesc_isStableEquivalence Q F G K a b H hdesc n X d
  exact ConcreteCategory.bijective_of_isIso _

include hdesc in
/-- Every negative signed degree is covered by the same unchanged iterated descent. -/
theorem originalIteratedNegativeBijective (n t : ℕ) (X : C) :
    Function.Bijective ((stableHomotopyFunctor (-((t : ℤ) + 1))).map
      (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
        (((strictDiagramIterate Q n).map b).app X)
        ((strictDiagramIterateNull Q H n).homotopy X))) :=
  originalIteratedSignedBijective Q F G K a b H hdesc n X (-((t : ℤ) + 1))

/-- The finite-stage signed boundary retains the original recursively specified fiber lift. -/
theorem originalIteratedBoundary (n : ℕ) (X : C) (d : ℤ)
    (x : stableHomotopyGroup (mappingCone (((strictDiagramIterate Q n).map a).app X)) (d + 1)) :
    stableFiberConnecting (((strictDiagramIterate Q n).map b).app X) d
        ((stableHomotopyFunctor (d + 1)).map
          (mappingConeDesc (((strictDiagramIterate Q n).map a).app X)
            (((strictDiagramIterate Q n).map b).app X)
            ((strictDiagramIterateNull Q H n).homotopy X)) x) =
      (stableHomotopyFunctor d).map (homotopyFiberLift
        (((strictDiagramIterate Q n).map b).app X) (((strictDiagramIterate Q n).map a).app X)
        ((strictDiagramIterateNull Q H n).homotopy X))
        (stableMappingConeConnecting (((strictDiagramIterate Q n).map a).app X)
          (modelDiagramIterateArrow_coneFiber_isStableEquivalence Q F G a n X) d x) :=
  ConcreteCategory.congr_hom (modelDiagramIterateCofiberDesc_connecting Q F G K a b H n X d) x
end Models
end QuillenTest.ModelDiagramIterateCofiberPreservation

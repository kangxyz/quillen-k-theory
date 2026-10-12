/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramCofiberDescent

/-!
# Prescribed original Bass null-descent consumers

These clients retain the original corner null tracks, all three cone/overlap times, the actual
loop parameter and coefficient map, and the original target inclusion. They do not infer any
seed-relative or signed double-boundary coherence from these literal quotient equalities.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Quillen.Tests.StrictDiagramCofiberDescent
section Square
variable {S T U : Arrow (Arrow LoopPrespectrum.{w})}
    (a : S ⟶ T) (b : T ⟶ U) {z : S ⟶ U} (H : StrictSquare.MapHomotopy (a ≫ b) z)
    (h00 : z.left.left = zeroHom S.left.left U.left.left)
    (h01 : z.left.right = zeroHom S.left.right U.left.right)
    (h10 : z.right.left = zeroHom S.right.left U.right.left)
    (h11 : z.right.right = zeroHom S.right.right U.right.right)

/-- The original corner cylinder is descended with the exact specified original null time. -/
theorem originalCornerNull (n : ℕ) (r : unitInterval) (x : S.left.left.space n) :
    ((StrictSquare.coneSquareDesc a b H h00 h01 h10 h11).left.left).map n
      (ReducedMappingCone.cylinder (S.left.left.point n) (T.left.left.point n)
        (a.left.left.map n) (r, x)) = H.source.level n (r, x) := rfl

/-- Cofiber time, intrinsic cone height and overlap height retain the specified original order. -/
theorem originalThreeCylinderTimes (n : ℕ) (r s q : unitInterval) (x : S.left.left.space n) :
    (mappingConeMap (strictSquareComparisonFunctor.map
      (StrictSquare.coneSquareDesc a b H h00 h01 h10 h11))).map n
        ((StrictSquare.coneInterchangeIso a).hom.map n
          (ReducedMappingCone.cylinder ((mappingCone (StrictSquare.comparison S)).point n)
            ((mappingCone (StrictSquare.comparison T)).point n)
            ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n)
            (r, ReducedMappingCone.cylinder ((StrictSquare.span S).point n)
              (S.right.right.point n) ((StrictSquare.comparison S).map n)
              (s, HomotopyPushout.cylinder S.left.hom S.hom.left n (q, x))))) =
      ReducedMappingCone.cylinder ((StrictSquare.span U).point n) (U.right.right.point n)
        ((StrictSquare.comparison U).map n)
        (s, HomotopyPushout.cylinder U.left.hom U.hom.left n (q, H.source.level n (r, x))) := rfl

/-- The actual Bass null endpoint casts retain the independent output-loop time at level zero. -/
theorem originalZeroLevelNullLoop (r t : unitInterval)
    (γ : Path ((mappingCone (StrictSquare.comparison S)).point 0)
      ((mappingCone (StrictSquare.comparison S)).point 0)) :
    Path.toContinuousMap
      ((StrictSquare.loopedConeNullHomotopy a b H h00 h01 h10 h11).level 0 (r, γ)) t =
        H.cone.level 0 (r, γ t) := rfl
end Square

section Diagram
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (b : G ⟶ K)
    (N : ∀ X, Homotopy (a.app X ≫ b.app X) (zeroHom (F.obj X) (K.obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (F.map f).map n x))

/-- The comparison retains each original coefficient map on every actual quotient class. -/
theorem originalCoefficientMap {X Y : C} (f : X ⟶ Y) (n : ℕ)
    (x : ((mappingConeDiagram ((KTheory.Bass.strictDiagramFunctor Q).map a)).obj X).space n) :
    ((KTheory.Bass.strictDiagramCofiberComparison Q a).app Y).map n
        (((mappingConeDiagram ((KTheory.Bass.strictDiagramFunctor Q).map a)).map f).map n x) =
      (((KTheory.Bass.strictDiagramFunctor Q).obj (mappingConeDiagram a)).map f).map n
        (((KTheory.Bass.strictDiagramCofiberComparison Q a).app X).map n x) :=
  congrArg (fun g ↦ g.map n x) ((KTheory.Bass.strictDiagramCofiberComparison Q a).naturality f)

/-- The actual Bass image of original descent equals descent of the unchanged entire Bass null. -/
theorem originalWholeDescent (X : C) (n : ℕ)
    (x : (mappingCone (((KTheory.Bass.strictDiagramFunctor Q).map a).app X)).space n) :
    (((KTheory.Bass.strictDiagramFunctor Q).map
      (mappingConeDescTransformation a b N hN)).app X).map n
        (((KTheory.Bass.strictDiagramCofiberComparison Q a).app X).map n x) =
      (mappingConeDesc (((KTheory.Bass.strictDiagramFunctor Q).map a).app X)
        (((KTheory.Bass.strictDiagramFunctor Q).map b).app X)
        (KTheory.Bass.strictDiagramNullHomotopy a b N hN Q X)).map n x :=
  congrArg (fun g ↦ g.map n x) (KTheory.Bass.strictDiagramCofiberComparison_desc Q a b N hN X)
end Diagram
end Quillen.Tests.StrictDiagramCofiberDescent

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleRightBinaryRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ReferenceRowTransport

/-! Both actual projection-rectangle right rows with their unchanged native reference transports. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)
  (F : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C'))
  (e : F.functor = (ProjectionReference.reference c r).functor)

def projectionNativeNode (i : Fin 18) :=
  ModelSimplex.reanchorNodes (F₀ := F) (F₁ := ProjectionReference.reference c r) (eqToIso e)
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr) i

def projectionFirstReference : F.functor ≅ (NormalizedTripleSimplex.sourceMap c q p).functor :=
  eqToIso e ≪≫ eqToIso (ProjectionReference.anchor p q c r hr)

def projectionMiddleReference : F.functor ≅ (NormalizedTripleSimplex.sourceMap q' b p).functor :=
  projectionFirstReference p q c r hr F e ≪≫ DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq

theorem projection_native_anchor (i : Fin 18) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e i =
      anchorNode (F₀ := F) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
        (projectionFirstReference p q c r hr F e)
        (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i) :=
  anchorNode_assoc (F₀ := F) (F₁ := ProjectionReference.reference c r)
    (F₂ := NormalizedTripleSimplex.sourceMap c q p)
    (eqToIso e) (eqToIso (ProjectionReference.anchor p q c r hr))
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i)

/-- Every full first-triple node is unchanged after its two actual reference transports. -/
theorem projection_first_nodes (i : Fin 8) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices c q p i,
      projectionFirstReference p q c r hr F e ≪≫ SplitTripleSimplex.references c q p i⟩ :
      Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C'),
        F.functor ≅ G.functor) := by
  refine (projection_native_anchor p q p' q' a b c hp hq r hr F e _).trans ?_
  exact anchorNode_congr (F₀ := F) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
    (projectionFirstReference p q c r hr F e)
    ((DoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq i).trans
      (DoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq i))

/-- Every full middle-triple node retains the original actual square-naturality source iso. -/
theorem projection_middle_nodes (i : Fin 8) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
    (⟨SplitTripleSimplex.vertices q' b p i,
      projectionMiddleReference p q q' b c hq r hr F e ≪≫ SplitTripleSimplex.references q' b p i⟩ :
      Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C'),
        F.functor ≅ G.functor) := by
  refine (projection_native_anchor p q p' q' a b c hp hq r hr F e _).trans ?_
  have hn := anchorNode_congr (F₀ := F) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
    (projectionFirstReference p q c r hr F e)
    ((DoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq i).trans
      (DoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq i))
  exact hn.trans (anchorNode_assoc (F₀ := F) (F₁ := NormalizedTripleSimplex.sourceMap c q p)
    (F₂ := NormalizedTripleSimplex.sourceMap q' b p)
    (projectionFirstReference p q c r hr F e)
    (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)
    ⟨SplitTripleSimplex.vertices q' b p i, SplitTripleSimplex.references q' b p i⟩)

/-- The first original right row is exactly its precomposed native binary normalization. -/
theorem projection_first_right_row (i : Fin 3) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preBinaryNodes F (normalizedMap p) c q
        (rightRowReference F c q p (projectionFirstReference p q c r hr F e)) i :=
  (projection_first_nodes p q p' q' a b c hp hq r hr F e (rightIndex i)).trans
    (triple_right_row F c q p (projectionFirstReference p q c r hr F e) i)

/-- The actual middle right row retains the native square equality before binary normalization. -/
theorem projection_middle_right_row (i : Fin 3) :
    projectionNativeNode p q p' q' a b c hp hq r hr F e
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preBinaryNodes F (normalizedMap p) q' b
        (rightRowReference F q' b p (projectionMiddleReference p q q' b c hq r hr F e)) i :=
  (projection_middle_nodes p q p' q' a b c hp hq r hr F e (rightIndex i)).trans
    (triple_right_row F q' b p (projectionMiddleReference p q q' b c hq r hr F e) i)

end Quillen.PerfectComplexes.BassH0Merge

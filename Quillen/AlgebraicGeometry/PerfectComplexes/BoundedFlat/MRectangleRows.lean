/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceBoundaryNodes

/-! Full native left and right rows of all three unchanged moving-rectangle triples. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Every original first-triple left row has its actual postcomposed binary references. -/
theorem rectangle_first_left_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := BinaryNormalizationSimplex.sourceMap q p)
      (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap c)
      (BinaryNormalizationSimplex.total c (q ≫ p)) (binaryNodes q p i) := by
  have hn : DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      tripleLeftNode (NormalizedTripleSimplex.sourceMap c q p) c q p rfl i := by
    fin_cases i <;> rfl
  exact hn.trans (triple_left_column (NormalizedTripleSimplex.sourceMap c q p) c q p rfl i)

/-- The entire first-triple right row keeps its canonical original normalization route. -/
theorem rectangle_first_right_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    preReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap p)
      (rightRowReference (NormalizedTripleSimplex.sourceMap c q p) c q p (Iso.refl _))
      (binaryNodes c q i) := by
  have hn : DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      tripleRightNode (NormalizedTripleSimplex.sourceMap c q p) c q p (Iso.refl _) i := by
    fin_cases i <;> rfl
  exact hn.trans (triple_right_row (NormalizedTripleSimplex.sourceMap c q p) c q p (Iso.refl _) i)

/-- The original middle-triple left row retains its actual source equality transport. -/
theorem rectangle_middle_left_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := BinaryNormalizationSimplex.sourceMap b p)
      (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap q')
      (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
        BinaryNormalizationSimplex.total q' (b ≫ p)) (binaryNodes b p i) :=
  ((DoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (DoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq (leftIndex i))).trans
      (triple_left_column_iso (NormalizedTripleSimplex.sourceMap c q p) q' b p
        (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

/-- The original middle-triple right row retains both original binary normalization pieces. -/
theorem rectangle_middle_right_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    preReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap p)
      (rightRowReference (NormalizedTripleSimplex.sourceMap c q p) q' b p
        (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq)) (binaryNodes q' b i) :=
  ((DoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (DoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq (rightIndex i))).trans
      (triple_right_row (NormalizedTripleSimplex.sourceMap c q p) q' b p
        (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i)

/-- The last-triple left row keeps the entire original two-square source equality. -/
theorem rectangle_last_left_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := BinaryNormalizationSimplex.sourceMap p' a)
      (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap q')
      (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
        BinaryNormalizationSimplex.total q' (p' ≫ a)) (binaryNodes p' a i) :=
  ((DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq (leftIndex i)).trans
    (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq (leftIndex i))).trans
      (triple_left_column_iso (NormalizedTripleSimplex.sourceMap c q p) q' p' a
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i)

/-- The last-triple right row keeps the original target composition triangle and its source. -/
theorem rectangle_last_right_nodes (i : Fin 3) :
    DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    preReferenceNode (NormalizedTripleSimplex.sourceMap c q p) (normalizedMap a)
      (rightRowReference (NormalizedTripleSimplex.sourceMap c q p) q' p' a
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq)) (binaryNodes q' p' i) :=
  ((DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq (rightIndex i)).trans
    (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq (rightIndex i))).trans
      (triple_right_row (NormalizedTripleSimplex.sourceMap c q p) q' p' a
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i)

end Quillen.PerfectComplexes.BassMOuterJoin

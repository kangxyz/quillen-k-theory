/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMovingSquarePause
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionChartRows
public import Quillen.Topology.Path.SimplexCollapsedEdges
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductSupport
public import Quillen.Topology.Path.ScalarPathCells

/-!
# Complete reference rows of the original coefficient moving square

The three five-node rows retain the actual geometric source transports and the original
binary normalization intermediates. Only their ordered primitive edges are used as faces.
The two moving side rows retain their complete references as well.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientMovingSquareRows
open BassH0Merge BassH1Join BassReferenceMerge

/-- The direct square keeps both binary paths in their original order. -/
def outerRow : Fin 5 → Fin 18 := ![0, 14, 15, 1, 2]

/-- The first composite half is the postcomposed first original square. -/
def firstRow : Fin 5 → Fin 18 := ![5, 7, 17, 6, 13]

/-- The second composite half is the precomposed second original square. -/
def secondRow : Fin 5 → Fin 18 := ![9, 12, 13, 10, 11]

/-- The source-composition side retains its original three binary nodes. -/
def sourceSide : Fin 3 → Fin 18 := ![2, 3, 11]

/-- The target-composition side retains its original three binary nodes. -/
def targetSide : Fin 3 → Fin 18 := ![15, 16, 17]

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

abbrev reference := NormalizedTripleSimplex.sourceMap c q p
abbrev nodes := DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq

private theorem first_triple_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices c q p i, SplitTripleSimplex.references c q p i⟩ :
        DoubleSquareCommonSimplex.Node p q c) :=
  (DoubleSquareMergedSimplex.first_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.first_nodes p q p' q' a b c hp hq i)

private theorem middle_triple_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (DoubleSquareMergedSimplex.middleFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices q' b p i,
        DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
          SplitTripleSimplex.references q' b p i⟩ : DoubleSquareCommonSimplex.Node p q c) :=
  (DoubleSquareMergedSimplex.middle_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.middle_nodes p q p' q' a b c hp hq i)

private theorem last_triple_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
      (⟨SplitTripleSimplex.vertices q' p' a i,
        DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
          SplitTripleSimplex.references q' p' a i⟩ : DoubleSquareCommonSimplex.Node p q c) :=
  (DoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
    (DoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i)

/-- The first square uses the original last-triple source transport before postcomposition. -/
def firstAnchor : (reference p q c).functor ≅
    (NativeSquareFiveSimplex.source p' a ≫ normalizedMap q').functor :=
  DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
    BinaryNormalizationSimplex.total q' (p' ≫ a)

/-- The second square uses the actual middle-triple transport before precomposition. -/
def secondAnchor : (reference p q c).functor ≅
    (normalizedMap p ≫ NativeSquareFiveSimplex.source q' b).functor :=
  DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
    NormalizedTripleSimplex.rightFirst q' b p

/-- Every node on the source-composition side is the original postcomposed binary node. -/
theorem source_side_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq (sourceSide i) =
      postReferenceNode (reference p q c) (normalizedMap c)
        (H := BinaryNormalizationSimplex.sourceMap q p)
        (BinaryNormalizationSimplex.total c (q ≫ p)) (binaryNodes q p i) := by
  have hi : sourceSide i = DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi, first_triple_nodes]
  simpa only [Iso.refl_trans] using
    triple_left_column_iso (reference p q c) c q p (Iso.refl _) i

/-- Every node on the target-composition side keeps the actual final source transport. -/
theorem target_side_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq (targetSide i) =
      preReferenceNode (reference p q c) (normalizedMap a)
        (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
          NormalizedTripleSimplex.rightFirst q' p' a) (binaryNodes q' p' i) := by
  have hi : targetSide i = DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi, last_triple_nodes]
  exact triple_right_row (reference p q c) q' p' a
    (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i

private theorem first_binary_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq
      (firstRow (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      postReferenceNode (reference p q c) (normalizedMap q')
        (firstAnchor p q p' q' a b c hp hq) (binaryNodes p' a i) := by
  have hi : firstRow (NativeSquareFiveSimplex.firstFace.toOrderHom i) =
      DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi, last_triple_nodes]
  exact triple_left_column_iso (reference p q c) q' p' a
    (DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq) i

private theorem first_other_binary_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq
      (firstRow (NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      postReferenceNode (reference p q c) (normalizedMap q')
        (H := BinaryNormalizationSimplex.sourceMap b p)
        (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq ≪≫
          BinaryNormalizationSimplex.total q' (b ≫ p)) (binaryNodes b p i) := by
  have hi : firstRow (NativeSquareFiveSimplex.secondFace.toOrderHom i) =
      DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi, middle_triple_nodes]
  exact triple_left_column_iso (reference p q c) q' b p
    (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i

private theorem second_binary_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq
      (secondRow (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      preReferenceNode (reference p q c) (normalizedMap p)
        (secondAnchor p q q' b c hq) (binaryNodes q' b i) := by
  have hi : secondRow (NativeSquareFiveSimplex.firstFace.toOrderHom i) =
      DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi, middle_triple_nodes]
  exact triple_right_row (reference p q c) q' b p
    (DoubleSquareCommonSimplex.middleSourceIso p q q' b c hq) i

private theorem second_other_binary_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq
      (secondRow (NativeSquareFiveSimplex.secondFace.toOrderHom i)) =
      preReferenceNode (reference p q c) (normalizedMap p)
        (NormalizedTripleSimplex.rightFirst c q p) (binaryNodes c q i) := by
  have hi : secondRow (NativeSquareFiveSimplex.secondFace.toOrderHom i) =
      DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i) := by
    fin_cases i <;> rfl
  rw [hi, first_triple_nodes]
  simpa only [tripleRightNode, rightRowReference, Iso.refl_trans,
    preBinaryNodes, preReferenceNode] using
    triple_right_row (reference p q c) c q p (Iso.refl _) i


/-- All five nodes of the first original square retain their postcomposition reference. -/
theorem first_row_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (firstRow i) =
      postReferenceNode (reference p q c) (normalizedMap q')
        (firstAnchor p q p' q' a b c hp hq)
        (NativeSquareFiveSimplex.nodes p' a b p hp.symm i) := by
  have hs (j : Fin 3) :
      nodes p q p' q' a b c hp hq
        (firstRow (NativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      postReferenceNode (reference p q c) (normalizedMap q')
        (firstAnchor p q p' q' a b c hp hq)
        (NativeSquareFiveSimplex.nodes p' a b p hp.symm
          (NativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    post_families_match (reference p q c) (normalizedMap q')
      (BinaryNormalizationSimplex.sourceMap b p) (binaryNodes b p)
      (first_other_binary_nodes p q p' q' a b c hp hq)
      (post_square_second_nodes p' a b p hp.symm (reference p q c) (normalizedMap q')
        (firstAnchor p q p' q' a b c hp hq)) 0
      (first_binary_nodes p q p' q' a b c hp hq 0) j
  fin_cases i
  · exact first_binary_nodes p q p' q' a b c hp hq 0
  · exact first_binary_nodes p q p' q' a b c hp hq 1
  · exact first_binary_nodes p q p' q' a b c hp hq 2
  · exact hs 1
  · exact hs 2

/-- All five nodes of the second original square retain their precomposition reference. -/
theorem second_row_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (secondRow i) =
      preReferenceNode (reference p q c) (normalizedMap p)
        (secondAnchor p q q' b c hq)
        (NativeSquareFiveSimplex.nodes q' b c q hq.symm i) := by
  have hs (j : Fin 3) :
      nodes p q p' q' a b c hp hq
        (secondRow (NativeSquareFiveSimplex.secondFace.toOrderHom j)) =
      preReferenceNode (reference p q c) (normalizedMap p)
        (secondAnchor p q q' b c hq)
        (NativeSquareFiveSimplex.nodes q' b c q hq.symm
          (NativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    pre_families_match (reference p q c) (normalizedMap p)
      (BinaryNormalizationSimplex.sourceMap c q) (binaryNodes c q)
      (second_other_binary_nodes p q p' q' a b c hp hq)
      (pre_square_second_nodes q' b c q hq.symm (reference p q c) (normalizedMap p)
        (secondAnchor p q q' b c hq)) 0
      (second_binary_nodes p q p' q' a b c hp hq 0) j
  fin_cases i
  · exact second_binary_nodes p q p' q' a b c hp hq 0
  · exact second_binary_nodes p q p' q' a b c hp hq 1
  · exact second_binary_nodes p q p' q' a b c hp hq 2
  · exact hs 1
  · exact hs 2

include hp hq in
/-- The direct-square source is transported by the actual outer geometric square equality. -/
theorem outerSourceEq : (reference p q c).functor =
    (NativeSquareFiveSimplex.source (q' ≫ p') a).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm)

/-- The whole direct row uses that literal equality transport, not an arbitrary chosen iso. -/
def outerAnchor := eqToIso (outerSourceEq p q p' q' a b c hp hq)

private theorem last_anchor_eq :
    DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq =
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback
          ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
            (Category.assoc q' p' a)))) := by
  apply Iso.ext
  simp only [DoubleSquareCommonSimplex.lastSourceIso, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, eqToIso.hom, whiskering_eqToHom]

private theorem right_raw_reference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    SplitTripleSimplex.rightFirstGeometric f g h =
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm)) ≪≫
        BinaryNormalizationSimplex.first (f ≫ g) h := by
  unfold SplitTripleSimplex.rightFirstGeometric BinaryNormalizationSimplex.first
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem right_normalized_reference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.rightFirst f g h =
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm)) ≪≫
        BinaryNormalizationSimplex.total (f ≫ g) h := by
  unfold NormalizedTripleSimplex.rightFirst BinaryNormalizationSimplex.total
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem outer_first_binary_nodes (i : Fin 3) :
    nodes p q p' q' a b c hp hq
      (outerRow (NativeSquareFiveSimplex.firstFace.toOrderHom i)) =
      anchorNode (outerAnchor p q p' q' a b c hp hq) (binaryNodes (q' ≫ p') a i) := by
  fin_cases i
  · change (⟨reference p q c, Iso.refl _⟩ : DoubleSquareCommonSimplex.Node p q c) =
      ⟨BinaryNormalizationSimplex.sourceMap (q' ≫ p') a,
        outerAnchor p q p' q' a b c hp hq ≪≫ Iso.refl _⟩
    apply ModelSimplex.reference_node_eq (outerSourceEq p q p' q' a b c hp hq)
    simp only [outerAnchor, Iso.refl_hom, Iso.trans_hom, eqToIso.hom,
      Category.id_comp, Category.comp_id]
  · have hn := last_triple_nodes p q p' q' a b c hp hq 4
    refine hn.trans ?_
    have hf : (SplitTripleSimplex.vertices q' p' a 4).functor =
        (binaryNodes (q' ≫ p') a 1).1.functor := rfl
    apply Sigma.ext (Model.Hom.ext hf)
    apply heq_of_eq
    change DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
      SplitTripleSimplex.rightFirstGeometric q' p' a =
        outerAnchor p q p' q' a b c hp hq ≪≫ BinaryNormalizationSimplex.first (q' ≫ p') a
    rw [last_anchor_eq, right_raw_reference, ← Iso.trans_assoc, eqToIso_trans]
    rfl
  · have hn := last_triple_nodes p q p' q' a b c hp hq 5
    refine hn.trans ?_
    have hf : (SplitTripleSimplex.vertices q' p' a 5).functor =
        (binaryNodes (q' ≫ p') a 2).1.functor := rfl
    apply Sigma.ext (Model.Hom.ext hf)
    apply heq_of_eq
    change DoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq ≪≫
      NormalizedTripleSimplex.rightFirst q' p' a =
        outerAnchor p q p' q' a b c hp hq ≪≫ BinaryNormalizationSimplex.total (q' ≫ p') a
    rw [last_anchor_eq, right_normalized_reference, ← Iso.trans_assoc, eqToIso_trans]
    rfl

private theorem outer_source_cancel :
    outerAnchor p q p' q' a b c hp hq ≪≫
      NativeSquareFiveSimplex.sourceIso (q' ≫ p') a c (q ≫ p)
        (DoubleSquareTrack.total_eq p q p' q' a b c hp hq) = Iso.refl _ := by
  change eqToIso _ ≪≫ eqToIso _ = Iso.refl _
  rw [eqToIso_trans]
  rfl

/-- All five complete direct-square nodes retain the actual outer geometric equality. -/
theorem outer_row_nodes (i : Fin 5) :
    nodes p q p' q' a b c hp hq (outerRow i) =
      anchorNode (outerAnchor p q p' q' a b c hp hq)
        (NativeSquareFiveSimplex.nodes (q' ≫ p') a c (q ≫ p)
          (DoubleSquareTrack.total_eq p q p' q' a b c hp hq) i) := by
  fin_cases i
  · exact outer_first_binary_nodes p q p' q' a b c hp hq 0
  · exact outer_first_binary_nodes p q p' q' a b c hp hq 1
  · exact outer_first_binary_nodes p q p' q' a b c hp hq 2
  · change (⟨BinaryNormalizationSimplex.intermediateMap c (q ≫ p),
      BinaryNormalizationSimplex.first c (q ≫ p)⟩ : DoubleSquareCommonSimplex.Node p q c) =
      ⟨BinaryNormalizationSimplex.intermediateMap c (q ≫ p),
        outerAnchor p q p' q' a b c hp hq ≪≫
          (NativeSquareFiveSimplex.sourceIso (q' ≫ p') a c (q ≫ p)
            (DoubleSquareTrack.total_eq p q p' q' a b c hp hq) ≪≫
            BinaryNormalizationSimplex.first c (q ≫ p))⟩
    rw [← Iso.trans_assoc, outer_source_cancel, Iso.refl_trans]
  · change (⟨BinaryNormalizationSimplex.targetMap c (q ≫ p),
      BinaryNormalizationSimplex.total c (q ≫ p)⟩ : DoubleSquareCommonSimplex.Node p q c) =
      ⟨BinaryNormalizationSimplex.targetMap c (q ≫ p),
        outerAnchor p q p' q' a b c hp hq ≪≫
          (NativeSquareFiveSimplex.sourceIso (q' ≫ p') a c (q ≫ p)
            (DoubleSquareTrack.total_eq p q p' q' a b c hp hq) ≪≫
            BinaryNormalizationSimplex.total c (q ≫ p))⟩
    rw [← Iso.trans_assoc, outer_source_cancel, Iso.refl_trans]

/-- Literal composite-map equalities retain every direct node and its original source cast. -/
theorem outer_row_nodes_cast (r : C ⟶ A) (r' : C' ⟶ A')
    (hr : r = q ≫ p) (hr' : r' = q' ≫ p') (h : r' ≫ a = c ≫ r) (i : Fin 5) :
    nodes p q p' q' a b c hp hq (outerRow i) =
      anchorNode (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback
          (h.trans (congrArg (fun k ↦ c ≫ k) hr)).symm)))
        (NativeSquareFiveSimplex.nodes r' a c r h i) := by
  subst r
  subst r'
  exact outer_row_nodes p q p' q' a b c hp hq i

/-- Each used primitive edge is ordered, even though none of the whole rows is ordered. -/
theorem primitive_rows_monotone (j : Fin 3) (i : Fin 4) :
    Monotone ((![outerRow, firstRow, secondRow] j) ∘ (BassH1Support.edgeFace i).toOrderHom) :=
  (by decide : ∀ (j : Fin 3) (i : Fin 4),
    Monotone ((![outerRow, firstRow, secondRow] j) ∘
      (BassH1Support.edgeFace i).toOrderHom)) j i

/-- The actual moving side rows are ordered binary faces. -/
theorem side_rows_monotone (j : Fin 2) : Monotone (![sourceSide, targetSide] j) :=
  (by decide : ∀ j : Fin 2, Monotone (![sourceSide, targetSide] j)) j

/-- The original direct row must not be treated as a globally monotone face. -/
theorem outerRow_not_monotone : ¬ Monotone outerRow := by decide

open DoubleSquareScalarPaths Quillen.NativePathCells

/-- Collapsing the actual original boundary retains the whole direct square path. -/
theorem moving_zero (s : unitInterval) :
    coefficientMovingSquareParameter (0, s) = outerSquarePath s :=
  collapsed_zero_path coefficientBoundaryParameter s

/-- The whole terminal path is precisely the original two-square concatenation. -/
theorem moving_one (s : unitInterval) :
    coefficientMovingSquareParameter (1, s) = originalComparisonSource s :=
  collapsed_top_path coefficientBoundaryParameter s

/-- The actual left moving side is the unchanged target-composition binary path. -/
theorem moving_left (q : unitInterval) :
    coefficientMovingSquareParameter (q, 0) = targetChart q :=
  collapsed_left_path coefficientBoundaryParameter q

/-- The actual right moving side is the unchanged source-composition binary path. -/
theorem moving_right (q : unitInterval) :
    coefficientMovingSquareParameter (q, 1) = sourceChart q :=
  collapsed_right_path coefficientBoundaryParameter q

private theorem comparison_source_eq : originalComparisonSource =
    ((lastRestriction.symm.trans middleChart).trans
      (secondRestriction.symm.trans firstRestriction)) := by
  simp only [originalComparisonSource, Path.trans_symm, Path.symm_symm]

/-- The full direct path factors through its actual nonmonotone five-node relabeling. -/
theorem moving_zero_row (s : unitInterval) :
    coefficientMovingSquareParameter (0, s) =
      StdSimplex.map outerRow (NativeSquareFiveSimplex.parameter s) := by
  rw [moving_zero]
  exact (BassSupportOrder.map_two_binary outerRow 0 1 2 3 4 s).symm

/-- The first terminal half keeps all four original edge segments at their old speed. -/
theorem moving_one_lower_row (s : unitInterval) :
    coefficientMovingSquareParameter (1, lower s) =
      StdSimplex.map firstRow (NativeSquareFiveSimplex.parameter s) := by
  rw [moving_one, comparison_source_eq, path_lower]
  exact (BassSupportOrder.map_two_binary firstRow 0 1 2 3 4 s).symm

/-- The second terminal half keeps its independent exact original parameter. -/
theorem moving_one_upper_row (s : unitInterval) :
    coefficientMovingSquareParameter (1, upper s) =
      StdSimplex.map secondRow (NativeSquareFiveSimplex.parameter s) := by
  rw [moving_one, comparison_source_eq, path_upper]
  exact (BassSupportOrder.map_two_binary secondRow 0 1 2 3 4 s).symm

/-- The whole right side retains its literal three-node parameter. -/
theorem moving_right_row (q : unitInterval) :
    coefficientMovingSquareParameter (q, 1) =
      StdSimplex.map sourceSide (binaryPath (k := 2) 0 1 2 q) := by
  rw [moving_right]
  exact (BassSupportOrder.map_any_binary sourceSide 0 1 2 q).symm

/-- The whole left side retains its literal three-node parameter. -/
theorem moving_left_row (q : unitInterval) :
    coefficientMovingSquareParameter (q, 0) =
      StdSimplex.map targetSide (binaryPath (k := 2) 0 1 2 q) := by
  rw [moving_left]
  exact (BassSupportOrder.map_any_binary targetSide 0 1 2 q).symm

end Quillen.PerfectComplexes.CoefficientMovingSquareRows

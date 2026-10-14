/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareCommonSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNodeTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.RightFirstNative

/-! Exact shared nodes required before the three native scalar surfaces can be pasted. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.DoubleSquareCommonSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

private theorem rightSourceEq {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (NormalizedTripleSimplex.sourceMap f g h).functor =
      (BinaryNormalizationSimplex.sourceMap (f ≫ g) h).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.assoc f g h).symm)

private theorem rightRawReference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    SplitTripleSimplex.rightFirstGeometric f g h =
      eqToIso (rightSourceEq f g h) ≪≫ BinaryNormalizationSimplex.first (f ≫ g) h := by
  unfold SplitTripleSimplex.rightFirstGeometric BinaryNormalizationSimplex.first
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem rightNormalizedReference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.rightFirst f g h =
      eqToIso (rightSourceEq f g h) ≪≫ BinaryNormalizationSimplex.total (f ≫ g) h := by
  unfold NormalizedTripleSimplex.rightFirst BinaryNormalizationSimplex.total
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

include hq in
private theorem middleFunctorEq : (NormalizedTripleSimplex.sourceMap c q p).functor =
    (NormalizedTripleSimplex.sourceMap q' b p).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (DoubleSquareTrack.middle_eq p q q' b c hq).symm)

include hp hq in
private theorem lastFunctorEq : (NormalizedTripleSimplex.sourceMap c q p).functor =
    (NormalizedTripleSimplex.sourceMap q' p' a).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))

private theorem middleSourceIso_hom : (middleSourceIso p q q' b c hq).hom =
    eqToHom (middleFunctorEq p q q' b c hq) := by
  simp only [middleSourceIso, isoWhiskerLeft_hom, isoWhiskerRight_hom, eqToIso.hom,
    whiskering_eqToHom]

private theorem lastSourceIso_hom : (lastSourceIso p q p' q' a b c hp hq).hom =
    eqToHom (lastFunctorEq p q p' q' a b c hp hq) := by
  simp only [lastSourceIso, isoWhiskerLeft_hom, isoWhiskerRight_hom, eqToIso.hom,
    whiskering_eqToHom]

private theorem middleSourceIso_eq : middleSourceIso p q q' b c hq =
    eqToIso (middleFunctorEq p q q' b c hq) := Iso.ext (middleSourceIso_hom p q q' b c hq)

private theorem lastSourceIso_eq : lastSourceIso p q p' q' a b c hp hq =
    eqToIso (lastFunctorEq p q p' q' a b c hp hq) :=
  Iso.ext (lastSourceIso_hom p q p' q' a b c hp hq)

/-- The first actual square identifies the two complete source reference nodes. -/
theorem source_middle_shared : nodes p q p' q' a b c hp hq 0 =
    nodes p q p' q' a b c hp hq 8 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (0 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (0 : Fin 8)))
  rw [first_nodes, middle_nodes]
  apply ModelSimplex.reference_node_eq (middleFunctorEq p q q' b c hq)
  simpa only [SplitTripleSimplex.references, Fin.cases_zero, Iso.refl_hom, Iso.trans_hom,
    Category.id_comp, Category.comp_id] using (middleSourceIso_hom p q q' b c hq).symm

/-- Both actual square equations identify the last complete source reference node. -/
theorem source_last_shared : nodes p q p' q' a b c hp hq 0 =
    nodes p q p' q' a b c hp hq 16 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (0 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (0 : Fin 8)))
  rw [first_nodes, last_nodes]
  apply ModelSimplex.reference_node_eq (lastFunctorEq p q p' q' a b c hp hq)
  simpa only [SplitTripleSimplex.references, Fin.cases_zero, Iso.refl_hom, Iso.trans_hom,
    Category.id_comp, Category.comp_id] using (lastSourceIso_hom p q p' q' a b c hp hq).symm

/-- The second square identifies the actual shared raw binary-normalization intermediate. -/
theorem left_raw_shared : nodes p q p' q' a b c hp hq 9 =
    nodes p q p' q' a b c hp hq 17 := by
  change nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (1 : Fin 8))) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (1 : Fin 8)))
  rw [middle_nodes, last_nodes]
  change (⟨BinaryNormalizationSimplex.intermediateMap q' (b ≫ p),
      middleSourceIso p q q' b c hq ≪≫ BinaryNormalizationSimplex.first q' (b ≫ p)⟩ :
        Node p q c) =
    ⟨BinaryNormalizationSimplex.intermediateMap q' (p' ≫ a),
      lastSourceIso p q p' q' a b c hp hq ≪≫ BinaryNormalizationSimplex.first q' (p' ≫ a)⟩
  rw [middleSourceIso_eq, lastSourceIso_eq]
  exact ModelSimplex.transportedReferenceNode_congr (NormalizedTripleSimplex.sourceMap c q p)
    (fun k : B' ⟶ A ↦ BinaryNormalizationSimplex.sourceMap q' k)
    (fun k ↦ BinaryNormalizationSimplex.intermediateMap q' k)
    (fun k ↦ BinaryNormalizationSimplex.first q' k) hp
    (middleFunctorEq p q q' b c hq) (lastFunctorEq p q p' q' a b c hp hq)

/-- The second square also identifies the actual normalized endpoint and its entire reference. -/
theorem left_normalized_shared : nodes p q p' q' a b c hp hq 10 =
    nodes p q p' q' a b c hp hq 18 := by
  change nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (2 : Fin 8))) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (2 : Fin 8)))
  rw [middle_nodes, last_nodes]
  change (⟨BinaryNormalizationSimplex.targetMap q' (b ≫ p),
      middleSourceIso p q q' b c hq ≪≫ BinaryNormalizationSimplex.total q' (b ≫ p)⟩ :
        Node p q c) =
    ⟨BinaryNormalizationSimplex.targetMap q' (p' ≫ a),
      lastSourceIso p q p' q' a b c hp hq ≪≫ BinaryNormalizationSimplex.total q' (p' ≫ a)⟩
  rw [middleSourceIso_eq, lastSourceIso_eq]
  exact ModelSimplex.transportedReferenceNode_congr (NormalizedTripleSimplex.sourceMap c q p)
    (fun k : B' ⟶ A ↦ BinaryNormalizationSimplex.sourceMap q' k)
    (fun k ↦ BinaryNormalizationSimplex.targetMap q' k)
    (fun k ↦ BinaryNormalizationSimplex.total q' k) hp
    (middleFunctorEq p q q' b c hq) (lastFunctorEq p q p' q' a b c hp hq)

/-- The first square identifies the shared raw right intermediate and its entire reference. -/
theorem right_raw_shared : nodes p q p' q' a b c hp hq 4 =
    nodes p q p' q' a b c hp hq 12 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (4 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (4 : Fin 8)))
  rw [first_nodes, middle_nodes]
  change (⟨BinaryNormalizationSimplex.intermediateMap (c ≫ q) p,
      SplitTripleSimplex.rightFirstGeometric c q p⟩ : Node p q c) =
    ⟨BinaryNormalizationSimplex.intermediateMap (q' ≫ b) p,
      middleSourceIso p q q' b c hq ≪≫ SplitTripleSimplex.rightFirstGeometric q' b p⟩
  rw [rightRawReference, rightRawReference, middleSourceIso_eq,
    ← Iso.trans_assoc, eqToIso_trans]
  exact ModelSimplex.transportedReferenceNode_congr (NormalizedTripleSimplex.sourceMap c q p)
    (fun k : C' ⟶ B ↦ BinaryNormalizationSimplex.sourceMap k p)
    (fun k ↦ BinaryNormalizationSimplex.intermediateMap k p)
    (fun k ↦ BinaryNormalizationSimplex.first k p) hq
    (rightSourceEq c q p) ((middleFunctorEq p q q' b c hq).trans (rightSourceEq q' b p))

/-- The first square also identifies the shared normalized right endpoint and its reference. -/
theorem right_normalized_shared : nodes p q p' q' a b c hp hq 5 =
    nodes p q p' q' a b c hp hq 13 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (5 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (5 : Fin 8)))
  rw [first_nodes, middle_nodes]
  change (⟨BinaryNormalizationSimplex.targetMap (c ≫ q) p,
      NormalizedTripleSimplex.rightFirst c q p⟩ : Node p q c) =
    ⟨BinaryNormalizationSimplex.targetMap (q' ≫ b) p,
      middleSourceIso p q q' b c hq ≪≫ NormalizedTripleSimplex.rightFirst q' b p⟩
  rw [rightNormalizedReference, rightNormalizedReference, middleSourceIso_eq,
    ← Iso.trans_assoc, eqToIso_trans]
  exact ModelSimplex.transportedReferenceNode_congr (NormalizedTripleSimplex.sourceMap c q p)
    (fun k : C' ⟶ B ↦ BinaryNormalizationSimplex.sourceMap k p)
    (fun k ↦ BinaryNormalizationSimplex.targetMap k p)
    (fun k ↦ BinaryNormalizationSimplex.total k p) hq
    (rightSourceEq c q p) ((middleFunctorEq p q q' b c hq).trans (rightSourceEq q' b p))

end Quillen.PerfectComplexes.DoubleSquareCommonSimplex

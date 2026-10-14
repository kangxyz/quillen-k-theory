/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ModelReferenceReanchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMergedScalarBoundary

/-! The actual five common outer-projection nodes in a native double-square rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectionReference
open BassReferenceMerge
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')

/-- The last raw target reference retains the original equality transports and geometric iso. -/
theorem last_raw_reference :
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 14).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm) ≪≫
          BinaryNormalizationSimplex.geometricIso (q' ≫ p') a) := by
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))) ≪≫
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc q' p' a).symm) ≪≫
      BinaryNormalizationSimplex.geometricIso (q' ≫ p') a) = _
  rw [← smallIso_trans]
  apply congrArg smallIso
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, eqToHom_trans]

abbrev reference := BinaryNormalizationSimplex.sourceMap c r

include hr in
theorem anchor : (reference c r).functor = (NormalizedTripleSimplex.sourceMap c q p).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (congrArg (fun k ↦ c ≫ k) hr.symm))

abbrev Node := Σ F : modelOf (boundedFlatPerfectWaldhausen A) ⟶
    modelOf (boundedFlatPerfectWaldhausen C'), (reference c r).functor ≅ F.functor

/-- Change only the reference of every actual original rectangle node. -/
def nodes (i : Fin 18) : Node c r :=
  ModelSimplex.reanchorNodes (F₀ := reference c r)
    (F₁ := NormalizedTripleSimplex.sourceMap c q p) (eqToIso (anchor p q c r hr))
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq) i

def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen A))
    (modelOf (boundedFlatPerfectWaldhausen C')) 17 :=
  ModelSimplex.reanchorSimplex (F₀ := reference c r)
    (F₁ := NormalizedTripleSimplex.sourceMap c q p) (eqToIso (anchor p q c r hr))
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

/-- The entire original rectangle is unchanged by the explicit common reference transport. -/
theorem simplex_original : simplex p q p' q' a b c hp hq r hr =
    DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq :=
  ModelSimplex.reanchorSimplex_eq (eqToIso (anchor p q c r hr))
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

include hp hq hr hr' in
/-- The projection composites retain this actual transported target source. -/
theorem outerAnchor : (reference c r).functor =
    (BinaryNormalizationSimplex.sourceMap r' a).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.outer_eq p q p' q' a b c hp hq r r' hr hr'))

/-- Canonical five-node outer square, independent of any chart factorization. -/
def outerNodes (houter : c ≫ r = r' ≫ a) : Fin 5 → Node c r :=
  ![⟨reference c r, Iso.refl _⟩,
    ⟨BinaryNormalizationSimplex.intermediateMap c r, BinaryNormalizationSimplex.first c r⟩,
    ⟨BinaryNormalizationSimplex.targetMap c r, BinaryNormalizationSimplex.total c r⟩,
    ⟨BinaryNormalizationSimplex.intermediateMap r' a,
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback houter)) ≪≫
        BinaryNormalizationSimplex.first r' a⟩,
    ⟨BinaryNormalizationSimplex.targetMap r' a,
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedFlatNormalizedPullback houter)) ≪≫
        BinaryNormalizationSimplex.total r' a⟩]

/-- The actual projection equations supply the common outer square's original reference. -/
def sharedNodes : Fin 5 → Node c r :=
  outerNodes a c r r' (DoubleSquareTrack.outer_eq p q p' q' a b c hp hq r r' hr hr')

def sharedIndex : Fin 5 → Fin 18 := ![0, 1, 2, 14, 15]

/-- The actual common source node is preserved with its reference. -/
theorem source_node : nodes p q p' q' a b c hp hq r hr 0 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 0 := by
  subst r
  change (⟨reference c (q ≫ p), Iso.refl _ ≪≫ Iso.refl _⟩ : Node c (q ≫ p)) =
    ⟨reference c (q ≫ p), Iso.refl _⟩
  rw [Iso.refl_trans]

/-- The first original raw normalization intermediate is common. -/
theorem source_raw_node : nodes p q p' q' a b c hp hq r hr 1 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 1 := by
  subst r
  change (⟨BinaryNormalizationSimplex.intermediateMap c (q ≫ p),
    Iso.refl _ ≪≫ BinaryNormalizationSimplex.first c (q ≫ p)⟩ : Node c (q ≫ p)) =
    ⟨BinaryNormalizationSimplex.intermediateMap c (q ≫ p),
      BinaryNormalizationSimplex.first c (q ≫ p)⟩
  rw [Iso.refl_trans]

/-- The first normalized endpoint is common. -/
theorem source_normal_node : nodes p q p' q' a b c hp hq r hr 2 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 2 := by
  subst r
  change (⟨BinaryNormalizationSimplex.targetMap c (q ≫ p),
    Iso.refl _ ≪≫ BinaryNormalizationSimplex.total c (q ≫ p)⟩ : Node c (q ≫ p)) =
    ⟨BinaryNormalizationSimplex.targetMap c (q ≫ p),
      BinaryNormalizationSimplex.total c (q ≫ p)⟩
  rw [Iso.refl_trans]

/-- The projected raw target reference is its original canonical equality transport. -/
theorem target_raw_reference : (nodes p q p' q' a b c hp hq r hr 14).2 =
    eqToIso (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) ≪≫
      BinaryNormalizationSimplex.first (q' ≫ p') a := by
  change eqToIso (anchor p q c r hr) ≪≫
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 14).2 = _
  rw [last_raw_reference, smallIso_trans, smallIso_eqToIso]
  rw [← Iso.trans_assoc, eqToIso_trans]
  rfl

/-- The projected normalized target reference retains the original total normalization. -/
theorem target_normal_reference : (nodes p q p' q' a b c hp hq r hr 15).2 =
    eqToIso (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) ≪≫
      BinaryNormalizationSimplex.total (q' ≫ p') a := by
  change eqToIso (anchor p q c r hr) ≪≫
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq 15).2 = _
  rw [BassReferenceMerge.last_source_reference, smallIso_trans, smallIso_eqToIso]
  rw [← Iso.trans_assoc, eqToIso_trans]
  rfl

theorem target_raw_map : (nodes p q p' q' a b c hp hq r hr 14).1 =
    BinaryNormalizationSimplex.intermediateMap (q' ≫ p') a := by
  apply Model.Hom.ext
  rfl

theorem target_normal_map : (nodes p q p' q' a b c hp hq r hr 15).1 =
    BinaryNormalizationSimplex.targetMap (q' ≫ p') a := by
  apply Model.Hom.ext
  rfl

/-- The full raw target node uses the actual target projection equation. -/
theorem target_raw_node : nodes p q p' q' a b c hp hq r hr 14 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 3 := by
  have he : nodes p q p' q' a b c hp hq r hr 14 =
      ModelSimplex.transportedReferenceNode (reference c r)
        (fun k ↦ BinaryNormalizationSimplex.sourceMap k a)
        (fun k ↦ BinaryNormalizationSimplex.intermediateMap k a)
        (fun k ↦ BinaryNormalizationSimplex.first k a) (q' ≫ p')
        (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) := by
    apply Sigma.ext (target_raw_map p q p' q' a b c hp hq r hr)
    exact heq_of_eq (target_raw_reference p q p' q' a b c hp hq r hr)
  exact he.trans (ModelSimplex.transportedReferenceNode_congr (reference c r)
    (fun k ↦ BinaryNormalizationSimplex.sourceMap k a)
    (fun k ↦ BinaryNormalizationSimplex.intermediateMap k a)
    (fun k ↦ BinaryNormalizationSimplex.first k a) hr' _ _)

/-- The full normalized target node uses that same original projection equation. -/
theorem target_normal_node : nodes p q p' q' a b c hp hq r hr 15 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 4 := by
  have he : nodes p q p' q' a b c hp hq r hr 15 =
      ModelSimplex.transportedReferenceNode (reference c r)
        (fun k ↦ BinaryNormalizationSimplex.sourceMap k a)
        (fun k ↦ BinaryNormalizationSimplex.targetMap k a)
        (fun k ↦ BinaryNormalizationSimplex.total k a) (q' ≫ p')
        (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) := by
    apply Sigma.ext (target_normal_map p q p' q' a b c hp hq r hr)
    exact heq_of_eq (target_normal_reference p q p' q' a b c hp hq r hr)
  exact he.trans (ModelSimplex.transportedReferenceNode_congr (reference c r)
    (fun k ↦ BinaryNormalizationSimplex.sourceMap k a)
    (fun k ↦ BinaryNormalizationSimplex.targetMap k a)
    (fun k ↦ BinaryNormalizationSimplex.total k a) hr' _ _)

/-- All five shared nodes retain their entire actual reference isomorphisms. -/
theorem shared_nodes (i : Fin 5) : nodes p q p' q' a b c hp hq r hr (sharedIndex i) =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' i := by
  fin_cases i
  · exact source_node p q p' q' a b c hp hq r r' hr hr'
  · exact source_raw_node p q p' q' a b c hp hq r r' hr hr'
  · exact source_normal_node p q p' q' a b c hp hq r r' hr hr'
  · exact target_raw_node p q p' q' a b c hp hq r r' hr hr'
  · exact target_normal_node p q p' q' a b c hp hq r r' hr hr'

include hr' in
/-- Two actual chart factorizations share the full original outer-path nodes. -/
theorem two_projection_shared (q₂ : C ⟶ B) (q₂' : C' ⟶ B')
    (hq₂ : c ≫ q₂ = q₂' ≫ b) (hr₂ : q₂ ≫ p = r) (hr₂' : q₂' ≫ p' = r')
    (i : Fin 5) :
    nodes p q p' q' a b c hp hq r hr (sharedIndex i) =
      nodes p q₂ p' q₂' a b c hp hq₂ r hr₂ (sharedIndex i) :=
  (shared_nodes p q p' q' a b c hp hq r r' hr hr' i).trans
    (shared_nodes p q₂ p' q₂' a b c hp hq₂ r r' hr₂ hr₂' i).symm

end Quillen.PerfectComplexes.ProjectionReference

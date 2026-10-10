/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.LoopMap
public import Quillen.Waldhausen.SConstruction.Rows.OneRowNaturality
public import Quillen.Topology.Realization.HomotopySquare


/-!
# Exact-functor naturality of the original iterated-S structure map

Exact functors act on both actual S-directions. When the functor preserves
the specified zero object, the original cylinder and realized loop map
commute with these actual maps. The strict zero equality is explicit; no
unrelated naturality or delooping-equivalence hypothesis is supplied.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Exact functors act on both genuine S-directions. -/
def doubleMap : doubleS V ⟶ doubleS W where
  app n := sSetMap (QuotientRows.postcompose_exact V W hF n.unop)
  naturality n m α := by
    ext k A : 4
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

def doubleDiagonalMap : doubleDiagonal V ⟶ doubleDiagonal W :=
  TheoremA.diagonalMap (doubleMap V W hF)

variable (h0 : F.obj V.zero = W.zero)
include h0 in
lemma suspensionRow_postcompose {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    suspensionRow V τ ⋙ QuotientRows.postcompose V W hF n = F ⋙ suspensionRow W τ := by
  change (QuotientRows.oneEmbedding V ⋙ QuotientRows.reindex V τ) ⋙ _ = _
  rw [Functor.assoc, ← QuotientRows.postcompose_reindex V W hF τ,
    ← Functor.assoc, QuotientRows.oneEmbedding_postcompose V W hF h0]
  rfl

include h0 in
lemma suspensionCylinder_naturality :
    (sSetMap hF ▷ Δ[1]) ≫ suspensionCylinder W =
      suspensionCylinder V ≫ doubleDiagonalMap V W hF := by
  ext n z : 4
  apply Subtype.ext
  change z.1.val ⋙ F ⋙ suspensionRow W z.2.down =
    z.1.val ⋙ suspensionRow V z.2.down ⋙ QuotientRows.postcompose V W hF n.unop
  rw [suspensionRow_postcompose V W hF h0]

include h0 in
lemma postcompose_zero (n : SimplexCategory) :
    (QuotientRows.postcompose V W hF n).obj (QuotientRows.zero V n) =
      QuotientRows.zero W n := by
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ h0) ?_
  intro p q f
  exact (hF.zero V.isZero).eq_of_src _ _

include h0 in
lemma doubleDiagonalMap_zeroSimplex (n : SimplexCategoryᵒᵖ) :
    (doubleDiagonalMap V W hF).app n
      (zeroSimplex (QuotientRows.waldhausenStructure V n.unop).cof
        (QuotientRows.waldhausenStructure V n.unop).weq
        (QuotientRows.zero V n.unop) (QuotientRows.isZero V n.unop) n) =
      zeroSimplex (QuotientRows.waldhausenStructure W n.unop).cof
        (QuotientRows.waldhausenStructure W n.unop).weq
        (QuotientRows.zero W n.unop) (QuotientRows.isZero W n.unop) n := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ postcompose_zero V W hF h0 n.unop) ?_
  intro p q f
  exact ((QuotientRows.postcompose_exact V W hF n.unop).zero
    (QuotientRows.isZero V n.unop)).eq_of_src _ _

include h0 in
lemma doubleDiagonalMap_basepoint :
    SSet.toTop.map (doubleDiagonalMap V W hF) (doubleBasepoint V) = doubleBasepoint W := by
  change SSet.toTop.map (doubleDiagonalMap V W hF) (realizationPoint (doubleVertex V)) = _
  rw [realizationPoint_naturality]
  exact congrArg realizationPoint (doubleDiagonalMap_zeroSimplex V W hF h0 (op ⦋0⦌))

include h0 in
/-- The concrete loop structure map is natural for exact functors preserving
the specified zeros, through the original realization maps in both stages. -/
lemma loopStructureMap_naturality (x : V.Delooping) :
    basedLoopMap (SSet.toTop.map (doubleDiagonalMap V W hF)).hom
      (doubleDiagonalMap_basepoint V W hF h0) (loopStructureMap V x) =
        loopStructureMap W (deloopingMap hF x) := by
  ext t
  exact realizationSimplicialHomotopy_square (suspensionHomotopy V) (suspensionHomotopy W)
    (sSetMap hF) (doubleDiagonalMap V W hF)
    (suspensionCylinder_naturality V W hF h0).symm t x

end Quillen.Waldhausen.IteratedS

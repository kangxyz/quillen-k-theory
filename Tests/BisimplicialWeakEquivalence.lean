/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.Realization.BisimplicialWeakEquivalence

/-! # Semantic consumers of original weak diagonal realization

These retain actual diagonal maps, all degrees and target components,
weak-only finite attachments and the prescribed colimit comparison.
-/
noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
namespace Quillen.Tests.BisimplicialWeakEquivalence
open BisimplicialRealization TheoremA
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
  (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌)))

include h in
/-- The induced bijection is on the original diagonal map in every degree. -/
theorem diagonal_homotopy_maps (x : |diagonalSSet X|) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (SSet.toTop.map (diagonalMap η)).hom (x := x) rfl) :=
  (diagonalMap_isRealizationWeakEquivalence η h).homotopy_bijective x n

include h in
/-- Component surjectivity includes all actual target points. -/
theorem diagonal_components (y : |diagonalSSet Y|) :
    ∃ x, Joined ((SSet.toTop.map (diagonalMap η)).hom x) y :=
  (diagonalMap_isRealizationWeakEquivalence η h).component_surjective y

include h in
/-- The zero-dimensional homotopy set is included explicitly. -/
theorem diagonal_zero (x : |diagonalSSet X|) :
    Function.Bijective (homotopyGroupMap (N := Fin 0)
      (SSet.toTop.map (diagonalMap η)).hom (x := x) rfl) :=
  diagonal_homotopy_maps η h x 0

include h in
/-- The original empty latching level does not acquire a nonempty premise. -/
theorem zero_latching : IsRealizationWeakEquivalence (latchingMap η 0) :=
  latchingMap_isRealizationWeakEquivalence η h 0

include h in
/-- Weak-only row data control the full actual attachment at every degree. -/
theorem original_attachment (n : ℕ) : IsRealizationWeakEquivalence (attachmentMap n η) :=
  attachmentMap_isRealizationWeakEquivalence η h n

/-- Arbitrary sequential T1 closed-embedding systems retain their given comparison. -/
theorem original_sequential_colimit {F G : ℕ ⥤ TopCat.{u}} (α : F ⟶ G)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
    [∀ n, T1Space (F.obj n)] [∀ n, T1Space (G.obj n)]
    (hF : ∀ n, Topology.IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, Topology.IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))
    (hα : ∀ n, IsWeakHomotopyEquivalence (α.app n).hom) :
    IsWeakHomotopyEquivalence (hc.map d α).hom :=
  RealizationCompactStages.colimitMap_isWeakHomotopyEquivalence α c hc d hd hF hG hα

end Quillen.Tests.BisimplicialWeakEquivalence

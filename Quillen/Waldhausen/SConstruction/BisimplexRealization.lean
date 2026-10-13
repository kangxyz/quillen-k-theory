/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Bisimplicial
public import Quillen.Topology.Realization.ProductSimplex

/-! # Realizing the two independent coordinates of an original quotient grid

An actual certified bisimplex gives a map from the product of its two standard simplices
into the original diagonal S-construction. The continuous family retains both barycentric
coordinates and their exact reindexing, rather than choosing a homotopy witness.
-/
@[expose] public section
noncomputable section
open CategoryTheory Opposite MonoidalCategory Convexity
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)

/-- Reindex the actual quotient grid independently along the two original simplex arrows. -/
def bisimplexFamily : (Δ[n] ⊗ Δ[m] : SSet.{max u v}) ⟶ sSet W.cof W.weq where
  app k := ↾fun z ↦ ⟨gridMap₂ z.1.down z.2.down ⋙ F,
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp
      (hF.precomp W.cof W.weq z.1.down z.2.down)⟩
  naturality _ _ _ := by ext z; rfl

/-- Both standard-simplex operators retain the entire original grid under reindexing. -/
theorem bisimplexFamily_precomp {n' m' : ℕ} (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌) :
    (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫ bisimplexFamily W F hF =
      bisimplexFamily W (gridMap₂ α β ⋙ F) (hF.precomp W.cof W.weq α β) := by
  ext k z
  rfl

/-- The original grid realized with independent barycentric S and nerve coordinates. -/
def bisimplexRealization :
    C(StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)), |sSet W.cof W.weq|) :=
  (SSet.toTop.map (bisimplexFamily W F hF)).hom.comp
    ⟨(realizationProductSimplexHomeomorph n m).symm,
      (realizationProductSimplexHomeomorph n m).symm.continuous⟩

/-- The specified continuous family keeps the actual inverse product-simplex comparison. -/
theorem bisimplexRealization_apply
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    bisimplexRealization W F hF (z, t) =
      SSet.toTop.map (bisimplexFamily W F hF)
        ((realizationProductSimplexHomeomorph n m).symm (z, t)) := rfl

/-- The entire continuous family commutes with both original simplex operators. -/
theorem bisimplexRealization_precomp {n' m' : ℕ}
    (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌)
    (z : StdSimplex ℝ (Fin (n' + 1))) (t : StdSimplex ℝ (Fin (m' + 1))) :
    bisimplexRealization W F hF (z.map α, t.map β) =
      bisimplexRealization W (gridMap₂ α β ⋙ F)
        (hF.precomp W.cof W.weq α β) (z, t) := by
  have hx :
      SSet.toTop.map (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β)
          ((realizationProductSimplexHomeomorph n' m').symm (z, t)) =
        (realizationProductSimplexHomeomorph n m).symm (z.map α, t.map β) := by
    apply (realizationProductSimplexHomeomorph n m).injective
    rw [Homeomorph.apply_symm_apply, realizationProductSimplexHomeomorph_naturality,
      Homeomorph.apply_symm_apply]
  change SSet.toTop.map (bisimplexFamily W F hF)
      ((realizationProductSimplexHomeomorph n m).symm (z.map α, t.map β)) = _
  rw [← hx]
  change (SSet.toTop.map (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫
    SSet.toTop.map (bisimplexFamily W F hF)) _ = _
  rw [← Functor.map_comp, bisimplexFamily_precomp]
  rfl

/-- Equal original grids give equal specified continuous realization families. -/
theorem bisimplexRealization_congr {G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C}
    (hG : IsSimplex₂ W.cof W.weq G) (h : F = G) :
    bisimplexRealization W F hF = bisimplexRealization W G hG := by
  cases h
  rfl

end Quillen.Waldhausen

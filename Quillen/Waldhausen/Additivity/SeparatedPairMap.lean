/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Additivity.NormalizedSumMap
public import Quillen.Waldhausen.Additivity.DiagonalKMap
public import Quillen.Waldhausen.Additivity.SubdivisionBasepoint
public import Quillen.Waldhausen.Product.KEquivalence

/-! # The actual pair of distinct subdivision restrictions

The old separated pair grid is a genuine product Waldhausen grid in both independent degrees.
Its two projections are the original first and right restrictions. The actual diagonal and
product realization maps preserve those projections and the chosen zero, without any inverse
or compact-lift choice.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Additivity
open ExtensionCategory
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The actual right-half restriction, distinct from the original first-half endpoint. -/
def rightRestrictionMap :
    OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶ bisimplicialSSet V where
  app p := (bisimplicialSSet V).map (OrdinalSubdivision.second.app p.unop).op
  naturality p q f := by
    change (bisimplicialSSet V).map (OrdinalSubdivision.δ.map f.unop).op ≫
        (bisimplicialSSet V).map (OrdinalSubdivision.second.app q.unop).op =
      (bisimplicialSSet V).map (OrdinalSubdivision.second.app p.unop).op ≫
        (bisimplicialSSet V).map f
    rw [← (bisimplicialSSet V).map_comp, ← (bisimplicialSSet V).map_comp]
    exact congrArg (bisimplicialSSet V).map
      (congrArg Quiver.Hom.op (OrdinalSubdivision.second.naturality f.unop)).symm

/-- The two original restrictions satisfy every product simplex condition componentwise. -/
theorem separatedPairGrid_isSimplex₂ {n m : SimplexCategory}
    {A : Grid₂ (OrdinalSubdivision.δ.obj n) m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ (productStructure V V).cof (productStructure V V).weq
      (separatedPairGrid A) := by
  let hL := hA.precomp V.cof V.weq (Edgewise.left n n) (𝟙 m)
  let hR := hA.precomp V.cof V.weq (Edgewise.right n n) (𝟙 m)
  exact {
    zero t i := product_isZero (hL.zero t i) (hR.zero t i)
    cofibration t i j k hij hjk :=
      ⟨hL.cofibration t i j k hij hjk, hR.cofibration t i j k hij hjk⟩
    quotient t i j k hij hjk := product_isPushout _ _ _ _
      (hL.quotient t i j k hij hjk) (hR.quotient t i j k hij hjk)
    weak s t i j hst hij := ⟨hL.weak s t i j hst hij, hR.weak s t i j hst hij⟩ }

/-- The original separated pair grid, as an actual map into the product S-construction. -/
def separatedPairMap : OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶
    bisimplicialSSet (productStructure V V) where
  app n := {
    app m := ↾fun A ↦ ⟨separatedPairGrid A.1, separatedPairGrid_isSimplex₂ V A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality n n' μ := by
    ext m A
    apply Subtype.ext
    exact separatedPairGrid_reindex μ.unop (𝟙 m.unop) A.1

/-- The underlying pair is literally the original grid, with quotient-first order. -/
theorem separatedPairMap_grid (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((separatedPairMap V).app n).app m A).1 = separatedPairGrid A.1 := rfl

/-- The first product projection is exactly the old first-half endpoint. -/
theorem separatedPairMap_fst :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (fst_exact V V) =
      OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V) := by
  ext n m A
  apply Subtype.ext
  rfl

/-- The second product projection is exactly the actual right-half restriction. -/
theorem separatedPairMap_snd :
    separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (snd_exact V V) = rightRestrictionMap V := by
  ext n m A
  apply Subtype.ext
  rfl

/-- The right restriction retains the original zero vertex. -/
theorem rightRestrictionMap_zeroVertex :
    (TheoremA.diagonalMap (rightRestrictionMap V)).app (op ⦋0⦌)
      (subdivisionZeroVertex V) = diagonalZeroVertex V := rfl

/-- The pair sends the actual constant-zero grid to the actual product zero grid. -/
theorem separatedPairMap_zeroVertex :
    (TheoremA.diagonalMap (separatedPairMap V)).app (op ⦋0⦌)
      (subdivisionZeroVertex V) = diagonalZeroVertex (productStructure V V) := rfl

/-- The original first restriction followed by its actual diagonal isomorphism. -/
def separatedFirstDeloopingMap :
    C(|TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|, V.Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))

/-- The original right restriction followed by that same diagonal isomorphism. -/
def separatedRightDeloopingMap :
    C(|TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|, V.Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    (realizedDiagonalMap (rightRestrictionMap V))

/-- The actual product-valued map on the unchanged original subdivision realization. -/
def separatedPairDeloopingMap :
    C(|TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      (productStructure V V).Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso (productStructure V V)).hom).hom.comp
    (realizedDiagonalMap (separatedPairMap V))

/-- Both actual product projections retain the distinct original restriction maps. -/
theorem separatedPairDeloopingMap_projection
    (x : |TheoremA.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|) :
    Product.deloopingComparison V V (separatedPairDeloopingMap V x) =
      (separatedFirstDeloopingMap V x, separatedRightDeloopingMap V x) := by
  apply _root_.Prod.ext
  · have hn := DFunLike.congr_fun
      (realizedDiagonalMap_exact_naturality (productStructure V V) V (fst_exact V V))
      (realizedDiagonalMap (separatedPairMap V) x)
    have hp := DFunLike.congr_fun (congrArg realizedDiagonalMap (separatedPairMap_fst V)) x
    rw [realizedDiagonalMap_comp] at hp
    exact hn.symm.trans (congrArg
      (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y) hp)
  · have hn := DFunLike.congr_fun
      (realizedDiagonalMap_exact_naturality (productStructure V V) V (snd_exact V V))
      (realizedDiagonalMap (separatedPairMap V) x)
    have hp := DFunLike.congr_fun (congrArg realizedDiagonalMap (separatedPairMap_snd V)) x
    rw [realizedDiagonalMap_comp] at hp
    exact hn.symm.trans (congrArg
      (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y) hp)

/-- The first restriction retains its original chosen-zero point. -/
theorem separatedFirstDeloopingMap_basepoint :
    separatedFirstDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y)
    (horizontalEndpoint_basepoint V)).trans (diagonalRealization_basepoint V)

/-- The right restriction also retains that actual chosen-zero point. -/
theorem separatedRightDeloopingMap_basepoint :
    separatedRightDeloopingMap V (subdivisionBasepoint V) = V.kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y)
    (realizationPoint_naturality (TheoremA.diagonalMap (rightRestrictionMap V))
      (subdivisionZeroVertex V))).trans (diagonalRealization_basepoint V)

/-- The pair retains exactly the original product basepoint, with no selected path. -/
theorem separatedPairDeloopingMap_basepoint :
    separatedPairDeloopingMap V (subdivisionBasepoint V) = (productStructure V V).kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso (productStructure V V)).hom y)
    (realizationPoint_naturality (TheoremA.diagonalMap (separatedPairMap V))
      (subdivisionZeroVertex V))).trans (diagonalRealization_basepoint (productStructure V V))

end Quillen.Waldhausen.Additivity

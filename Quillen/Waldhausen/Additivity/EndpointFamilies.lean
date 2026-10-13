/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Additivity.EndpointNaturality

/-! # Coherent weak-transformation families at the deformation endpoints -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace Quillen.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The actual identity endpoint transformation to the original middle map. -/
def identityEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    (((identityDeformationMap V W a hF hG hc).app n).app m A).1 ⟶
      (((bisimplicialSSetMap V.cof V.weq hG).app n).app m A).1 :=
  (identityDeformationIso V W a hc (𝟙 n.unop) A.1).hom

/-- These endpoint components are actual isomorphisms and hence weak. -/
theorem identityEndpointFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    W.weq ((identityEndpointFamily V W a hF hG hc n m A).app x) :=
  W.weq_iso _ (by
    change IsIso ((identityDeformationIso V W a hc (𝟙 n.unop) A.1).hom.app x)
    infer_instance)

/-- Exact component coherence for independent interval and nerve restriction. -/
theorem identityEndpointFamily_reindex_app {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m)
    (A : ((bisimplicialSSet V).obj (op n)).obj (op m)) (x : Grid₂ n' m') :
    HEq ((identityEndpointFamily V W a hF hG hc (op n) (op m) A).app ((gridMap₂ α β).obj x))
      ((identityEndpointFamily V W a hF hG hc (op n') (op m')
        ⟨gridMap₂ α β ⋙ A.1, A.2.precomp V.cof V.weq α β⟩).app x) := by
  exact heq_of_eq (NatTrans.congr_app
    (eq_of_heq (identityDeformationIso_reindex V W a hc α β A.1)) x)

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The actual separated endpoint transformation to the common split diagram. -/
def separatedEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((separatedDeformationMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((separatedSumMap V W hs.exactH hs.exactF).app n).app m A).1 :=
  (separatedDeformationIso V W a (Edgewise.left n.unop n.unop) (Edgewise.right n.unop n.unop)
    (left_le_right n.unop) (left_separated_right n.unop) b hs A.2).hom

/-- Every separated endpoint component is a genuine weak equivalence. -/
theorem separatedEndpointFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m)
    (x : Grid₂ n.unop m.unop) :
    W.weq ((separatedEndpointFamily V W a b hs n m A).app x) :=
  W.weq_iso _ (by
    change IsIso ((separatedDeformationIso V W a (Edgewise.left n.unop n.unop)
      (Edgewise.right n.unop n.unop) (left_le_right n.unop) (left_separated_right n.unop) b hs
        A.2).hom.app x)
    infer_instance)

/-- Coherence uses the actual equality of the reindexed arrow and the unique
pushout-to-cofiber comparison, not a postulated naturality of a homotopy. -/
theorem separatedEndpointFamily_reindex_app {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m)
    (A : ((OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj (op n)).obj (op m))
    (x : Grid₂ n' m') :
    HEq ((separatedEndpointFamily V W a b hs (op n) (op m) A).app ((gridMap₂ α β).obj x))
      ((separatedEndpointFamily V W a b hs (op n') (op m')
        ⟨gridMap₂ (OrdinalSubdivision.δ.map α) β ⋙ A.1,
          A.2.precomp V.cof V.weq (OrdinalSubdivision.δ.map α) β⟩).app x) :=
  separatedDeformationIso_reindex_app V W a b hs α β A.2 x

end Quillen.Waldhausen.Additivity

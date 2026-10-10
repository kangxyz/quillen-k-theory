/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Additivity.EndpointFamilies
public import Quillen.Waldhausen.SConstruction.WeakGridHomotopy

/-! # Genuine simplicial homotopies at both additivity endpoints -/
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

/-- The actual identity deformation is simplicially homotopic to the original
middle-functor map, using its coherent canonical pushout isomorphisms. -/
def identityEndpointHomotopy :
    SSet.Homotopy (TheoremA.diagonalMap (identityDeformationMap V W a hF hG hc))
      (TheoremA.diagonalMap (bisimplicialSSetMap V.cof V.weq hG)) :=
  diagonalWeakGridHomotopy W _ _ (identityEndpointFamily V W a hF hG hc)
    (identityEndpointFamily_weak V W a hF hG hc) (by
      intro n n' α A x
      exact (identityEndpointFamily_reindex_app V W a hF hG hc α.unop α.unop A x).symm)

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The actual separated deformation is simplicially homotopic to the common
split endpoint, with strict reindex coherence proved from the input arrows. -/
def separatedEndpointHomotopy :
    SSet.Homotopy
      (TheoremA.diagonalMap (separatedDeformationMap V W a hs.exactF hs.exactG hs.cofibration))
      (TheoremA.diagonalMap (separatedSumMap V W hs.exactH hs.exactF)) :=
  diagonalWeakGridHomotopy W _ _ (separatedEndpointFamily V W a b hs)
    (separatedEndpointFamily_weak V W a b hs) (by
      intro n n' α A x
      exact (separatedEndpointFamily_reindex_app V W a b hs α.unop α.unop A x).symm)

end Quillen.Waldhausen.Additivity

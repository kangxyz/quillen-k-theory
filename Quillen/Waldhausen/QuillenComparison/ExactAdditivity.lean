/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Waldhausen.QuillenComparison.KCommutativity
public import Quillen.Waldhausen.QuillenComparison.ExactNaturality
public import Quillen.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-! # Literal additivity of the original Quillen exact-functor K-maps

Pointwise genuine conflations give the structural Waldhausen cofibration
sequence. Canonical based Q/S naturality transports its proved multiplication
formula to the unchanged original Quillen KMap API.
-/
@[expose] public section

open Quillen.Waldhausen.QuillenComparison


open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u v

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
open Waldhausen.QuillenComparison
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D}

/-- Genuine conflation sequences of exact functors induce literal additivity
on the original Quillen K-maps, including degree zero. -/
theorem KMap_conflation_additivity (F G H : ExactFunctor E E')
    (a : F.toFunctor ⟶ G.toFunctor) (b : G.toFunctor ⟶ H.toFunctor)
    (w : a ≫ b = 0)
    (hc : ∀ X, E'.conflation (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))
    (n : ℕ) (x : E.K n) : G.KMap n x = F.KMap n x * H.KMap n x := by
  let V := Waldhausen.ofExactCategory E
  let W := Waldhausen.ofExactCategory E'
  let := Waldhausen.Additivity.hasBinaryCoproducts W
  let hs := Waldhausen.GilletWaldhausen.exactFunctorSequence_isCofibrationSequence
    E E' a b w hc F G H rfl rfl rfl
  obtain ⟨y, rfl⟩ := (comparisonKEquiv E n).surjective x
  have h := Waldhausen.Additivity.KMap_additivity_mul V W a b hs n y
  have hF := DFunLike.congr_fun (comparisonKEquiv_exactFunctor_naturality F n) y
  have hG := DFunLike.congr_fun (comparisonKEquiv_exactFunctor_naturality G n) y
  have hH := DFunLike.congr_fun (comparisonKEquiv_exactFunctor_naturality H n) y
  calc
    G.KMap n (comparisonKEquiv E n y) =
        comparisonKEquiv E' n (Waldhausen.KMap G.waldhausenExact n y) := hG.symm
    _ = comparisonKEquiv E' n
        (Waldhausen.KMap F.waldhausenExact n y * Waldhausen.KMap H.waldhausenExact n y) :=
      congrArg (comparisonKEquiv E' n) h
    _ = F.KMap n (comparisonKEquiv E n y) * H.KMap n (comparisonKEquiv E n y) :=
      ((comparisonKEquiv E' n).map_mul _ _).trans (congrArg₂ (· * ·) hF hH)

end CategoryTheory.ExactCategory.ExactFunctor

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedProductUnitInterchange

/-! # Regression properties of the original supported scalar interchange -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.SupportedGlobalUnitIdentityOperation
open Quillen.PerfectComplexes.SupportedProductUnitInterchange
universe u

/-- Repeating a supported scalar operation on a geometrically pulled-back original K-zero class
produces a class whose square is the identity. No support-forget map is used. -/
example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)
    (a : BoundedFlatPerfectSupportedK B.obj.hom 0) :
    let b := unitKOperation A.obj.hom r 1
      (unitKOperation A.obj.hom r 0 (boundedFlatPerfectSupportedKPullback g 0 a))
    b * b = 1 := by
  dsimp only
  let b := unitKOperation A.obj.hom r 1
    (unitKOperation A.obj.hom r 0 (boundedFlatPerfectSupportedKPullback g 0 a))
  have h : b = b⁻¹ := unitKOperation_interchange_sign A.obj.hom r r 0 _
  calc
    b * b = b⁻¹ * b := congrArg (fun z ↦ z * b) h
    _ = 1 := inv_mul_cancel b

/-- A caller supplies its actual scalar equation on any open-pair arrow. -/
example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.obj.right, ⊤))ˣ) (s : (Γ(A.obj.right, ⊤))ˣ)
    (h : Units.map g.hom.right.appTop.hom.toMonoidHom r = s)
    (K : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory) :
    (boundedFlatPerfectSupportedPullback g).map
        ((boundedFlatPerfectSupportedGlobalUnitIso B.obj.hom r).hom.app K) =
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom s).hom.app
        ((boundedFlatPerfectSupportedPullback g).obj K) :=
  pullback_preserves_of_eq g r s h K

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MScalarPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFamilyReindex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReassociationSupport

/-! Exact finite support-order conditions supplied by the common certificate. -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {k : ℕ} (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))

/-- Only the actual 71 finite support chains; no enclosing unused simplex order is assumed. -/
structure SupportOrders : Prop where
  oldPlus : ∀ i, Monotone
    (g ∘ BassH1Order.oldIndex ∘ (BassSupportOrder.oldPlusFace i).toOrderHom)
  oldMinus : ∀ i, Monotone
    (g ∘ BassH1Order.oldIndex ∘ (BassSupportOrder.oldMinusFace i).toOrderHom)
  oldH0Plus : ∀ i, Monotone
    (g ∘ BassH1Order.oldIndex ∘ (BassSupportOrder.h0PlusFace i).toOrderHom)
  oldH0Minus : ∀ i, Monotone
    (g ∘ BassH1Order.oldIndex ∘ (BassSupportOrder.h0MinusFace i).toOrderHom)
  oldBottom : Monotone (g ∘ BassH1Order.oldIndex ∘ BassSupportOrder.bottomFace.toOrderHom)
  firstPlus : ∀ i, Monotone (g ∘ BassH1Order.firstIndex ∘
    (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom)
  firstMinus : ∀ i, Monotone (g ∘ BassH1Order.firstIndex ∘
    (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom)
  middlePlus : ∀ i, Monotone (g ∘ BassH1Order.middleIndex ∘
    (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom)
  middleMinus : ∀ i, Monotone (g ∘ BassH1Order.middleIndex ∘
    (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom)
  productPlus : ∀ i j, Monotone (g ∘ BassH1Order.plusProductIndex ∘
    (BassH1Support.edgePairFace i j).toOrderHom)
  productMinus : ∀ i j, Monotone (g ∘ BassH1Order.minusProductIndex ∘
    (BassH1Support.edgePairFace i j).toOrderHom)
  vertexPlus : ∀ i, Monotone (f ∘ BassMVertexOrder.plusIndex ∘
    (BassPrimitiveSupport.rectangleFace i).toOrderHom)
  vertexMinus : ∀ i, Monotone (f ∘ BassMVertexOrder.minusIndex ∘
    (BassPrimitiveSupport.rectangleFace i).toOrderHom)
  vertexMiddle : ∀ i j, Monotone (f ∘ BassMVertexOrder.middleIndex ∘
    (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom)

end Quillen.PerfectComplexes.BassMFamilyTransfer

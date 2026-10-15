/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReindexedOldCells

/-! Every original H1 cell and the whole H1 family survive the exact support reindexing. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) {k : ℕ}
  (N : Fin (k + 1) → BassOverlap.Node P u v)
  (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))
  (hn : ∀ i, N (g i) = BassH1Merged.nodes P u v i) (o : SupportOrders f g)

include hn o in
/-- The entire original H1 first cell keeps all native levels and scalar values. -/
theorem old_first_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.firstParameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.firstParameter (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.firstIndex
      (BassH0Diagram.parameter (r, t))), x) = _
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.firstIndex (BassH0Diagram.parameter (r, t)), x)
  obtain ⟨α, hα, i, z, hz⟩ := BassPrimitiveSupport.h0_support (r, t)
  rw [← hz]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact old_face_value P u v N g hn BassH1Order.firstIndex
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace)
      (BassH1Order.firstPlus_monotone i) (o.firstPlus i) n z x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact old_face_value P u v N g hn BassH1Order.firstIndex
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace)
      (BassH1Order.firstMinus_monotone i) (o.firstMinus i) n z x

include hn o in
/-- The entire original H1 middle cell keeps all native levels and scalar values. -/
theorem old_middle_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.middleParameter (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.middleParameter (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.middleIndex
      (BassH0Diagram.parameter (r, t))), x) = _
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.middleIndex (BassH0Diagram.parameter (r, t)), x)
  obtain ⟨α, hα, i, z, hz⟩ := BassPrimitiveSupport.h0_support (r, t)
  rw [← hz]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact old_face_value P u v N g hn BassH1Order.middleIndex
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace)
      (BassH1Order.middlePlus_monotone i) (o.middlePlus i) n z x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact old_face_value P u v N g hn BassH1Order.middleIndex
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace)
      (BassH1Order.middleMinus_monotone i) (o.middleMinus i) n z x

include hn o in
/-- The original positive H1 product keeps both parameters and all native inputs. -/
theorem old_product_plus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.plusProductParameter.{u} (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.plusProductParameter.{u} (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.plusProductIndex
      (BassH1Components.plusParameter.{u} (r, t))), x) = _
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.plusProductIndex (BassH1Components.plusParameter.{u} (r, t)), x)
  obtain ⟨i, j, z, hz⟩ := BassH1Support.plus_support.{u} r t
  rw [← hz]
  exact old_face_value P u v N g hn BassH1Order.plusProductIndex (BassH1Support.edgePairFace i j)
    (BassH1Order.plusProduct_monotone i j) (o.productPlus i j) n z x

include hn o in
/-- The original inverse H1 product keeps both parameters and all native inputs. -/
theorem old_product_minus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.minusProductParameter.{u} (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.minusProductParameter.{u} (r, t), x) := by
  change prespectrumSimplexFamily (nativeSimplex P u v N) n
    (StdSimplex.map g (StdSimplex.map BassH1Order.minusProductIndex
      (BassH1Components.minusParameter.{u} (r, t))), x) = _
  change _ = prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
    (StdSimplex.map BassH1Order.minusProductIndex (BassH1Components.minusParameter.{u} (r, t)), x)
  obtain ⟨i, j, z, hz⟩ := BassH1Support.minus_support.{u} r t
  rw [← hz]
  exact old_face_value P u v N g hn BassH1Order.minusProductIndex (BassH1Support.edgePairFace i j)
    (BassH1Order.minusProduct_monotone i j) (o.productMinus i j) n z x

include hn o in
/-- The whole original H1 surface survives, with both scalar times independent. -/
theorem old_h1_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n
      (StdSimplex.map g (BassH1Order.h1Parameter.{u} (r, t)), x) =
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (BassH1Order.h1Parameter.{u} (r, t), x) := by
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [BassH1Order.h1_lower]
    exact old_first_value P u v N f g hn o n s t x
  · rcases three_cover t with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [BassH1Order.h1_plus_cell]
      exact old_product_plus_value P u v N f g hn o n s q x
    · rw [BassH1Order.h1_middle_cell]
      exact old_middle_value P u v N f g hn o n s q x
    · rw [BassH1Order.h1_minus_cell]
      exact old_product_minus_value P u v N f g hn o n s q x

end Quillen.PerfectComplexes.BassMFamilyTransfer

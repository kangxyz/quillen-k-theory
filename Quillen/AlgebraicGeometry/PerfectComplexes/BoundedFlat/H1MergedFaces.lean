/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedReferenceReindex

/-! Every actual supported component face is retained in the common reference simplex. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire original old diagram agrees on every face with proved support order. -/
theorem old_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋62⦌)
    (h : Monotone (BassH1Order.oldIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (supportedFace BassH1Order.oldIndex α h) =
      (BassH0Merged.simplex P u v).face α := by
  exact supported_reference_face (BassOverlap.commonReference P u v)
    (BassH0Merged.nodes P u v) (nodes P u v)
    BassH1Order.oldIndex (old_nodes P u v) α h

/-- All original levels and inputs retain the unchanged old family on that supported face. -/
theorem old_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋62⦌)
    (h : Monotone (BassH1Order.oldIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassH1Order.oldIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (supportedFace BassH1Order.oldIndex α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, old_face]
  exact (prespectrumSimplexFamily_face
    (BassH0Merged.simplex P u v) α n z x).symm

/-- The entire original first diagram agrees on every face with proved support order. -/
theorem first_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassH1Order.firstIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (supportedFace BassH1Order.firstIndex α h) =
      (BassH1Components.firstSimplex P u v).face α := by
  rw [← BassH1References.first_original P u v]
  exact supported_reference_face (BassOverlap.commonReference P u v)
    (BassH1References.firstNodes P u v) (nodes P u v)
    BassH1Order.firstIndex (first_nodes P u v) α h

/-- All original levels and inputs retain the unchanged first family on that supported face. -/
theorem first_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassH1Order.firstIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassH1Order.firstIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH1Components.firstSimplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (supportedFace BassH1Order.firstIndex α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, first_face]
  exact (prespectrumSimplexFamily_face
    (BassH1Components.firstSimplex P u v) α n z x).symm

/-- The entire original middle diagram agrees on every face with proved support order. -/
theorem middle_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassH1Order.middleIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (supportedFace BassH1Order.middleIndex α h) =
      (BassH1Components.middleSimplex P u v).face α := by
  rw [← BassH1References.middle_original P u v]
  exact supported_reference_face (BassOverlap.commonReference P u v)
    (BassH1References.middleNodes P u v) (nodes P u v)
    BassH1Order.middleIndex (middle_nodes P u v) α h

/-- All original levels and inputs retain the unchanged middle family on that supported face. -/
theorem middle_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (BassH1Order.middleIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassH1Order.middleIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH1Components.middleSimplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (supportedFace BassH1Order.middleIndex α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, middle_face]
  exact (prespectrumSimplexFamily_face
    (BassH1Components.middleSimplex P u v) α n z x).symm

/-- The entire original plus diagram agrees on every face with proved support order. -/
theorem plus_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋24⦌)
    (h : Monotone (BassH1Order.plusProductIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (supportedFace BassH1Order.plusProductIndex α h) =
      (BassH1Components.chartProduct P u v (underToLaurent R)).face α := by
  rw [← BassH1References.chart_original P u v (underToLaurent R)
    (laurentPlus_projection P b)]
  exact supported_reference_face (BassOverlap.commonReference P u v)
    (BassH1References.chartNodes P u v (underToLaurent R)
      (laurentPlus_projection P b)) (nodes P u v)
    BassH1Order.plusProductIndex (plus_nodes P u v) α h

/-- All original levels and inputs retain the unchanged plus family on that supported face. -/
theorem plus_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋24⦌)
    (h : Monotone (BassH1Order.plusProductIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassH1Order.plusProductIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurent R)) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (supportedFace BassH1Order.plusProductIndex α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, plus_face]
  exact (prespectrumSimplexFamily_face
    (BassH1Components.chartProduct P u v (underToLaurent R)) α n z x).symm

/-- The entire original minus diagram agrees on every face with proved support order. -/
theorem minus_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋24⦌)
    (h : Monotone (BassH1Order.minusProductIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (supportedFace BassH1Order.minusProductIndex α h) =
      (BassH1Components.chartProduct P u v (underToLaurentInvert R)).face α := by
  rw [← BassH1References.chart_original P u v (underToLaurentInvert R)
    (laurentMinus_projection P b)]
  exact supported_reference_face (BassOverlap.commonReference P u v)
    (BassH1References.chartNodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P b)) (nodes P u v)
    BassH1Order.minusProductIndex (minus_nodes P u v) α h

/-- All original levels and inputs retain the unchanged minus family on that supported face. -/
theorem minus_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋24⦌)
    (h : Monotone (BassH1Order.minusProductIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map BassH1Order.minusProductIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurentInvert R)) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (supportedFace BassH1Order.minusProductIndex α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, minus_face]
  exact (prespectrumSimplexFamily_face
    (BassH1Components.chartProduct P u v (underToLaurentInvert R)) α n z x).symm

end Quillen.PerfectComplexes.BassH1Merged

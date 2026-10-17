/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenPathCube

/-! Whole seed-path transport of the original chosen cube and its exact common J0 path. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenPathTransport
open CoefficientBassSeedChosenPathCube
/-- Continuous postcomposition on the space of whole paths. -/
def postPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(C(I, X), C(I, Y)) :=
  ⟨fun γ ↦ f.comp γ, ContinuousMap.continuous_postcomp f⟩

private theorem postPath_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (γ : C(I, X)) (s : I) : postPath f γ s = f (γ s) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c) (h : p ≫ q = p' ≫ q')

/-- Transport every point of a whole seed path, retaining its original seed clock. -/
def pathMap : C(C(I, CoefficientBassPositiveC0CarrierSeed.Carrier P p q),
    C(I, CoefficientBassPositiveC0CarrierSeed.Carrier P p' q')) :=
  postPath (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)

/-- Whole-path transport evaluates by the original point transport. -/
theorem pathMap_apply (γ : C(I, CoefficientBassPositiveC0CarrierSeed.Carrier P p q)) (s : I) :
    pathMap P p q p' q' h γ s =
      CoefficientBassNegativeCarrierReference.transport P p q p' q' h (γ s) :=
  postPath_apply (CoefficientBassNegativeCarrierReference.transport P p q p' q' h) γ s

/-- The common path equation is the proved full J0 surface equation, before evaluation. -/
theorem shared_path (r : I) :
    pathMap P p q p' q' h
      (surfacePath (CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy r) =
    surfacePath (CoefficientBassCompositeJ0Conjugation.reverseComparison P p' q').toHomotopy r := by
  apply ContinuousMap.ext
  intro s
  exact (pathMap_apply P p q p' q' h _ s).trans
    ((congrArg (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)
      (surfacePath_apply _ r s)).trans
      ((CoefficientBassCompositeJ0ConjugationTransport.reverseComparison_transport
        P p q p' q' h r s).trans (surfacePath_apply _ r s).symm))

/-- Mapping the selected cube uses the original values; no extension is selected again. -/
def mappedComparison :=
  (comparison P p q).map (pathMap P p q p' q' h)

/-- All three original coordinates survive this full-reference transport. -/
theorem mappedComparison_apply (r t s : I) :
    mappedComparison P p q p' q' h (r, t) s =
      CoefficientBassNegativeCarrierReference.transport P p q p' q' h
        ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier ((r, t), s)) := by
  have hm := Path.Homotopy.map_apply (comparison P p q) (pathMap P p q p' q' h) (r, t)
  exact (congrArg (fun γ ↦ γ s) hm).trans
    ((pathMap_apply P p q p' q' h _ s).trans
      (congrArg (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)
        (comparison_apply P p q r t s)))

end Quillen.PerfectComplexes.CoefficientBassSeedChosenPathTransport

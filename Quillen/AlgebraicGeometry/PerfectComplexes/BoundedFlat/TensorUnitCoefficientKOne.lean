/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRepresentative
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison

/-!
# The normalized first coefficient square represents the original forward unit K-one class

Realize the independently constructed and explicitly zero-normalized coefficient square with
separate object-row and automorphism-nerve parameters. Its actual loop-space path is equal to the
original weak-object square path. The existing inverse-prefix `loopKOneNormalization` therefore
gives the original forward unit class, including through the literal perfect inclusion.
No tensor product with arbitrary second K-inputs is inferred from this coefficient-class result.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Convexity
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes

/-- The actual coefficient-square realization; nerve time is first and object-row time second. -/
def tensorUnitCoefficientSquareValue (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    C(unitInterval × unitInterval, (boundedFlatPerfectWaldhausen X).Delooping) :=
  ⟨fun z => bisimplexRealization (boundedFlatPerfectWaldhausen X)
      (tensorUnitCoefficientSquare X r).val
      ((isSimplex₂_diagonal_iff _ _ _).mpr (tensorUnitCoefficientSquare X r).property)
      (StdSimplex.homeomorphI.symm z.2, StdSimplex.homeomorphI.symm z.1), by fun_prop⟩

/-- The whole two-parameter square is the original forward weak-object square, with no flip. -/
theorem tensorUnitCoefficientSquareValue_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (s t : unitInterval) :
    tensorUnitCoefficientSquareValue X r (s, t) =
      (boundedFlatPerfectWaldhausen X).weakObjectSquareLoopPath (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) s t := by
  exact congrArg (fun A : (sSet (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq) _⦋1⦌ =>
    bisimplexRealization (boundedFlatPerfectWaldhausen X) A.val
      ((isSimplex₂_diagonal_iff _ _ _).mpr A.property)
      (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s))
    (tensorUnitCoefficientSquare_eq X r)

/-- Both object-row endpoints and both whole nerve faces retain their original basepoints. -/
def tensorUnitCoefficientSquareTrack (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    ((boundedFlatPerfectWaldhausen X).kZeroObjectLoop (boundedFlatRankOne X)).Homotopy
      ((boundedFlatPerfectWaldhausen X).kZeroObjectLoop (boundedFlatRankOne X)) where
  toFun := tensorUnitCoefficientSquareValue X r
  continuous_toFun := (tensorUnitCoefficientSquareValue X r).continuous
  map_zero_left t := by
    rw [tensorUnitCoefficientSquareValue_eq]
    exact congrArg (fun p => p t)
      ((boundedFlatPerfectWaldhausen X).weakObjectSquareLoopPath
        (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).source
  map_one_left t := by
    rw [tensorUnitCoefficientSquareValue_eq]
    exact congrArg (fun p => p t)
      ((boundedFlatPerfectWaldhausen X).weakObjectSquareLoopPath
        (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).target
  prop' s t ht := by
    change tensorUnitCoefficientSquareValue X r (s, t) = _
    rw [tensorUnitCoefficientSquareValue_eq]
    exact ((boundedFlatPerfectWaldhausen X).weakObjectSquareTrack
      (boundedFlatRankOneUnit X r).hom
      ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)).prop' s t ht

/-- Curry the actual two-parameter tensor coefficient square into its original loop component. -/
def tensorUnitCoefficientLoopPath (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    Path ((boundedFlatPerfectWaldhausen X).kZeroObjectLoop (boundedFlatRankOne X))
      ((boundedFlatPerfectWaldhausen X).kZeroObjectLoop (boundedFlatRankOne X)) where
  toFun s := (tensorUnitCoefficientSquareTrack X r).eval s
  continuous_toFun :=
    Path.continuous_uncurry_iff.mp (tensorUnitCoefficientSquareTrack X r).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The entire coefficient loop path, before class formation, is the original automorphism path. -/
theorem tensorUnitCoefficientLoopPath_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientLoopPath X r =
      (boundedFlatPerfectWaldhausen X).weakObjectSquareLoopPath (boundedFlatRankOneUnit X r).hom
        ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact tensorUnitCoefficientSquareValue_eq X r s t

/-- Normalize the actual coefficient path by the pre-existing inverse-prefix K-one class map. -/
def tensorUnitCoefficientKOneClass (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectWaldhausen X).K 1 :=
  loopKOneNormalization ((boundedFlatPerfectWaldhausen X).kZeroObjectLoop (boundedFlatRankOne X))
    ⟦tensorUnitCoefficientLoopPath X r⟧

/-- The independently realized coefficient square represents the original forward unit class. -/
theorem tensorUnitCoefficientKOneClass_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    tensorUnitCoefficientKOneClass X r =
      (boundedFlatPerfectWaldhausen X).automorphismKOneClass (boundedFlatRankOneUnit X r) := by
  unfold tensorUnitCoefficientKOneClass
  rw [tensorUnitCoefficientLoopPath_eq]
  rfl

/-- The literal perfect inclusion retains the original rank-one forward unit K-one class. -/
theorem tensorUnitCoefficientKOneClass_inclusion (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    KMap (boundedFlatPerfectInclusion_exact X) 1 (tensorUnitCoefficientKOneClass X r) =
      perfectGlobalUnitKOneClass X r (rankOnePerfect X) := by
  rw [tensorUnitCoefficientKOneClass_eq, KMap_automorphismKOneClass,
    boundedFlatRankOneUnit_global]
  apply congrArg (perfectWaldhausen X).automorphismKOneClass
  apply Iso.ext
  apply (locallyPerfect X).ι.map_injective
  change (boundedFlatPerfect X).ι.map
      ((boundedFlatPerfectGlobalUnitIso X r).hom.app (boundedFlatRankOne X)) =
    (locallyPerfect X).ι.map ((perfectGlobalUnitIso X r).hom.app (rankOnePerfect X))
  rw [boundedFlatPerfectGlobalUnitIso_hom_original]
  simp only [perfectGlobalUnitIso, Functor.fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rfl

end Quillen.PerfectComplexes

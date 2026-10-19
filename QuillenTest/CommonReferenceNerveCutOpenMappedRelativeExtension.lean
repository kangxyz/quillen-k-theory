/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenMappedRelativeExtension

/-! Exact route recovery and independent parameters after the actual native cone map. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommonReferenceNerve.CutOpenCarrier
open scoped Topology unitInterval
universe u
namespace QuillenTest.CommonReferenceNerveCutOpenMappedRelativeExtension
variable {V W T : Model.{u}} {F : V ⟶ W} {J : W ⟶ T} {G : V ⟶ T}
  {ε₀ ε₁ : G.functor ≅ (F ≫ J).functor}
  (B : RelativeBoundary F J G ε₀ ε₁)
  {P : LoopPrespectrum.{u}} (j : nativeCone J ⟶ P)
  {f g : prespectrum V ⟶ parameterLooping P} (H K : Homotopy f g)
  (h : B.RecoversMappedRoutes j H K)

/-- All three times retain the original carrier and the prescribed postmap. -/
theorem exact_family (n : ℕ) (r s t : I) (x : (prespectrum V).space n) :
    Path.toContinuousMap ((B.mappedRelativeComparison j H K h).level n (r, (s, x))) t =
      j.map n (nativeEval F J G ε₀ ε₁ n (B.carrier ((r, s), t)) x) :=
  B.mappedRelativeComparison_apply j H K h n r s t x

/-- The initial comparison face is the given first whole route. -/
theorem first_route (n : ℕ) (s : I) (x : (prespectrum V).space n) :
    (B.mappedRelativeComparison j H K h).level n (0, (s, x)) = H.level n (s, x) :=
  ((B.mappedRelativeComparison j H K h).level n).apply_zero (s, x)

/-- The final comparison face is the given second whole route. -/
theorem last_route (n : ℕ) (s : I) (x : (prespectrum V).space n) :
    (B.mappedRelativeComparison j H K h).level n (1, (s, x)) = K.level n (s, x) :=
  ((B.mappedRelativeComparison j H K h).level n).apply_one (s, x)

/-- Structure time remains independent of comparison, route, and seed time. -/
theorem four_times (n : ℕ) (r s t v : I) (x : (prespectrum V).space n) :
    Path.toContinuousMap ((B.mappedRelativeComparison j H K h).level (n + 1)
      (r, (s, (prespectrum V).structureMap n x t))) v =
    Path.toContinuousMap ((parameterLooping P).structureMap n
      ((B.mappedRelativeComparison j H K h).level n (r, (s, x))) t) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v)
    ((B.mappedRelativeComparison j H K h).comm n r s x t)

end QuillenTest.CommonReferenceNerveCutOpenMappedRelativeExtension

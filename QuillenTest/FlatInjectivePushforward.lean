/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Pushforward.FlatInjective

/-! Consumers of the original flat geometric adjunction on bounded injective targets. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.FlatInjectivePushforward

open Quillen
/-- The standard ambient derived category of actual module sheaves. -/
local instance standardDerived (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- Any bounded-below injective target produces the actual K-injective direct-image target. -/
theorem original_target {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (I : CochainComplex Z.Modules ℤ) (a : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n)) :
    ((PerfectComplexes.pushforwardComplex f).obj I).IsKInjective :=
  AlgebraicGeometry.Scheme.Modules.pushforward_isKInjective_of_flat f I a hb hi

/-- Transporting a genuine derived arrow and its inverse transport loses no information. -/
theorem original_derived_roundtrip {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (K : CochainComplex X.Modules ℤ) (I : CochainComplex Z.Modules ℤ) (a : ℤ)
    (hb : ∀ n, n < a → IsZero (I.X n)) (hi : ∀ n, Injective (I.X n))
    (α : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((PerfectComplexes.pushforwardComplex f).obj I)) :
    AlgebraicGeometry.Scheme.Modules.flatPushforwardDerivedHomEquiv f K I a hb hi
        ((AlgebraicGeometry.Scheme.Modules.flatPushforwardDerivedHomEquiv f K I a hb hi).symm α) = α
          :=
  (AlgebraicGeometry.Scheme.Modules.flatPushforwardDerivedHomEquiv f K I a hb hi).apply_symm_apply α

end QuillenTest.FlatInjectivePushforward

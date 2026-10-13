/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ComplexPushforward
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatPullback
public import Quillen.Algebra.Homology.Adjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Flat direct image of bounded-below injective targets

Flatness
makes the original direct image preserve injective sheaves. No preservation
of perfect objects or acyclicity of quasicoherent coefficients is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.SchemeSheaf
/-- The standard ambient derived category of actual module sheaves. -/
local instance standardDerivedSheaves (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

/-- The right adjoint to exact flat pullback preserves actual injective module sheaves. -/
theorem injective_pushforward_of_flat {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (M : Z.Modules) [Injective M] : Injective ((Scheme.Modules.pushforward f).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).map_injective M inferInstance

/-- Lower-bounded termwise injective targets stay K-injective under flat direct image. -/
theorem pushforward_isKInjective_of_flat {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (I : CochainComplex Z.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n)) :
    ((PerfectComplexes.pushforwardComplex f).obj I).IsKInjective := by
  let J := (PerfectComplexes.pushforwardComplex f).obj I
  have : J.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff J a).mpr
    (fun n hn ↦ (Scheme.Modules.pushforward f).map_isZero (hbound n hn))
  have (n : ℤ) : Injective (J.X n) := by
    let := hinj n
    exact injective_pushforward_of_flat f (I.X n)
  exact CochainComplex.isKInjective_of_injective J a

/-- The original geometric adjunction gives actual derived Hom transport at an injective model. -/
def flatPushforwardDerivedHomEquiv {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (K : CochainComplex X.Modules ℤ) (I : CochainComplex Z.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n)) :
    (DerivedCategory.Q.obj (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj I) ≃+
    (DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((PerfectComplexes.pushforwardComplex f).obj I)) := by
  have : I.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff I a).mpr hbound
  let := hinj
  let := CochainComplex.isKInjective_of_injective I a
  let : CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I) :=
    pushforward_isKInjective_of_flat f I a hbound hinj
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).cochainDerivedHomEquivOfKInjective K I

/-- Original chain arrows retain their actual sheaf-adjoint image under derived transport. -/
@[simp]
theorem flatPushforwardDerivedHomEquiv_map {Z X : Scheme.{u}} (f : Z ⟶ X) [Flat f]
    (K : CochainComplex X.Modules ℤ) (I : CochainComplex Z.Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (s : ((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj K ⟶ I) :
    flatPushforwardDerivedHomEquiv f K I a hbound hinj (DerivedCategory.Q.map s) =
      DerivedCategory.Q.map
        (((Scheme.Modules.pullbackPushforwardAdjunction f).mapHomologicalComplex (.up ℤ)).homEquiv
          K I s) := by
  have : I.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff I a).mpr hbound
  let := hinj
  let := CochainComplex.isKInjective_of_injective I a
  let : CochainComplex.IsKInjective
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I) :=
    pushforward_isKInjective_of_flat f I a hbound hinj
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).cochainDerivedHomEquivOfKInjective_map
    K I s

end Quillen.SchemeSheaf

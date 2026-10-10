/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.BoundedFlat.SupportComparison

/-! # Original relative-open and supported bounded-flat comparisons

The ambient scheme is quasi-compact; its open is arbitrary. Every statement
retains the original relative target or support map rather than replacing it
by all perfect K-theory of the open.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.BoundedFlatRelativeComparison

/-- Every original supported K-zero class has an actual bounded-flat model class. -/
theorem supported_zero_representative {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace X] (x : PerfectSupportedK j 0) :
    ∃ y, boundedFlatPerfectSupportedToPerfectSupportedKMap j 0 y = x :=
  (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective j 0).surjective x

/-- Every relative-open class has a model representative without extending an arbitrary open object. -/
theorem relative_representative {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace X] (n : ℕ) (x : PerfectOpenK j n) :
    ∃ y, boundedFlatPerfectOpenToPerfectOpenKMap j n y = x :=
  (boundedFlatPerfectOpenToPerfectOpenKMap_bijective j n).surjective x

/-- Supported classes are detected by the actual original inclusion comparison. -/
theorem supported_detection {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace X] (n : ℕ)
    (x y : BoundedFlatPerfectSupportedK j n)
    (h : boundedFlatPerfectSupportedToPerfectSupportedKMap j n x =
      boundedFlatPerfectSupportedToPerfectSupportedKMap j n y) : x = y :=
  (boundedFlatPerfectSupportedToPerfectSupportedKMap_bijective j n).injective h

/-- Forgetting support retains its original K-map on actual representatives. -/
theorem original_support_square {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (x : BoundedFlatPerfectSupportedK j n) :
    perfectSupportedKMap j n (boundedFlatPerfectSupportedToPerfectSupportedKMap j n x) =
      boundedFlatPerfectToPerfectKMap X n (boundedFlatPerfectSupportedKMap j n x) :=
  DFunLike.congr_fun (boundedFlatPerfectSupportedToPerfectSupported_comp j n) x

/-- The original change-of-weak-equivalences map commutes even in degree zero. -/
theorem original_coarse_square {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (x : BoundedFlatPerfectK X 0) :
    boundedFlatPerfectOpenToPerfectOpenKMap j 0 (boundedFlatPerfectOpenKMap j 0 x) =
      perfectOpenKMap j 0 (boundedFlatPerfectToPerfectKMap X 0 x) :=
  DFunLike.congr_fun (boundedFlatPerfectOpenToPerfectOpen_comp j 0) x

/-- Actual supported mapping cones retain acyclicity on the open. -/
theorem actual_supported_cone {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Complex X} (hK : boundedFlatPerfectSupported j K)
    (hL : boundedFlatPerfectSupported j L) (f : K ⟶ L) :
    ((restrict j).obj (CochainComplex.mappingCone f)).Acyclic :=
  (boundedFlatPerfectSupported_mappingCone j hK hL f).2

end Quillen.Tests.BoundedFlatRelativeComparison

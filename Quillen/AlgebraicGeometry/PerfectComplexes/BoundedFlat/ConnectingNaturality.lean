/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenFibration
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback
public import Quillen.Waldhausen.Fibration.ConnectingNaturality

/-! # Naturality of the actual bounded-flat supported connecting homomorphism -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration

/-- Flattening the actual relative-acyclic objects commutes with geometric pullback. -/
theorem boundedFlatPerfectAcyclicSupportedKEquiv_pullback
    {A B : Quillen.Scheme.OpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback f n).comp
      (boundedFlatPerfectAcyclicSupportedKEquiv B.obj.hom n).toMonoidHom =
    (boundedFlatPerfectAcyclicSupportedKEquiv A.obj.hom n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedFlatPerfectOpenNested B.obj.hom)
        (boundedFlatPerfectOpenNested A.obj.hom) (boundedFlatPerfectPullback_exact f.hom.right)
        (boundedFlatPerfectOpenPullback_exact f)) n) := by
  change (KMap (boundedFlatPerfectSupportedPullback_exact f) n).comp
      (KMap (boundedFlatPerfectAcyclicToSupported_exact B.obj.hom) n) =
    (KMap (boundedFlatPerfectAcyclicToSupported_exact A.obj.hom) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- The original supported boundary commutes with arbitrary open-pair pullback. -/
theorem boundedFlatPerfectOpenConnectingHom_pullback
    {A B : Quillen.Scheme.OpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    (boundedFlatPerfectSupportedKPullback f n).comp (boundedFlatPerfectOpenConnectingHom B.obj.hom
      n) =
    (boundedFlatPerfectOpenConnectingHom A.obj.hom n).comp (boundedFlatPerfectOpenKPullback f (n+1))
      := by
  unfold boundedFlatPerfectOpenConnectingHom boundedFlatPerfectOpenKPullback
  rw [← MonoidHom.comp_assoc, boundedFlatPerfectAcyclicSupportedKEquiv_pullback,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedFlatPerfectOpenNested B.obj.hom) (boundedFlatPerfectOpenNested A.obj.hom)
      (boundedFlatPerfectPullback_exact f.hom.right) (boundedFlatPerfectOpenPullback_exact f),
    ← MonoidHom.comp_assoc]

/-- Original bounded-flat inclusion and acyclic flattening commute literally on K-maps. -/
theorem boundedFlatPerfectAcyclicSupportedKEquiv_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (boundedFlatPerfectSupportedToPerfectSupportedKMap j n).comp
      (boundedFlatPerfectAcyclicSupportedKEquiv j n).toMonoidHom =
    (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
      (KMap (acyclicFunctor_exact (boundedFlatPerfectOpenNested j) (perfectOpenNested j)
        (boundedFlatPerfectInclusion_exact X) (boundedFlatPerfectOpenInclusion_exact j)) n) := by
  change (KMap (boundedFlatPerfectSupportedInclusion_exact j) n).comp
      (KMap (boundedFlatPerfectAcyclicToSupported_exact j) n) =
    (KMap (perfectAcyclicToSupported_exact j) n).comp _
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

/-- The actual inclusion compares the original supported boundaries, without qc assumptions. -/
theorem boundedFlatPerfectOpenConnectingHom_comparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (boundedFlatPerfectSupportedToPerfectSupportedKMap j n).comp
      (boundedFlatPerfectOpenConnectingHom j n) =
    (perfectOpenConnectingHom j n).comp (boundedFlatPerfectOpenToPerfectOpenKMap j (n+1)) := by
  unfold boundedFlatPerfectOpenConnectingHom perfectOpenConnectingHom
    boundedFlatPerfectOpenToPerfectOpenKMap
  rw [← MonoidHom.comp_assoc, boundedFlatPerfectAcyclicSupportedKEquiv_comparison,
    MonoidHom.comp_assoc, changeWeakConnectingHom_natural
      (boundedFlatPerfectOpenNested j) (perfectOpenNested j)
      (boundedFlatPerfectInclusion_exact X) (boundedFlatPerfectOpenInclusion_exact j),
    ← MonoidHom.comp_assoc]

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.ComponentExtension
public import Quillen.Topology.LocalCoefficients.SupportedChains

/-!
# Consumers for genuine path-component extension by zero

The extension works in independent coefficient universes. The original ambient
path transport is retained, and the support theorem applies to the actual
component-inclusion chain map without an openness hypothesis.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits Quillen Quillen.LocalCoefficients
universe u v
variable {Y : Type u} [TopologicalSpace Y] (y : Y)

example (A : System.{u, v} (pathComponent y)) :
    pullback (FundamentalGroupoidComponent.inclusion y) (componentExtension y A) ≅ A :=
  componentExtensionPullbackIso y A

example (A : System.{u, v} (pathComponent y)) (z : Y) (hz : z ∉ pathComponent y) :
    IsZero (fiber (componentExtension y A) z) :=
  componentExtension_isZero_off y A z hz

example (A : System.{u, v} (pathComponent y)) {a b : pathComponent y}
    (p : Path a.val b.val) :
    transport (componentExtension y A) p ≫
        (componentExtensionPullbackIso y A).hom.app (FundamentalGroupoid.mk b) =
      (componentExtensionPullbackIso y A).hom.app (FundamentalGroupoid.mk a) ≫
        transport A (pathComponentPath p) :=
  componentExtension_transport y A p

example (A : System.{u, v} (pathComponent y)) (hA : AbelianMonodromy A) :
    AbelianMonodromy (componentExtension y A) :=
  componentExtension_abelianMonodromy y A hA

example (A : System.{u, u} (pathComponent y)) :
    IsIso (pushforwardChainMap (subspaceInclusion (pathComponent y))
      (componentExtension y A)) :=
  pathComponentInclusion_pushforwardChainMap_isIso_of_support y
    (componentExtension y A) (componentExtension_isZero_off y A)

example : (FundamentalGroupoidComponent.inclusionMap y).Full := inferInstance
example : (FundamentalGroupoidComponent.inclusionMap y).Faithful := inferInstance

example : (FundamentalGroupoidComponent.equivalence y).functor ⋙
    (FundamentalGroupoidComponent.componentProperty y).ι =
      FundamentalGroupoidComponent.inclusionMap y :=
  FundamentalGroupoidComponent.equivalence_forward y

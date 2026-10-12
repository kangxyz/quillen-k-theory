/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.ClassifyingSpace.ExtensionProjection

/-! Consumers of the actual quotient isomorphism and original zero-vertex path. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits ZeroObject Quillen
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

example (A : C) :
    E.extensionProjectionObject (E.extensionTotalOf (𝟙 A) (E.inflation.id_mem A)) ≅
      (0 : C) := E.identityQuotientIsoZero A

example : Path (E.extensionProjectionRealization (classifyingSpacePoint E.extensionTotalPoint))
    (classifyingSpacePoint (Q.of E.deflation E.inflation (0 : C))) :=
  E.extensionProjectionBasepointPath

example (x : E.ExtensionTotal) :
    E.extensionProjectionRealization (classifyingSpacePoint x) =
      classifyingSpacePoint (E.extensionProjection.obj x) :=
  E.extensionProjectionRealization_point x

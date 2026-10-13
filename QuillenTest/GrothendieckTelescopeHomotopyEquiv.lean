/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.ClassifyingSpace.GrothendieckTelescopeHomotopyEquiv
/-! The global telescope equivalence retains the original stage map. -/
noncomputable section
open CategoryTheory Quillen
universe u
example (F : ℕ ⥤ Cat.{u, u})
    (e : ∀ {n m : ℕ} (_ : n ⟶ m),
      ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj n)) (ClassifyingSpace (F.obj m)))
    (he : ∀ {n m : ℕ} (f : n ⟶ m),
      (e f).toFun = (classifyingSpaceMap (F.map f).toFunctor).hom) (n : ℕ) :
    (GrothendieckTelescope.fiberInclusionHomotopyEquiv F e he n).toFun =
      (classifyingSpaceMap (Grothendieck.ι F n)).hom :=
  GrothendieckTelescope.fiberInclusionHomotopyEquiv_toFun F e he n

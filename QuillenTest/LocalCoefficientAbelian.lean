/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.Abelian
import Quillen.Topology.LocalCoefficients.Homology

/-! Actual path transport and induced coefficient homology automorphisms. -/

open CategoryTheory Quillen.LocalCoefficients
noncomputable section
universe u

variable {X : Type u} [TopologicalSpace X] {A : System.{u, u} X}

example (hA : AbelianMonodromy A) {b x : X} (g : Path b b) (p : Path b x) :
    (pathLoopCorrectionIso hA g).hom.app (FundamentalGroupoid.mk x) =
      transport A p.symm ≫ transport A g ≫ transport A p :=
  pathLoopCorrectionIso_hom_app hA g p

example (hA : AbelianMonodromy A) {b : X} (g : Path b b) (n : ℕ) :
    IsIso (coefficientHomologyMap (pathLoopCorrectionIso hA g).hom n) := by
  change IsIso (coefficientHomologyIso (pathLoopCorrectionIso hA g) n).hom
  infer_instance

example (hA : AbelianMonodromy A) {b x : X} (g : Path b b) (p q : Path b x) :
    transport A p.symm ≫ transport A g ≫ transport A p =
      transport A q.symm ≫ transport A g ≫ transport A q := by
  rw [← pathLoopCorrectionIso_hom_app hA g p, ← pathLoopCorrectionIso_hom_app hA g q]

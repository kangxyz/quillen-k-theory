/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.CylinderShift

/-! Consumer checks for the genuine arbitrary-local-system cylinder shift. -/

open CategoryTheory CategoryTheory.Limits
open Quillen.LocalCoefficients
open scoped unitInterval

universe u

noncomputable section

variable (X : Type u) [TopologicalSpace X]

example (A : System.{u, u} X) (n : ℕ) :
    (relativeSingularChainComplex (cylinderBoundary X)
      (pullback (cylinderProjection X) A)).homology (n + 1) ≅ homology A n :=
  cylinderPullbackRelativeHomologyIso X A n

example (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderRelativeHomologyIso X A n).hom =
      (cylinderBoundarySequence_shortExact X A).δ (n + 1) n rfl ≫
        (cylinderBoundaryAdditionIso X A n).inv ≫ biprod.fst :=
  cylinderRelativeHomologyIso_hom X A n

example (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderRelativeHomologyIso X A n).inv ≫
      (cylinderBoundarySequence_shortExact X A).δ (n + 1) n rfl ≫
        (cylinderBoundaryAdditionIso X A n).inv =
      biprod.lift (𝟙 (homology A n)) (-𝟙 (homology A n)) :=
  cylinderRelativeHomologyIso_inv_δ X A n

example (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    (cylinderBoundaryAdditionIso X A n).hom ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X)) A n =
      biprod.desc (𝟙 (homology A n)) (𝟙 (homology A n)) :=
  cylinderBoundaryAdditionIso_hom_inclusion X A n

example (A : System.{u, u} (unitInterval × X)) (t : unitInterval) :
    (relativeSingularChainComplex (cylinderSlice X t) A).Acyclic :=
  cylinderSlice_relative_acyclic X t A

example (A : System.{u, u} (unitInterval × X)) :
    IsZero ((relativeSingularChainComplex (cylinderBoundary X) A).homology 0) :=
  cylinderRelativeHomology_zero X A

example (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackBoundaryHomologyIso X A n).hom ≫
      pushforwardHomologyMap (subspaceInclusion (cylinderBoundary X))
        (pullback (cylinderProjection X) A) n ≫
      pushforwardHomologyMap (cylinderProjection X) A n =
      biprod.desc (𝟙 (homology A n)) (𝟙 (homology A n)) :=
  cylinderPullbackBoundaryHomologyIso_hom_inclusion X A n

example (A : System.{u, u} X) (n : ℕ) :
    (cylinderPullbackRelativeHomologyIso X A n).inv ≫
      (cylinderBoundarySequence_shortExact X (pullback (cylinderProjection X) A)).δ
        (n + 1) n rfl ≫ (cylinderPullbackBoundaryHomologyIso X A n).inv =
      biprod.lift (𝟙 (homology A n)) (-𝟙 (homology A n)) :=
  cylinderPullbackRelativeHomologyIso_inv_δ X A n

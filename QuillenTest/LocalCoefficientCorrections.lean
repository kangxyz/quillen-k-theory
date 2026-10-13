/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.FiniteCorrections
import Quillen.Topology.LocalCoefficients.CategoryTracks
import Quillen.Topology.LocalCoefficients.HomotopyCorrection
import Quillen.Topology.LocalCoefficients.Homology

/-! Consumers of genuine finite corrections and coherent categorical tracks. -/

noncomputable section
open CategoryTheory Quillen Quillen.LocalCoefficients
universe u

example {X : Type u} [TopologicalSpace X] {A : System.{u, u} X}
    (hA : AbelianMonodromy A)
    (l : List (Σ b : FundamentalGroupoid X, b ⟶ b)) (n : ℕ) :
    homology A n ≅ homology A n :=
  coefficientHomologyIso (finiteLoopCorrectionIso hA l) n

example {C D : Type u} [SmallCategory C] [SmallCategory D]
    (A : System.{u, u} (ClassifyingSpace D)) {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    (categoryPullbackFunctor A).map (α ≫ β) =
      (categoryPullbackFunctor A).map α ≫ (categoryPullbackFunctor A).map β :=
  (categoryPullbackFunctor A).map_comp α β

example {C : Type u} [SmallCategory C]
    {A B : System.{u, u} (ClassifyingSpace C)} {η θ : A ⟶ B}
    (h : ∀ c : C, η.app (FundamentalGroupoid.mk (classifyingSpacePoint c)) =
      θ.app (FundamentalGroupoid.mk (classifyingSpacePoint c))) : η = θ :=
  coefficientMap_ext_vertices h

example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H K : f.Homotopy g) {A : System.{u, u} Y}
    (hA : AbelianMonodromy A) (n : ℕ) (x : homology (pullback f A) n) :
    ∃ s : Finset X,
      (∀ a ∈ s, ∀ b ∈ s, Joined (g a) (g b) → Joined a b) →
      ∃ T : A ≅ A,
        coefficientHomologyMap (pullbackMap g T.hom) n
          (coefficientHomologyMap (homotopyPullbackIso H A).hom n x) =
        coefficientHomologyMap (homotopyPullbackIso K A).hom n x :=
  homology_finite_homotopy_correction H K hA n x

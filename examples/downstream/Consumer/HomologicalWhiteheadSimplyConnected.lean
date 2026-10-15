/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected

/-! Independent consumers ask for the complete original weak property and the
actual original homotopy-group map, starting only from ordinary integral homology. -/

@[expose] public section

open Quillen.LocalCoefficients

noncomputable section
open CategoryTheory
universe u
namespace Quillen.Consumer.HomologicalWhiteheadSimplyConnected
open LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]

/-- The weak property includes original target-component coverage. -/
theorem components_of_integral_homology (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficientModule.{u}).map (TopCat.ofHom f))) (y : Y) :
    ∃ x : X, Joined (f x) y :=
  (isWeakHomotopyEquivalence_of_singularHomology_isIso f hH).component_surjective y

/-- Every homotopy map is the unchanged original f-induced map, at every point and degree. -/
theorem homotopy_bijections_of_integral_homology (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficientModule.{u}).map (TopCat.ofHom f))) (x : X) (k : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin k) f (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_singularHomology_isIso f hH).homotopy_bijective x k

end Quillen.Consumer.HomologicalWhiteheadSimplyConnected

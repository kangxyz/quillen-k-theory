/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.HomologicalFirstObstruction
public import Quillen.Topology.LocalCoefficients.RegularFunctoriality

/-!
# Simply connected integral homology equivalences are genuine weak equivalences

Start at one-connectivity, raise the range by the actual cone first obstruction,
and retain every original fiber and basepoint at each induction step. The result
is the existing complete weak-homotopy-equivalence predicate on the original map.
The ordinary singular-homology formulation uses the actual natural chain
comparison, with universe-correct lifted integer coefficients.

No CW-type or universal-cover existence assumption occurs.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u

namespace Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The homology comparison retains the actual original spatial map. -/
@[reassoc]
theorem constantHomologyIso_naturality (f : C(X, Y)) (V : ModuleCat.{u} ℤ) (n : ℕ) :
    pushforwardHomologyMap f (constant Y V) n ≫ (constantHomologyIso (X := Y) V n).hom =
      (constantHomologyIso (X := X) V n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj V).map
          (TopCat.ofHom f) := by
  have h := congrArg (fun η ↦ (HomologicalComplex.homologyFunctor
    (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).map η)
      (constantChainComplexIso_naturality f V)
  simpa [pushforwardHomologyMap, constantHomologyIso,
    AlgebraicTopology.singularHomologyFunctor, HomologicalComplex.homologyMap_comp] using h

/-- Isomorphisms on the actual constant-integral homology maps give precisely
the quasi-isomorphism required by the genuine cone homology theorem. -/
theorem integral_quasiIso_of_homology_isIso (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso (pushforwardHomologyMap f
      (constant Y integralCoefficientModule.{u}) n)) :
    QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) := by
  constructor
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mpr (hH n)

/-- The ordinary singular-homology hypothesis is transported only through
the proved natural isomorphism of the original chain models. -/
theorem integral_quasiIso_of_singularHomology_isIso (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficientModule.{u}).map (TopCat.ofHom f))) :
    QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})) := by
  apply integral_quasiIso_of_homology_isIso f
  intro n
  let := hH n
  apply (isIso_comp_right_iff
    (pushforwardHomologyMap f (constant Y integralCoefficientModule.{u}) n)
    (constantHomologyIso (X := Y) integralCoefficientModule.{u} n).hom).mp
  rw [constantHomologyIso_naturality]
  infer_instance

variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]

/-- Every finite connectivity range holds for the unchanged original map. -/
theorem isHomotopyConnectedMap_of_integral_quasiIso (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})))
    (n : ℕ) : IsHomotopyConnectedMap f n := by
  have hsucc : ∀ m : ℕ, IsHomotopyConnectedMap f (m + 1) := by
    intro m
    induction m with
    | zero => exact isHomotopyConnectedMap_one_of_simplyConnected f x
    | succ m ih =>
      exact ReducedMappingCone.isHomotopyConnectedMap_succ_of_integral_quasiIso f m ih hH
  exact (hsucc n).mono (by omega)

/-- All original path-space fibers have singleton homotopy sets in every
finite degree, with no lost target component or basepoint. -/
theorem fiber_subsingleton_of_integral_quasiIso (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})))
    (y : Y) (z : HomotopyFiber f y) (k : ℕ) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f y) z) :=
  (isHomotopyConnectedMap_of_integral_quasiIso f x hH (k + 1)).fiber_subsingleton
    y z k (Nat.lt_succ_self k)

/-- Integral homology equivalence detects complete weak equivalence between
simply connected spaces, for the original continuous map. -/
theorem isWeakHomotopyEquivalence_of_integral_quasiIso (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u}))) :
    IsWeakHomotopyEquivalence f :=
  (isWeakHomotopyEquivalence_iff_isHomotopyConnectedMap f).mpr
    (isHomotopyConnectedMap_of_integral_quasiIso f x hH)

/-- The formulation using mathlib's actual ordinary singular homology maps. -/
theorem isWeakHomotopyEquivalence_of_singularHomology_isIso (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficientModule.{u}).map (TopCat.ofHom f))) :
    IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_integral_quasiIso f (Classical.choice inferInstance)
    (integral_quasiIso_of_singularHomology_isIso f hH)

end Quillen.LocalCoefficients

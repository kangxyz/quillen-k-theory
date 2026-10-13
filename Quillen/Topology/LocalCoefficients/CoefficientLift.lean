/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Lifting only the coefficient universe

`coefficientLift` places an existing local system in any larger coefficient
universe without changing its underlying space. The linear equivalence of
fibers commutes with every path-class map, actual path transport, and map of
coefficient systems. Unlike `UniverseLift.system`, no spatial lift or chain
complex is required.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v w

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- Enlarge the coefficient universe, retaining the original space and monodromy. -/
def coefficientLift (A : System.{u, v} X) : System.{u, max v w} X :=
  A ⋙ ModuleCat.uliftFunctor.{w, v} ℤ

/-- Coefficient lifting is functorial in maps of the original local systems. -/
def coefficientLiftFunctor (X : Type u) [TopologicalSpace X] :
    System.{u, v} X ⥤ System.{u, max v w} X :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.uliftFunctor.{w, v} ℤ)

/-- The canonical cross-universe linear equivalence on each unchanged point. -/
def coefficientLiftFiberEquiv (A : System.{u, v} X) (x : X) :
    fiber (coefficientLift.{u, v, w} A) x ≃ₗ[ℤ] fiber A x :=
  ULift.moduleEquiv

/-- The fiber equivalence intertwines every original path-class map. -/
@[simp]
theorem coefficientLift_map_down (A : System.{u, v} X)
    {x y : FundamentalGroupoid X} (p : x ⟶ y)
    (a : (coefficientLift.{u, v, w} A).obj x) :
    ((coefficientLift.{u, v, w} A).map p a).down = A.map p a.down := rfl

/-- In particular, it intertwines transport along actual paths. -/
@[simp]
theorem coefficientLiftFiberEquiv_transport (A : System.{u, v} X)
    {x y : X} (p : Path x y) (a : fiber (coefficientLift.{u, v, w} A) x) :
    coefficientLiftFiberEquiv A y (transport (coefficientLift.{u, v, w} A) p a) =
      transport A p (coefficientLiftFiberEquiv A x a) := rfl

/-- Naturality also holds with respect to maps of coefficient systems. -/
@[simp]
theorem coefficientLiftFiberEquiv_naturality {A B : System.{u, v} X}
    (η : A ⟶ B) (x : X) (a : fiber (coefficientLift.{u, v, w} A) x) :
    coefficientLiftFiberEquiv B x
        (((coefficientLiftFunctor.{u, v, w} X).map η).app (FundamentalGroupoid.mk x) a) =
      η.app (FundamentalGroupoid.mk x) (coefficientLiftFiberEquiv A x a) := rfl

/-- Lifting coefficients cannot identify distinct transport morphisms. -/
theorem coefficientLift_map_injective (A : System.{u, v} X)
    {x y : FundamentalGroupoid X} {p q : x ⟶ y}
    (h : (coefficientLift.{u, v, w} A).map p =
      (coefficientLift.{u, v, w} A).map q) : A.map p = A.map q :=
  (ModuleCat.uliftFunctor.{w, v} ℤ).map_injective h

end Quillen.LocalCoefficients

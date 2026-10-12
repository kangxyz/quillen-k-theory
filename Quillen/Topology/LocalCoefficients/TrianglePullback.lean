/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.TriangleHomology

/-! # Triangle maps retain the canonical coefficient pullback comparison -/

@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace Quillen.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

/-- Canonical double-pullback conversion commutes with the actual triangle chain map. -/
theorem triangleSimplicialMap_pullback (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (U : C(Z, W)) (A : System.{u, u} W)
    (w' : U.comp s = (U.comp t).comp h) :
    triangleSimplicialMap h s t w (pullback U A) ≫
        coefficientSimplicialMap (pullbackCompositionIso t U A).inv =
      coefficientSimplicialMap (pullbackCompositionIso s U A).inv ≫
        triangleSimplicialMap h (U.comp s) (U.comp t) w' A := by
  subst s
  apply NatTrans.ext
  funext n
  apply Sigma.hom_ext
  intro σ
  simp [triangleSimplicialMap, coefficientSimplicialMap, pushforwardSimplicialMap,
    coefficientModuleMap, pushforwardModuleMap, chainInclusion, pullbackCompositionIso,
    ← Category.assoc]

/-- The comparison commutes with the genuine induced homology maps. -/
@[reassoc]
theorem triangleHomologyMap_pullback (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, Z))
    (w : s = t.comp h) (U : C(Z, W)) (A : System.{u, u} W)
    (w' : U.comp s = (U.comp t).comp h) (n : ℕ) :
    triangleHomologyMap h s t w (pullback U A) n ≫
        coefficientHomologyMap (pullbackCompositionIso t U A).inv n =
      coefficientHomologyMap (pullbackCompositionIso s U A).inv n ≫
        triangleHomologyMap h (U.comp s) (U.comp t) w' A n := by
  have he := congrArg (fun k ↦ (HomologicalComplex.homologyFunctor _ _ n).map
    ((AlgebraicTopology.alternatingFaceMapComplex _).map k))
      (triangleSimplicialMap_pullback h s t w U A w')
  simp only [Functor.map_comp, ← triangleHomologyMap_eq] at he
  exact he

end Quillen.LocalCoefficients

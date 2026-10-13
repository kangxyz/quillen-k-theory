/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.PointRelativeHomology
public import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # Positive point-relative homology and actual finite boundary tests -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients
open scoped Simplicial
universe u
namespace QuillenTest.PointRelativeHomology
variable {X : Type u} [TopologicalSpace X] (x : X) (V : ModuleCat.{u} ℤ)

/-- Degree one is included even though the point's zeroth homology need not vanish. -/
def degree_one_comparison : homology (constant X V) 1 ≅
    (relativeSingularChainComplex {x} (constant X V)).homology 1 :=
  pointRelativeHomologyIso x V 0

/-- The inverse recovers every genuine absolute class from its actual relative quotient image. -/
theorem quotient_round_trip (n : ℕ) (a : homology (constant X V) (n + 1)) :
    (pointRelativeHomologyIso x V n).inv
      (HomologicalComplex.homologyMap
        (cokernel.π (pushforwardChainMap (subspaceInclusion {x}) (constant X V)))
          (n + 1) a) = a := by
  change (pointRelativeHomologyIso x V n).inv ((pointRelativeHomologyIso x V n).hom a) = a
  exact ConcreteCategory.congr_hom (pointRelativeHomologyIso x V n).hom_inv_id a

/-- An actual degree-two relative cycle has a finite ambient three-chain witness. -/
theorem degree_two_finite_boundary
    (z : (relativeSingularChainComplex {x} (constant X V)).cycles 2)
    (hz : (relativeSingularChainComplex {x} (constant X V)).homologyπ 2 z = 0) :
    ∃ (s : Finset (SingularSimplex X ⦋3⦌)) (a : ∀ σ, simplexFiber (constant X V) σ),
      (relativeSingularChainComplex {x} (constant X V)).d 3 2
        ((cokernel.π (pushforwardChainMap (subspaceInclusion {x}) (constant X V))).f 3
          (∑ σ ∈ s, chainInclusion (constant X V) σ (a σ))) =
        (relativeSingularChainComplex {x} (constant X V)).iCycles 2 z :=
  relativeCycle_exists_finite_boundary {x} (constant X V) 2 z hz

end QuillenTest.PointRelativeHomology

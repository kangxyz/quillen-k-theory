/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.PointRelativeEvaluation
public import Quillen.Topology.HomotopyGroups.SphericalFaces

/-!
# A genuine spherical simplex gives a point-relative integral cycle

The generator is not declared an absolute cycle in unnormalized singular
chains. Instead every boundary face is a basepoint-constant simplex and dies
under the original point-relative quotient. The original coefficient is the
lifted integer one.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {z : X}

/-- The original point-relative quotient kills every basepoint-constant generator. -/
@[reassoc]
theorem chainInclusion_const_pointRelativeQuotient (z : X) (n : ℕ) :
    chainInclusion (constant X integralCoefficientModule.{u}) (ContinuousMap.const _ z) ≫
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficientModule.{u}))).f n = 0 := by
  let I := pushforwardChainMap (subspaceInclusion {z}) (constant X integralCoefficientModule.{u})
  let q := cokernel.π I
  let τ : SingularSimplex ({z} : Set X) ⦋n⦌ := ContinuousMap.const _ ⟨z, rfl⟩
  have hiq : I.f n ≫ q.f n = 0 := by
    exact congrArg (fun f ↦ f.f n) (cokernel.condition I)
  have hι : chainInclusion (constant X integralCoefficientModule.{u})
      (ContinuousMap.const _ z) =
      chainInclusion (constant ({z} : Set X) integralCoefficientModule.{u}) τ ≫ I.f n := by
    exact (chainInclusion_pushforwardModuleMap (subspaceInclusion {z})
      (constant X integralCoefficientModule.{u}) τ).symm
  rw [hι, Category.assoc, hiq, comp_zero]

/-- Every positive-dimensional spherical simplex has constant standard faces. -/
theorem spherical_restrictSimplex_eq_const {n : ℕ}
    (f₀ : SphericalSimplex X z (n + 1)) (i : Fin (n + 2)) :
    restrictSimplex f₀.val (SimplexCategory.δ i) = ContinuousMap.const _ z := by
  ext x
  change f₀ (x.map i.succAbove) = z
  exact f₀.boundary _ (simplexBoundaryFace n i x).property

/-- The actual spherical generator is killed by the relative differential. -/
theorem spherical_pointRelative_d_zero {n : ℕ}
    (f₀ : SphericalSimplex X z (n + 1)) :
    chainInclusion (constant X integralCoefficientModule.{u}) f₀.val ≫
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficientModule.{u}))).f (n + 1) ≫
      (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).d
        (n + 1) n = 0 := by
  let q := cokernel.π (pushforwardChainMap (subspaceInclusion {z})
    (constant X integralCoefficientModule.{u}))
  change chainInclusion _ f₀.val ≫ q.f (n + 1) ≫ _ = 0
  have hq : q.f (n + 1) ≫
      (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).d
        (n + 1) n =
      (singularChainComplex (constant X integralCoefficientModule.{u})).d (n + 1) n ≫
        q.f n := q.comm (n + 1) n
  rw [hq, ← Category.assoc, chainInclusion_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    integralRestrictionTransport]
  apply Finset.sum_eq_zero
  intro i _
  have hfacezero : chainInclusion (constant X integralCoefficientModule.{u})
      (restrictSimplex f₀.val (SimplexCategory.δ i)) ≫ q.f n = 0 :=
    (congrArg (fun ρ : SingularSimplex X ⦋n⦌ ↦
      chainInclusion (constant X integralCoefficientModule.{u}) ρ ≫ q.f n)
        (spherical_restrictSimplex_eq_const f₀ i)).trans
      (chainInclusion_const_pointRelativeQuotient z n)
  have hid : 𝟙 integralCoefficientModule.{u} ≫
      chainInclusion (constant X integralCoefficientModule.{u})
        (restrictSimplex f₀.val (SimplexCategory.δ i)) ≫ q.f n = 0 :=
    (Category.id_comp _).trans hfacezero
  exact (congrArg (fun f ↦ (-1 : ℤ) ^ i.val • f) hid).trans (smul_zero _)

/-- The original relative-chain representative, with coefficient exactly one. -/
def sphericalRelativeChain {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).X (n + 1) :=
  (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
    (constant X integralCoefficientModule.{u}))).f (n + 1)
      (chainInclusion (constant X integralCoefficientModule.{u}) f₀.val (ULift.up 1))

/-- The actual relative chain is a cycle, including when its absolute boundary is nonzero. -/
theorem sphericalRelativeChain_cycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).d
      (n + 1) n (sphericalRelativeChain f₀) = 0 :=
  ConcreteCategory.congr_hom (spherical_pointRelative_d_zero f₀) (ULift.up 1)

/-- The cycle equation in the exact short-complex indexing used by the cycle object. -/
theorem sphericalRelativeChain_sc_cycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    ((forget₂ (ModuleCat.{u} ℤ) Ab).map
      ((relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).sc
        (n + 1)).g) (sphericalRelativeChain f₀) = 0 := by
  change (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).d
    (n + 1) ((ComplexShape.down ℕ).next (n + 1)) (sphericalRelativeChain f₀) = 0
  rw [ChainComplex.next_nat_succ]
  exact sphericalRelativeChain_cycle f₀

/-- The spherical representative as an element of the genuine relative cycle object. -/
def sphericalRelativeCycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).cycles (n + 1) :=
  ((relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).sc
    (n + 1)).cyclesMk (sphericalRelativeChain f₀) (sphericalRelativeChain_sc_cycle f₀)

/-- Taking the underlying chain returns exactly the original quotient generator. -/
theorem iCycles_sphericalRelativeCycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).iCycles
      (n + 1) (sphericalRelativeCycle f₀) = sphericalRelativeChain f₀ :=
  ((relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).sc
    (n + 1)).i_cyclesMk (sphericalRelativeChain f₀) (sphericalRelativeChain_sc_cycle f₀)

end Quillen.LocalCoefficients

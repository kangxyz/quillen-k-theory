/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-!
# Local coefficients on a product with a geometric simplex

The affine contraction to a specified vertex identifies every local system on
`X × Δ[n]` with the pullback of its restriction to that vertex slice. Its component
is the actual radial-path transport, rather than an unspecified equivalence.
Choosing vertex zero gives the coefficient identification used by the original
first-vertex convention in simplicial replacement.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Convexity
open scoped unitInterval Simplicial

universe u

namespace Quillen.LocalCoefficients

variable (X : Type u) [TopologicalSpace X]

/-- The original projection from a product with the geometric `n`-simplex. -/
def simplexProductProjection (n : ℕ) : C(X × StdSimplex ℝ (Fin (n + 1)), X) :=
  ⟨Prod.fst, continuous_fst⟩

/-- The original inclusion of a prescribed vertex slice. -/
def simplexProductVertex (n : ℕ) (v : Fin (n + 1)) :
    C(X, X × StdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ (x, StdSimplex.single v), by fun_prop⟩

/-- The specified affine contraction starts at the vertex slice and ends at the identity. -/
def simplexProductVertexHomotopy (n : ℕ) (v : Fin (n + 1)) :
    ((simplexProductVertex X n v).comp (simplexProductProjection X n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := (z.2.1, convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (StdSimplex.single v) z.2.2)
  continuous_toFun := by
    apply Continuous.prodMk continuous_snd.fst
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
    unfold Function.comp
    refine continuous_pi fun i ↦ ?_
    simp only [unitInterval.coe_symm_eq, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left z := by simp [simplexProductVertex, simplexProductProjection]
  map_one_left z := by simp

/-- The product projection is a homotopy equivalence with the original vertex section. -/
def simplexProductProjectionEquiv (n : ℕ) (v : Fin (n + 1)) :
    ContinuousMap.HomotopyEquiv (X × StdSimplex ℝ (Fin (n + 1))) X where
  toFun := simplexProductProjection X n
  invFun := simplexProductVertex X n v
  left_inv := ⟨simplexProductVertexHomotopy X n v⟩
  right_inv := by
    have h : (simplexProductProjection X n).comp (simplexProductVertex X n v) =
        ContinuousMap.id X := rfl
    rw [h]

/-- Radial transport trivializes every local system in the simplex direction. -/
def simplexProductVertexCoefficients (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) :
    pullback (simplexProductProjection X n) (pullback (simplexProductVertex X n v) A) ≅ A :=
  (pullbackCompositionIso (simplexProductProjection X n) (simplexProductVertex X n v) A).symm ≪≫
    homotopyPullbackIso (simplexProductVertexHomotopy X n v) A ≪≫ pullbackIdentityIso A

/-- The coefficient identification is exactly transport along the specified radial path. -/
@[simp]
theorem simplexProductVertexCoefficients_hom_app (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1))))
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexCoefficients X n v A).hom.app (FundamentalGroupoid.mk z) =
      transport A ((simplexProductVertexHomotopy X n v).evalAt z) := by
  simp [simplexProductVertexCoefficients, pullbackCompositionIso, pullbackIdentityIso]

/-- The original projection induces an isomorphism for every target local system. -/
theorem simplexProductProjection_homology_isIso (n : ℕ) (A : System.{u, u} X) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductProjection X n) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n 0) A k

/-- The original vertex section induces an isomorphism for every local system on the product. -/
theorem simplexProductVertex_homology_isIso (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) (k : ℕ) :
    IsIso (pushforwardHomologyMap (simplexProductVertex X n v) A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (simplexProductProjectionEquiv X n v).symm A k

/-- The actual geometric simplex over a fixed point of the parameter space. -/
def simplexProductSlice (n : ℕ) (x : X) :
    SingularSimplex (X × StdSimplex ℝ (Fin (n + 1))) ⦋n⦌ :=
  ⟨fun t ↦ (x, t), by fun_prop⟩

/-- Radial trivialization agrees with the original simplex transport convention. -/
theorem simplexProductVertexCoefficients_hom_app_eq_simplexTransport
    (n : ℕ) (v : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1))))
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexCoefficients X n v A).hom.app (FundamentalGroupoid.mk z) =
      simplexTransport A (simplexProductSlice X n z.1) (StdSimplex.single v) z.2 := by
  rw [simplexProductVertexCoefficients_hom_app]
  exact (simplexTransport_eq_path A (simplexProductSlice X n z.1)
    (((simplexProductVertexHomotopy X n v).evalAt z).map continuous_snd)).symm

/-- The specified straight edge homotopy between two original vertex slices. -/
def simplexProductVertexChange (n : ℕ) (v w : Fin (n + 1)) :
    (simplexProductVertex X n v).Homotopy (simplexProductVertex X n w) :=
  ((simplexProductVertexHomotopy X n v).compContinuousMap
    (simplexProductVertex X n w)).cast rfl rfl

/-- Coefficient transport between two vertex restrictions uses that original edge. -/
def simplexProductVertexChangeCoefficients (n : ℕ) (v w : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) :
    pullback (simplexProductVertex X n v) A ≅ pullback (simplexProductVertex X n w) A :=
  homotopyPullbackIso (simplexProductVertexChange X n v w) A

/-- Vertex-change coefficients are exactly the existing simplex-edge transport. -/
@[simp]
theorem simplexProductVertexChangeCoefficients_hom_app (n : ℕ) (v w : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) (x : X) :
    (simplexProductVertexChangeCoefficients X n v w A).hom.app (FundamentalGroupoid.mk x) =
      simplexTransport A (simplexProductSlice X n x)
        (StdSimplex.single v) (StdSimplex.single w) := by
  change transport A ((simplexProductVertexChange X n v w).evalAt x) = _
  exact (simplexTransport_eq_path A (simplexProductSlice X n x)
    (((simplexProductVertexChange X n v w).evalAt x).map continuous_snd)).symm

/-- Changing the chosen vertex commutes with radial coefficient identification. -/
@[reassoc]
theorem simplexProductVertexCoefficients_change (n : ℕ) (v w : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1))))
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    (simplexProductVertexChangeCoefficients X n v w A).hom.app
        (FundamentalGroupoid.mk z.1) ≫
      (simplexProductVertexCoefficients X n w A).hom.app (FundamentalGroupoid.mk z) =
        (simplexProductVertexCoefficients X n v A).hom.app (FundamentalGroupoid.mk z) := by
  simp only [simplexProductVertexChangeCoefficients_hom_app,
    simplexProductVertexCoefficients_hom_app_eq_simplexTransport, simplexTransport_comp]

/-- The two original slice maps agree on homology after the actual edge transport. -/
theorem simplexProductVertex_homology_change (n : ℕ) (v w : Fin (n + 1))
    (A : System.{u, u} (X × StdSimplex ℝ (Fin (n + 1)))) (k : ℕ) :
    pushforwardHomologyMap (simplexProductVertex X n v) A k =
      coefficientHomologyMap (simplexProductVertexChangeCoefficients X n v w A).hom k ≫
        pushforwardHomologyMap (simplexProductVertex X n w) A k :=
  pushforwardHomologyMap_homotopy (simplexProductVertexChange X n v w) A k

end Quillen.LocalCoefficients

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.RegularChains
public import Quillen.Topology.Covering.SingularSimplices
public import Quillen.Topology.Covering.PathClasses

/-!
# Regular local-coefficient chains and a supplied simply connected cover

For an actual covering with simply connected total space, regular
local-coefficient chains of the base are isomorphic to ordinary integral
singular chains of the total space. The comparison sends a regular basis
path to the unique simplex lift beginning at its monodromy endpoint.
It commutes with every simplicial restriction, hence with all faces,
degeneracies, and differentials.

The chain models use one explicitly specified common universe and the
ordinary coefficient object is `ULift ℤ` in that universe. No universal
cover is constructed, and no Hurewicz or Whitehead recognition is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) [SimplyConnectedSpace E]

/-- Regular basis paths specify exactly the possible first vertices of a lifted simplex. -/
def coveringRegularSimplexEquiv (e₀ : E) (n : SimplexCategory) :
    RegularSimplex (p e₀) n ≃ SingularSimplex E n :=
  (Equiv.sigmaCongrRight fun σ : SingularSimplex B n ↦
    Covering.pathClassEquiv hp e₀ (σ (StdSimplex.single 0))).trans
      (Covering.simplexEquiv hp n).symm

/-- The comparison uses the actual simplex lift at the actual monodromy endpoint. -/
theorem coveringRegularSimplexEquiv_apply (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp e₀ n s =
      Covering.lift hp s.1 (hp.monodromy s.2 ⟨e₀, rfl⟩).1
        (hp.monodromy s.2 ⟨e₀, rfl⟩).2 := rfl

/-- Every simplicial restriction agrees with the transported regular basis restriction. -/
theorem coveringRegularSimplexEquiv_restrict (e₀ : E) {m n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) (α : m ⟶ n) :
    coveringRegularSimplexEquiv hp e₀ m (restrictRegularSimplex (p e₀) s α) =
      restrictSimplex (coveringRegularSimplexEquiv hp e₀ n s) α := by
  change (Covering.simplexEquiv hp m).symm
    ⟨_, Covering.pathClassEquiv hp e₀ _ _⟩ =
      restrictSimplex ((Covering.simplexEquiv hp n).symm
        ⟨_, Covering.pathClassEquiv hp e₀ _ _⟩) α
  rw [← Covering.lift_restrict]
  congr 1
  dsimp only [restrictRegularSimplex, Covering.restrict]
  rw [Covering.pathClassEquiv_trans]
  rfl

/-- Degreewise linear isomorphism of the existing coproduct chain modules. -/
def coveringModuleIso (e₀ : E) (n : SimplexCategory) :
    chainModule (regular (p e₀)) n ≅
      chainModule (constant E integralCoefficients) n :=
  regularBasisIso (p e₀) n ≪≫
    (Finsupp.mapDomain.linearEquiv ℤ ℤ
      (coveringRegularSimplexEquiv hp e₀ n)).toModuleIso ≪≫
    (integralBasisIso n).symm

/-- The degreewise comparison retains the integer and lifts the actual simplex. -/
@[simp]
theorem coveringModuleIso_generator (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) (z : ℤ) :
    (coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) s z) =
      integralChainGenerator (coveringRegularSimplexEquiv hp e₀ n s) z := by
  change integralBasisInv n
    (Finsupp.mapDomain (coveringRegularSimplexEquiv hp e₀ n)
      (regularBasisHom (p e₀) n (regularChainGenerator (p e₀) s z))) = _
  rw [regularBasisHom_generator, Finsupp.mapDomain_single, integralBasisInv_single]

/-- The linear isomorphisms commute with all faces and degeneracies, including face zero. -/
@[reassoc]
theorem coveringModuleIso_naturality (e₀ : E) {m n : SimplexCategory}
    (α : m ⟶ n) :
    chainMap (regular (p e₀)) α ≫ (coveringModuleIso hp e₀ m).hom =
      (coveringModuleIso hp e₀ n).hom ≫ chainMap (constant E integralCoefficients) α := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro q z
  change (coveringModuleIso hp e₀ m).hom
      (chainMap (regular (p e₀)) α (regularChainGenerator (p e₀) ⟨σ, q⟩ z)) =
    chainMap (constant E integralCoefficients) α
      ((coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) ⟨σ, q⟩ z))
  simp [coveringRegularSimplexEquiv_restrict]

/-- The actual simplicial-module isomorphism, with all restriction identities proved. -/
def coveringSimplicialIso (e₀ : E) :
    simplicialModule (regular (p e₀)) ≅
      simplicialModule (constant E integralCoefficients) :=
  NatIso.ofComponents (fun n ↦ coveringModuleIso hp e₀ n.unop)
    (by
      intro n m α
      exact coveringModuleIso_naturality hp e₀ α.unop)

/-- The genuine chain isomorphism before the standard ordinary-chain reindexing. -/
def coveringConstantChainIso (e₀ : E) :
    singularChainComplex (regular (p e₀)) ≅
      singularChainComplex (constant E integralCoefficients) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (coveringSimplicialIso hp e₀)

/-- Regular local coefficients recover mathlib's ordinary singular chains of this cover. -/
def coveringChainIso (e₀ : E) :
    singularChainComplex (regular (p e₀)) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).obj (TopCat.of E) :=
  coveringConstantChainIso hp e₀ ≪≫ constantChainComplexIso integralCoefficients

/-- The actual differential square commutes in every degree. -/
@[reassoc]
theorem coveringModuleIso_d (e₀ : E) (m n : ℕ) :
    (singularChainComplex (regular (p e₀))).d m n ≫
        (coveringModuleIso hp e₀ ⦋n⦌).hom =
      (coveringModuleIso hp e₀ ⦋m⦌).hom ≫
        (singularChainComplex (constant E integralCoefficients)).d m n :=
  ((coveringConstantChainIso hp e₀).hom.comm m n).symm

end Quillen.LocalCoefficients

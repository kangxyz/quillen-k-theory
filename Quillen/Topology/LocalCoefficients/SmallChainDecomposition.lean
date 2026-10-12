/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChainGluing

/-! # Exact decompositions of genuine small chains -/
@[expose] public section
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u v w
namespace Quillen.LocalCoefficients
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}

/-- If each simplex is small, the original small-chain inclusion is an isomorphism. -/
def allSmallChainIso (U : ι → Set X) (A : System.{u, u} X)
    (h : ∀ n, ∀ s : SingularSimplex X n, IsCoverSmall U s) :
    smallChainComplex U A ≅ singularChainComplex A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (NatIso.ofComponents (fun n => smallModuleIso U A n.unop (h n.unop))
      (fun f => smallChainMap_inclusion U A f.unop))

/-- This isomorphism uses the original summand inclusion. -/
theorem allSmallChainIso_hom (U : ι → Set X) (A : System.{u, u} X)
    (h : ∀ n, ∀ s : SingularSimplex X n, IsCoverSmall U s) :
    (allSmallChainIso U A h).hom = smallChainComplexInclusion U A := rfl

/-- A family admitting no small singular simplex has the actual zero chain complex. -/
theorem smallChainComplex_isZero_of_no_small (U : ι → Set X) (A : System.{u, u} X)
    (h : ∀ n, ∀ s : SingularSimplex X n, ¬IsCoverSmall U s) :
    IsZero (smallChainComplex U A) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sigma.hom_ext
  intro s
  exact False.elim (h _ s.val s.property)

/-- With no simplex in both families, gluing is an actual chain isomorphism. -/
theorem smallChainGluingSum_isIso_of_disjoint
    (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)
    (h : ∀ n, ∀ s : SingularSimplex X n, ¬(IsCoverSmall U s ∧ IsCoverSmall V s)) :
    IsIso (smallChainGluingSum U V A) := by
  have hz := smallChainComplex_isZero_of_no_small (intersectionCover U V) A
    (fun n s hs => h n s ((isCoverSmall_intersectionCover U V s).mp hs))
  have he := smallChainGluingSequence_shortExact U V A
  have : Mono (smallChainGluingSum U V A) :=
    he.exact.mono_g (hz.eq_of_src _ _)
  have : Epi (smallChainGluingSum U V A) := he.epi_g
  exact isIso_of_mono_of_epi _

end Quillen.LocalCoefficients

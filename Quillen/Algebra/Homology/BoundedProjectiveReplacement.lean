/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# Bounded-above projective replacements

Negating degrees and passing to the opposite category turns the actual
bounded-below injective replacement into a bounded-above projective replacement.
The upper bound is unchanged. Quasi-isomorphisms are transported through the
actual reindexing and opposite functors, rather than assumed preserved.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace Quillen.CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reversing integer degrees preserves actual quasi-isomorphisms. -/
instance quasiIso_restriction_neg_up {K L : ChainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (restrictionMap f ComplexShape.embeddingUpIntDownInt) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff' _ (n-1) n (n+1) (by simp) (by simp)]
    exact (quasiIsoAt_iff' f (-(n-1)) (-n) (-(n+1)) (by simp; omega)
      (by simp; omega)).mp inferInstance

/-- The inverse integer reindexing preserves actual quasi-isomorphisms. -/
instance quasiIso_restriction_neg_down {K L : CochainComplex C ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (restrictionMap f ComplexShape.embeddingDownIntUpInt) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff' _ (n+1) n (n-1) (by simp) (by simp)]
    exact (quasiIsoAt_iff' f (-(n+1)) (-n) (-(n-1)) (by simp; omega)
      (by simp; omega)).mp inferInstance

/-- The inverse opposite cochain equivalence preserves actual quasi-isomorphisms. -/
instance quasiIso_cochain_opEquivalence_inverse_map {K L : CochainComplex Cᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((CochainComplex.opEquivalence C).inverse.map f).unop) := by
  change QuasiIso ((HomologicalComplex.unopFunctor C (ComplexShape.down ℤ)).map
    (restrictionMap f ComplexShape.embeddingDownIntUpInt).op)
  infer_instance

/-- A bounded-above complex in an abelian category with enough projectives has
an actual bounded-above degreewise-projective quasi-isomorphic replacement. -/
theorem exists_boundedAbove_projective_replacement [EnoughProjectives C]
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex C ℤ) (p : P ⟶ K), QuasiIso p ∧
      (∀ n, Projective (P.X n)) ∧ P.IsStrictlyLE b := by
  let E := CochainComplex.opEquivalence C
  let KO := E.functor.obj (op K)
  have : KO.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (K.isZero_of_isStrictlyLE b (-n) (by omega)).op
  obtain ⟨L, i, hi, hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective KO (-b)
  let P := (E.inverse.obj L).unop
  let p : P ⟶ K := (E.inverse.map i).unop ≫ (E.unitIso.app (op K)).hom.unop
  refine ⟨P, p, ?_, ?_, ?_⟩
  · dsimp [p, E]
    infer_instance
  · intro n
    exact inferInstanceAs (Projective ((L.X (-n)).unop))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (L.isZero_of_isStrictlyGE (-b) (-n) (by omega)).unop

end Quillen.CochainComplex

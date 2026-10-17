/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.Algebra.Homology.CochainComplex.OppositeSubcategory
public import Aglib.Algebra.Homology.CochainComplex.OppositeQuasiIso

/-!
# Actual opposite-complex quasi-isomorphism comparisons

The original degree-reversing opposite-complex equivalence preserves and
reflects the quasi-isomorphism property, with the unchanged chain-map formulas.
-/
@[expose] public section

open Quillen.CochainComplex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ObjectProperty (CochainComplex C ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

lemma quasiIso_cochain_opEquivalence_functor_map {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((CochainComplex.opEquivalence C).functor.map f.op) := by
  change QuasiIso (restrictionMap ((HomologicalComplex.opFunctor C (.up ℤ)).map f.op)
    ComplexShape.embeddingUpIntDownInt)
  infer_instance

lemma quasiIso_cochain_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ}
    (f : K ⟶ L) : QuasiIso ((CochainComplex.opEquivalence C).functor.map f.op) ↔ QuasiIso f := by
  constructor
  · intro h
    let := h
    have := _root_.CochainComplex.quasiIso_cochain_opEquivalence_inverse_map
      ((CochainComplex.opEquivalence C).functor.map f.op)
    let e := CochainComplex.opEquivalence C
    have he : f = (e.unitIso.app (op K)).inv.unop ≫
        (e.inverse.map (e.functor.map f.op)).unop ≫ (e.unitIso.app (op L)).hom.unop := by
      apply Quiver.Hom.op_inj
      simp only [op_comp, Quiver.Hom.op_unop, Category.assoc]
      change f.op = e.unitIso.hom.app (op L) ≫
        (e.functor ⋙ e.inverse).map f.op ≫ e.unitIso.inv.app (op K)
      rw [← e.unitIso.hom.naturality_assoc]
      simp
    rw [he]
    infer_instance
  · intro h
    let := h
    exact quasiIso_cochain_opEquivalence_functor_map f

end Quillen.Waldhausen

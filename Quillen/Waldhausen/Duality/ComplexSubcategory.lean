/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Algebra.Homology.OppositeSubcategory
public import Quillen.Waldhausen.Duality.ExactCategory
public import Quillen.CategoryTheory.ExactCategory.Functor
public import Aglib.Algebra.Homology.CochainComplex.OppositeQuasiIso

/-!
# Genuine opposite Waldhausen structures on complex subcategories

Actual admissible epimorphisms become cofibrations on the literal opposite
full subcategory. Quasi-isomorphisms remain the original chain maps detected
by homology. Pullback gluing is proved by the exact original full inclusion,
the actual degree-reversing opposite equivalence, and genuine abelian complex
gluing. The resulting structure is compatible with the original zero-corner
kernel/cokernel squares.
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

/-- Genuine pullback gluing for the original quasi-isomorphisms and admissible epimorphisms. -/
theorem complexSubcategoryPullbackGluing : HasPullbackGluing
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex C ℤ)) P).deflation
    (complexSubcategory P).weq where
  gluing {A B D T A' B' D' T'} {i j f g i' j' f' g'} a b d p hf hf' h h' ei ej ef eg hb hd hp := by
    let I := ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex C ℤ)) P
    have hfA := I.map_deflation f hf
    have hfA' := I.map_deflation f' hf'
    have : Epi f.hom := (abelianExactStructure_deflation_iff _ _).mp hfA
    have : Epi f'.hom := (abelianExactStructure_deflation_iff _ _).mp hfA'
    have hA : IsPullback i.hom j.hom f.hom g.hom := (I.map_isPullback h.flip hf).flip
    have hA' : IsPullback i'.hom j'.hom f'.hom g'.hom := (I.map_isPullback h'.flip hf').flip
    let E := (CochainComplex.opEquivalence C).functor
    let : E.IsEquivalence := (CochainComplex.opEquivalence C).isEquivalence_functor
    have hb' : QuasiIso b.hom := hb
    have hd' : QuasiIso d.hom := hd
    have hp' : QuasiIso p.hom := hp
    have : QuasiIso (E.map b.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have : QuasiIso (E.map d.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have : QuasiIso (E.map p.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have ha := quasiIso_gluing (hA'.op.flip.map E) (hA.op.flip.map E)
      (E.map p.hom.op) (E.map b.hom.op) (E.map d.hom.op) (E.map a.hom.op)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ef.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) eg.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ei.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ej.symm)
    exact (quasiIso_cochain_opEquivalence_functor_map_iff a.hom).mp ha

/-- The original opposite complex subcategory has admissible epi cofibrations. -/
def oppositeComplexSubcategory : Structure P.FullSubcategoryᵒᵖ :=
  exactDualStructure
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex C ℤ)) P)
    (complexSubcategory P) (complexSubcategoryPullbackGluing P)

lemma oppositeComplexSubcategory_compatible :
    IsCompatibleDual (complexSubcategory P) (oppositeComplexSubcategory P) :=
  exactDualStructure_compatible _ _ _ rfl

end Quillen.Waldhausen

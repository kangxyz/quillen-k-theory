/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.WeakArrowFactorization
public import Mathlib.Data.ZMod.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Original affine roof and weak-arrow factorization consumers

These consumers check the actual derived maps and inverse formula, literal
comma and factorization equations, actual categorical kernel sequences,
and the non-domain and empty-spectrum cases.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.Affine



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.AffineWeakArrowFactorization

open Quillen
open PerfectComplexes PerfectComplexes.Affine
attribute [local instance] standardDerivedModules PerfectComplexes.Affine.standardDerivedSheaves

/-- Equal original derived maps acquire a genuine chain homotopy after a weak
post-denominator, without any K-projectivity assumption on either complex. -/
lemma original_derived_equality {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    ∃ (M : CochainComplex C ℤ) (s : L ⟶ M), IsIso (DerivedCategory.Q.map s) ∧
      Nonempty (Homotopy (f ≫ s) (g ≫ s)) := by
  obtain ⟨M, s, hs, H⟩ := Quillen.CochainComplex.exists_post_quasiIso_homotopy_of_derived_eq f g h
  exact ⟨M, s, inferInstance, H⟩

/-- The original sheaf-derived map from an actual strict complex is represented
by an actual map into another strict complex over a non-domain. -/
lemma non_domain_actual_map (P Q : StrictPerfect (Spec (.of (ZMod 6))))
    (α : (DerivedCategory.Q).obj P.obj ⟶ (DerivedCategory.Q).obj Q.obj) :
    ∃ f : P.obj ⟶ Q.obj, (DerivedCategory.Q).map f = α :=
  exists_strict_chain_representative _ P Q α

/-- The factorization supplies an original quasi-isomorphism cospan whose
right projection represents the exact original derived inverse formula. -/
lemma original_derived_fraction (R : CommRingCat.{u})
    (P : StrictPerfect (Spec R)) (B B' : CochainComplex (Spec R).Modules ℤ)
    (hB' : locallyPerfect (Spec R) B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (D : CochainComplex (Spec R).Modules ℤ) (v : B' ⟶ D) (d : D ⟶ B) (_ : QuasiIso v),
      inv ((DerivedCategory.Q).map v) ≫ (DerivedCategory.Q).map b = (DerivedCategory.Q).map d := by
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_strict_dual_factorization R P B B' hB' w b
  refine ⟨D, v, d, hv, ?_⟩
  rw [← he, Functor.map_comp, IsIso.inv_hom_id_assoc]

/-- Both actual component projections are ambient epimorphisms and their
literal kernel sequences are short exact. -/
lemma component_kernel_sequences (R : CommRingCat.{u})
    (P : StrictPerfect (Spec R)) (B B' : CochainComplex (Spec R).Modules ℤ)
    (hB' : locallyPerfect (Spec R) B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : StrictPerfect (Spec R)) (D : CochainComplex (Spec R).Modules ℤ)
      (c : C.obj ⟶ P.obj) (d : D ⟶ B),
      (ShortComplex.mk (kernel.ι c) c (kernel.condition c)).ShortExact ∧
      (ShortComplex.mk (kernel.ι d) d (kernel.condition d)).ShortExact ∧
      strictPerfect (Spec R) (kernel c) ∧ locallyPerfect (Spec R) (kernel d) := by
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_strict_dual_factorization R P B B' hB' w b
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  refine ⟨C, D, c, d, ?_, ?_, hkc, hkd⟩
  · exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel c)
            mono_f := inferInstance
            epi_g := inferInstance }
  · exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel d)
            mono_f := inferInstance
            epi_g := inferInstance }

/-- In the actual comma category the weak-arrow square commutes literally,
as does the requested target factorization. -/
lemma original_comma_square (R : CommRingCat.{u})
    (X : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R)))
    (B' : Perfect (Spec R)) (b : B' ⟶ X.obj.right) :
    ∃ (Y : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec R)) (strictToPerfect (Spec R)))
      (f : Y ⟶ X) (v : B' ⟶ Y.obj.right),
      QuasiIso v.hom ∧ v.hom ≫ f.hom.right.hom = b.hom ∧
      f.hom.left.hom ≫ X.obj.hom.hom = Y.obj.hom.hom ≫ f.hom.right.hom := by
  obtain ⟨Y, f, v, hv, he, hc, hd, hkc, hkd⟩ := weakArrow_target_dual_factorization R X B' b
  exact ⟨Y, f, v, hv, congrArg (fun z => z.hom) he,
    congrArg (fun z => z.hom) f.hom.w⟩

/-- The complete original weak-arrow factorization also covers empty Spec of
the zero ring, without any nonempty-space or nontrivial-ring assumption. -/
lemma empty_spec_factorization
    (X : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec (.of (ZMod 1))))
      (strictToPerfect (Spec (.of (ZMod 1)))))
    (B' : Perfect (Spec (.of (ZMod 1)))) (b : B' ⟶ X.obj.right) :
    ∃ (Y : Waldhausen.WeakArrow.Obj (perfectWaldhausen (Spec (.of (ZMod 1))))
      (strictToPerfect (Spec (.of (ZMod 1))))) (f : Y ⟶ X) (v : B' ⟶ Y.obj.right),
      QuasiIso v.hom ∧ v.hom ≫ f.hom.right.hom = b.hom := by
  obtain ⟨Y, f, v, hv, he, hsq⟩ := original_comma_square _ X B' b
  exact ⟨Y, f, v, hv, he⟩

end QuillenTest.AffineWeakArrowFactorization

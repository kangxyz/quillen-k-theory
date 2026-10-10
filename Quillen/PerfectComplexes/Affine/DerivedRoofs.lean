/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Affine.PerfectDerivedEquivalence
import Quillen.Algebra.Homology.DerivedEqualityDenominators

/-!
# Genuine affine derived roofs with original chain maps

Over every commutative ring, each original derived morphism between strict
perfect sheaf complexes has an actual chain representative. This uses the
original affine comparison and module K-projectivity, without asserting
ambient sheaf K-projectivity. An arbitrary locally-perfect sheaf complex
has a genuine weak cospan with a strict complex. These constructions yield
a common actual homotopy-commuting roof for the dual approximation argument
of Thomason–Trobaugh, Theorem 1.9.8.

All targets may have arbitrary module-sheaf terms. The weak cospan has both
arrows into its replacement; no direct strict-to-target quasi-isomorphism
is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma exists_strict_chain_representative (R : CommRingCat.{u})
    (P Q : StrictPerfect (Spec R))
    (α : (toDerived (Spec R)).obj P.obj ⟶ (toDerived (Spec R)).obj Q.obj) :
    ∃ f : P.obj ⟶ Q.obj, (toDerived (Spec R)).map f = α := by
  let P' := (sectionsComplex R).obj P.obj
  let Q' := (sectionsComplex R).obj Q.obj
  have hP' : moduleStrictPerfect R P' := moduleStrictPerfect_sections R P.property
  have hQ' : moduleStrictPerfect R Q' := moduleStrictPerfect_sections R Q.property
  let A : PerfectModuleDerived R := ⟨DerivedCategory.Q.obj P', ⟨P', hP', ⟨Iso.refl _⟩⟩⟩
  let B : PerfectModuleDerived R := ⟨DerivedCategory.Q.obj Q', ⟨Q', hQ', ⟨Iso.refl _⟩⟩⟩
  let eP := associatedSectionsIso R P.property
  let eQ := associatedSectionsIso R Q.property
  let e := associatedDerivedFactors R
  let β : (associatedPerfectDerived R).obj A ⟶ (associatedPerfectDerived R).obj B :=
    e.hom.app P' ≫ (toDerived _).map eP.hom ≫ α ≫ (toDerived _).map eQ.inv ≫ e.inv.app Q'
  obtain ⟨g, hg⟩ := (associatedPerfectDerived R).map_surjective β
  have : P'.IsKProjective := isKProjective_of_moduleStrictPerfect R hP'
  obtain ⟨f, hf⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective
    (C := ModuleCat.{u} R) (K := P') (L := Q') g.hom
  refine ⟨eP.inv ≫ (associatedComplex R).map f ≫ eQ.hom, ?_⟩
  have hfg : (associatedDerived R).map (DerivedCategory.Q.map f) = β := by
    rw [hf]
    exact hg
  have hn := (NatIso.naturality_1 e f).symm
  change (toDerived _).map ((associatedComplex R).map f) =
    e.inv.app P' ≫ (associatedDerived R).map (DerivedCategory.Q.map f) ≫ e.hom.app Q' at hn
  simp only [Functor.map_comp, hn, hfg]
  dsimp [β]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(toDerived (Spec R)).map_id, Category.comp_id, ← Functor.map_comp_assoc,
    eP.inv_hom_id, (toDerived (Spec R)).map_id, Category.id_comp]

lemma exists_strict_weak_cospan (R : CommRingCat.{u})
    (K : Complex (Spec R)) (hK : locallyPerfect (Spec R) K) :
    ∃ (P : StrictPerfect (Spec R)) (M : Complex (Spec R))
      (p : P.obj ⟶ M) (s : K ⟶ M),
      locallyPerfect (Spec R) M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, ⟨e⟩⟩ := locallyPerfect_exists_strictPerfect_representative R hK
  obtain ⟨M, p, s, hs, he⟩ := toDerived_left_fraction e.hom
  have hp : IsIso ((toDerived (Spec R)).map p) := by rw [← he]; infer_instance
  exact ⟨P, M, p, s, (locallyPerfect_iff_of_quasiIso s).mp hK,
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Spec R).Modules p).mp hp, hs⟩


/-- The genuine homotopy-commuting roof input for affine dual approximation.
All objects, weak arrows and homotopies live in the original chain category. -/
lemma exists_strict_homotopy_roof (R : CommRingCat.{u})
    (P : StrictPerfect (Spec R)) (B B' : Complex (Spec R))
    (hB' : locallyPerfect (Spec R) B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (A : StrictPerfect (Spec R)) (M N : Complex (Spec R))
      (a : A.obj ⟶ P.obj) (p : A.obj ⟶ M) (t : B' ⟶ M) (s : B ⟶ N) (q : M ⟶ N),
      locallyPerfect (Spec R) M ∧ locallyPerfect (Spec R) N ∧
      QuasiIso p ∧ QuasiIso t ∧ QuasiIso s ∧
      Nonempty (Homotopy (p ≫ q) (a ≫ w ≫ s)) ∧
      Nonempty (Homotopy (t ≫ q) (b ≫ s)) := by
  obtain ⟨A, M, p, t, hM, hp, ht⟩ := exists_strict_weak_cospan R B' hB'
  let D := toDerived (Spec R)
  let β : D.obj M ⟶ D.obj B := inv (D.map t) ≫ D.map b
  let α : D.obj A.obj ⟶ D.obj P.obj := D.map p ≫ β ≫ inv (D.map w)
  obtain ⟨a, ha⟩ := exists_strict_chain_representative R A P α
  obtain ⟨N, q, s, hs, he⟩ := toDerived_left_fraction β
  change D.map a = α at ha
  change β ≫ D.map s = D.map q at he
  have hB : locallyPerfect (Spec R) B :=
    (locallyPerfect_iff_of_quasiIso w).mp (locallyPerfect_of_strictPerfect P.property)
  have hN : locallyPerfect (Spec R) N := (locallyPerfect_iff_of_quasiIso s).mp hB
  have heq₁ : D.map (p ≫ q) = D.map (a ≫ w ≫ s) := by
    rw [Functor.map_comp, ← he]
    simp only [Functor.map_comp, ha, α, Category.assoc, IsIso.inv_hom_id_assoc]
  have heq₂ : D.map (t ≫ q) = D.map (b ≫ s) := by
    rw [Functor.map_comp, ← he]
    simp [β]
  obtain ⟨N', u, hu, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    Quillen.CochainComplex.exists_post_quasiIso_two_homotopies_of_derived_eq
      (C := (Spec R).Modules) (p ≫ q) (a ≫ w ≫ s) (t ≫ q) (b ≫ s) heq₁ heq₂
  refine ⟨A, M, N', a, p, t, s ≫ u, q ≫ u, hM,
    (locallyPerfect_iff_of_quasiIso u).mp hN, hp, ht, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · simpa only [Category.assoc] using H₁
  · simpa only [Category.assoc] using H₂

end Quillen.PerfectComplexes.Affine

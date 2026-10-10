/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Scheme.Sheaf.AffineCohomology
import Tests.AffineCechHigher

/-!
# Consumers of actual higher affine quasicoherent cohomology

The tests retain the original right-derived global-section functor, arbitrary
actual injective resolutions, and their successive kernels. They cover arbitrary
rings, the zero-divisor ring `ZMod 6`, proper principal opens, an empty principal
cover, and the zero ring. Further consumers retain the literal cocycle equation,
actual open-free stalk naturality, and arbitrary injective coefficients on
families of opens with no top-cover hypothesis.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum Quillen.SchemeSheaf Quillen.SchemeSheaf.AffineCech
open Quillen.SchemeSheaf.AffineDerived Quillen.Tests.AffineCechSections

namespace Quillen.Tests.AffineCohomology

lemma arbitrary_ring_original_higher_derived {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) :=
  isZero_rightDerived_globalSections_succ M n

lemma torsion_ring_original_resolution_exact_four
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt 4 :=
  globalSections_injectiveResolution_exact_succ M I 3

lemma zero_ring_original_higher_derived
    (M : (Spec AffineCechHigher.zeroRing).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) :=
  isZero_rightDerived_globalSections_succ M n

lemma torsion_proper_principal_cover_exact
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (principalCechComplex M (![2, 0] : Fin 2 → torsionRing)).ExactAt (n + 1) := by
  apply principalCech_exactAt_succ_on_basicOpen M 2
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact le_rfl
    · change basicOpen (0 : torsionRing) ≤ basicOpen 2
      rw [basicOpen_zero]
      exact bot_le
  · exact le_iSup (fun i => basicOpen ((![2, 0] : Fin 2 → torsionRing) i)) 0

lemma empty_principal_cover_exact {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (principalCechComplex M (fun i : ULift.{u} (Fin 0) => Fin.elim0 i.down)).ExactAt (n + 1) := by
  apply principalCech_exactAt_succ_on_basicOpen M 0
  simp

lemma original_resolution_kernel_principal_exact {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) (m n : ℕ)
    (r : R) {ι : Type u} [Fintype ι] (f : ι → R)
    (hf : (⨆ i, basicOpen (f i)) = basicOpen r) :
    (principalCechComplex (kernel (I.cocomplex.d (m + 1) (m + 2))) f).ExactAt (n + 1) :=
  injectiveResolution_kernel_principalCech_exact_succ M
    (fun r _ _ f hf n => principalCech_exactAt_succ_on_basicOpen M r f hf n) I m r ι f hf n

lemma injective_original_cech_arbitrary_family (X : Scheme.{u})
    (M : X.Modules) [Injective M] {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    ((cechComplexFunctor U).obj M.presheaf).ExactAt (n + 1) :=
  injectiveCech_exact_succ X M U n

lemma original_open_free_stalk_naturality (X : Scheme.{u}) (x : X)
    {U V : X.Opens} (h : U ⟶ V) :
    (moduleStalk X x).map ((openFreeFunctor X).map h) ≫ (openFreeStalkIso X x V).hom =
      (openFreeStalkIso X x U).hom ≫ (pointOpenFreeFunctor X x).map h :=
  openFreeStalkIso_naturality X x h

lemma original_cocycle_on_principal_open {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (r : R)
    {ι : Type u} [Fintype ι] (f : ι → R)
    (hf : (⨆ i, basicOpen (f i)) = basicOpen r)
    (c : ∀ i j, Section M (basicOpen (f i) ⊓ basicOpen (f j)))
    (hc : ∀ i j k,
      res M (inf_le_left : (basicOpen (f i) ⊓ basicOpen (f j)) ⊓ basicOpen (f k) ≤ _)
        (c i j) + res M (inf_le_inf inf_le_right le_rfl) (c j k) =
      res M (inf_le_inf inf_le_left le_rfl) (c i k)) :
    ∃ b : ∀ i, Section M (basicOpen (f i)), ∀ i j,
      res M inf_le_right (b j) - res M inf_le_left (b i) = c i j :=
  Quillen.Cech.exists_cechOne_coboundary_of_exact
    (X := TopCat.of (Spec R)) (R := R)
    (fun i => (basicOpen (f i) : (Spec R).Opens)) (modulesSpecToSheaf.obj M).obj
    (principalCech_exactAt_succ_on_basicOpen M r f hf 0) c hc

end Quillen.Tests.AffineCohomology

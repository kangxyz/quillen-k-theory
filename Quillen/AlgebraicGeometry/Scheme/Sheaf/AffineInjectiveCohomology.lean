/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineCohomology
public import Quillen.Algebra.Homology.OpcycleBoundary


/-!
# Actual affine global sections of lower-bounded injective complexes

Positive principal-cover Cech acyclicity propagates through the actual
homology/opcycle/boundary short exact sequences, starting below a genuine
lower term bound. Quasicoherent homology and injective terms supply the two
acyclic inputs at each step. Original section lifting then proves that
actual global sections preserve each differential cokernel and the original
right homology data. Neither the opcycles nor the injective terms are assumed
quasicoherent. No global exactness of sections on all sheaves is claimed.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum Quillen.Cech HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules.AffineCech

/-- Actual positive Čech exactness on every finite principal cover of a principal open. -/
def principalCechAcyclic {R : CommRingCat.{u}} (M : (Spec R).Modules) : Prop :=
  ∀ (r : R) (ι : Type u) [Fintype ι] (f : ι → R),
    (⨆ i, basicOpen (f i)) = basicOpen r →
      ∀ n : ℕ, (principalCechComplex M f).ExactAt (n + 1)

lemma principalCechAcyclic_of_quasicoherent {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] : principalCechAcyclic M :=
  fun r _ _ f hf n => principalCech_exactAt_succ_on_basicOpen M r f hf n

lemma principalCechAcyclic_of_injective {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [Injective M] : principalCechAcyclic M :=
  fun _ _ _ f _ n => affine_injectiveCech_exact_succ M (fun i => basicOpen (f i)) n

lemma principalCechAcyclic_of_isZero {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (hM : IsZero M) : principalCechAcyclic M := by
  intro r ι _ f hf n
  let F := affineSectionPresheafFunctor R ⋙
    cechComplexFunctor (fun i => (basicOpen (f i) : (Spec R).Opens))
  have hF : IsZero ((principalCechComplex M f).X (n + 1)) :=
    (HomologicalComplex.eval _ _ (n + 1)).map_isZero (F.map_isZero hM)
  exact ShortComplex.exact_of_isZero_X₂ _ hF

/-- Actual principal-cover acyclicity gives global-section exactness for an arbitrary quotient. -/
lemma shortExact_globalSections_of_principalCechAcyclic {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (hA : principalCechAcyclic S.X₁) : (S.map moduleSpecΓFunctor).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  have hs := sections_surjective_of_principalCech_exact_one hS ⊤ isCompact_univ
    (fun ι _ f hf => hA 1 ι f (by simpa only [basicOpen_one] using hf) 0)
  exact shortExact_sections_of_surjective hS ⊤ hs

/-- Quotients of two genuinely Čech-acyclic terms remain Čech-acyclic. -/
lemma principalCechAcyclic_quotient {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (hA : principalCechAcyclic S.X₁) (hB : principalCechAcyclic S.X₂) :
    principalCechAcyclic S.X₃ := by
  intro r ι _ f hf n
  have hT := principalCech_shortExact_of_kernel_cechOne hS
    (fun r ι _ f hf => hA r ι f hf 0) f
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) (n + 2) rfl).isZero_of_both_isZero
    (hB r ι f hf n).isZero_homology (hA r ι f hf (n + 1)).isZero_homology

/-- Extensions preserve actual positive principal-cover Čech exactness. -/
lemma principalCechAcyclic_extension {R : CommRingCat.{u}}
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (hA : principalCechAcyclic S.X₁) (hC : principalCechAcyclic S.X₃) :
    principalCechAcyclic S.X₂ := by
  intro r ι _ f hf n
  have hT := principalCech_shortExact_of_kernel_cechOne hS
    (fun r ι _ f hf => hA r ι f hf 0) f
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₂ (n + 1)).isZero_of_both_isZero
    (hA r ι f hf n).isZero_homology (hC r ι f hf n).isZero_homology

open Quillen.CochainComplex

/-- Ascending from the actual lower term bound proves Čech acyclicity of unrestricted opcycles. -/
lemma principalCechAcyclic_opcycles {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    principalCechAcyclic (I.opcycles n) := by
  have below (n : ℤ) (hn : n < a) : principalCechAcyclic (I.opcycles n) :=
    principalCechAcyclic_of_isZero _ ((hbound n hn).of_epi (I.pOpcycles n))
  by_cases hn : n < a
  · exact below n hn
  · have hn' : a - 1 ≤ n := by omega
    clear hn
    induction n, hn' using Int.leInduction with
    | base => exact below (a - 1) (by omega)
    | succ n hn ih =>
      let := hqc n
      let := hinj (n + 1)
      have hB : principalCechAcyclic (boundaryAfter I n) :=
        principalCechAcyclic_quotient (R := R) (S := opcycleBoundarySequence I n)
          (opcycleBoundarySequence_shortExact I n)
          (principalCechAcyclic_of_quasicoherent (I.homology n)) ih
      exact principalCechAcyclic_quotient (R := R) (S := boundaryOpcycleSequence I n)
        (boundaryOpcycleSequence_shortExact I n) hB
        (principalCechAcyclic_of_injective (I.X (n + 1)))

/-- Every actual boundary appearing in the lower-bounded injective complex is Čech-acyclic. -/
lemma principalCechAcyclic_boundaryAfter {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    principalCechAcyclic (boundaryAfter I n) := by
  let := hqc n
  exact principalCechAcyclic_quotient (R := R) (S := opcycleBoundarySequence I n)
    (opcycleBoundarySequence_shortExact I n)
    (principalCechAcyclic_of_quasicoherent (I.homology n))
    (principalCechAcyclic_opcycles I a hbound hinj hqc n)

/-- Global sections preserve the actual next-boundary/term/opcycle short exact sequence. -/
lemma globalSections_boundaryOpcycle_shortExact {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    ((boundaryOpcycleSequence I n).map moduleSpecΓFunctor).ShortExact :=
  shortExact_globalSections_of_principalCechAcyclic (boundaryOpcycleSequence_shortExact I n)
    (principalCechAcyclic_boundaryAfter I a hbound hinj hqc n)

/-- The literal projection from each injective term onto its opcycles is epic on global sections. -/
lemma epi_globalSections_pOpcycles {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    Epi (moduleSpecΓFunctor.map (I.pOpcycles n)) := by
  have H := (globalSections_boundaryOpcycle_shortExact I a hbound hinj hqc (n - 1)).epi_g
  change Epi (moduleSpecΓFunctor.map (I.pOpcycles (n - 1 + 1))) at H
  have he : n - 1 + 1 = n := by omega
  rw [he] at H
  exact H

/-- The actual global-section cokernel is preserved at each differential of the injective complex.
-/
lemma globalSections_preserves_opcycles {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    PreservesColimit (parallelPair (I.d n (n + 1)) 0) moduleSpecΓFunctor := by
  let F := moduleSpecΓFunctor (R := R)
  let : (opcycleBoundarySequence I n).X₁.IsQuasicoherent := hqc n
  have hS₁ := shortExact_globalSections_of_quasicoherent_kernel
    (opcycleBoundarySequence_shortExact I n)
  have hS₂ := globalSections_boundaryOpcycle_shortExact I a hbound hinj hqc n
  let := hS₂.epi_g
  let : Epi (F.map (I.pOpcycles n)) := epi_globalSections_pOpcycles I a hbound hinj hqc n
  let : Epi (F.map (cokernel.π (I.homologyι n))) := hS₁.epi_g
  let : Epi (F.map (I.pOpcycles (n + 1))) := hS₂.epi_g
  let p := F.map (I.pOpcycles n) ≫ F.map (cokernel.π (I.homologyι n))
  have hp : Epi p := inferInstance
  have hd : F.map (I.d n (n + 1)) = p ≫ F.map (boundaryAfterι I n) := by
    dsimp [p]
    rw [Category.assoc, ← F.map_comp, boundaryAfter_π_ι, ← F.map_comp, I.p_fromOpcycles]
  have hc : IsColimit (CokernelCofork.ofπ (F.map (I.pOpcycles (n + 1)))
      (show F.map (boundaryAfterι I n) ≫ F.map (I.pOpcycles (n + 1)) = 0 from
        ((boundaryOpcycleSequence I n).map F).zero)) := hS₂.exact.gIsCokernel
  apply preservesColimit_of_preserves_colimit_cocone (I.opcyclesIsCokernel n (n + 1) (by simp))
  apply (isColimitMapCoconeCoforkEquiv' F (I.d_pOpcycles n (n + 1))).symm.toFun
  exact isCokernelEpiComp hc p hd

/-- Global sections preserve the original right homology data degree by degree. -/
lemma globalSections_preservesRightHomology {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    moduleSpecΓFunctor.PreservesRightHomologyOf (I.sc n) := by
  have hp : PreservesColimit (parallelPair (I.sc n).f 0) moduleSpecΓFunctor := by
    have H := globalSections_preserves_opcycles I a hbound hinj hqc (n - 1)
    have he : n - 1 + 1 = n := by omega
    rw [he] at H
    change PreservesColimit (parallelPair (I.d ((ComplexShape.up ℤ).prev n) n) 0) _
    rw [_root_.CochainComplex.prev]
    exact H
  let : (I.sc n).homologyData.right.IsPreservedBy moduleSpecΓFunctor :=
    { f := hp, g' := inferInstance }
  exact Functor.PreservesRightHomologyOf.mk' moduleSpecΓFunctor (I.sc n).homologyData.right

end AlgebraicGeometry.Scheme.Modules.AffineCech

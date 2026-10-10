/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles
import Quillen.Algebra.ModuleComplex.PrincipalDenominators
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Highest homology of finite-projective complexes

Splitting the actual upper cycle sequences proves finite projectivity of all
cycles at and above a cohomological upper bound of a bounded-above complex
of finite projectives. Its highest homology is therefore finite. Exact
localization and genuine principal-local derived models descend this
finiteness to an arbitrary original module complex. Rings are arbitrary;
no finite generation of lower homology over a noncoherent ring is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace Quillen.ModuleComplex
open Quillen.Waldhausen.GilletWaldhausen
variable {R : Type u} [CommRing R]

/-- Actual upper cycle sequences split, making every cycle at or above the cohomological bound finite projective. -/
lemma finite_projective_cycles_above_cohomology_bound
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n b : ℤ) [K.IsLE n]
    (hbound : ∀ i, b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite R (K.X i))
    (hprojective : ∀ i, Projective (K.X i)) (i : ℤ) (hi : n ≤ i) :
    Module.Finite R (K.cycles i) ∧ Projective (K.cycles i) := by
  have top (j : ℤ) (hj : b ≤ j) :
      Module.Finite R (K.cycles j) ∧ Projective (K.cycles j) := by
    let e := K.iCyclesIso j (j+1) (by simp) ((hbound (j+1) (by omega)).eq_of_tgt _ _)
    let := hfinite j
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, Projective.of_iso e.symm (hprojective j)⟩
  by_cases hib : i ≤ b
  · induction i, hib using Int.leInductionDown with
    | base => exact top b le_rfl
    | pred j hj ih =>
      have hp : Projective (K.cycles j) := (ih (by omega)).2
      have hS := cycleSequence_shortExact K (j-1) (by simpa using K.exactAt_of_isLE n j (by omega))
      have : Projective (cycleSequence K (j-1)).X₃ := by
        change Projective (K.cycles (j-1+1))
        simpa using hp
      let s := hS.splittingOfProjective
      let e : Retract (K.cycles (j-1)) (K.X (j-1)) :=
        ⟨K.iCycles (j-1), s.r, s.f_r⟩
      have : Epi e.r := epi_of_epi_fac e.retract
      let := hfinite (j-1)
      let := hprojective (j-1)
      exact ⟨Module.Finite.of_surjective e.r.hom ((ModuleCat.epi_iff_surjective e.r).mp inferInstance),
        e.projective⟩
  · exact top i (by omega)

/-- Highest homology is the actual quotient of a finite projective cycle module. -/
lemma finite_top_homology_of_boundedAbove_finite_projective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n b : ℤ) [K.IsLE n]
    (hbound : ∀ i, b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite R (K.X i))
    (hprojective : ∀ i, Projective (K.X i)) : Module.Finite R (K.homology n) := by
  let := (finite_projective_cycles_above_cohomology_bound K n b hbound hfinite hprojective n le_rfl).1
  exact Module.Finite.of_surjective (K.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance)

end Quillen.ModuleComplex

namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

local instance standardDerived (S : Type u) [Ring S] : HasDerivedCategory.{u+1} (ModuleCat.{u} S) :=
  HasDerivedCategory.standard _

/-- Genuine principal-local finite-projective derived models make original highest homology finite globally. -/
lemma finite_top_homology_of_principal_perfect_models
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsLE n]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hlocal : ∀ r : s,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ) (b : ℤ),
        (∀ i, b < i → IsZero (P.X i)) ∧
        (∀ i, Module.Finite (Localization.Away r.val) (P.X i)) ∧
        (∀ i, Projective (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj
          ((PrincipalLocalization.localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    Module.Finite R (K.homology n) := by
  apply Module.Finite.of_localizationSpan_finite' s hs
    (Rₚ := fun r => Localization.Away r.val)
    (Mₚ := fun r => (K.homology n).localizedModule (Submonoid.powers r.val))
    (fun r => (K.homology n).localizedModuleMkLinearMap (Submonoid.powers r.val))
  intro r
  obtain ⟨P, b, hb, hfinite, hprojective, ⟨e⟩⟩ := hlocal r
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  let L : CochainComplex (ModuleCat.{u} (Localization.Away r.val)) ℤ :=
    (PrincipalLocalization.localize r.val (.up ℤ)).obj K
  have : L.IsLE n := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (K.exactAt_of_isLE n i hi).map F
  have : P.IsLE n := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso e n
  let eH : L.homology n ≅ P.homology n :=
    ((DerivedCategory.homologyFunctorFactors _ n).app L).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app P
  let eF : L.homology n ≅ F.obj (K.homology n) := (K.sc n).mapHomologyIso F
  have := finite_top_homology_of_boundedAbove_finite_projective P n b hb hfinite hprojective
  exact Module.Finite.equiv (eF.symm ≪≫ eH).toLinearEquiv.symm

end Quillen.ModuleComplex

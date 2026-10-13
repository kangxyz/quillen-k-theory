/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.ModuleComplex.PrincipalDescent
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.Int.Interval

/-!
# Bounded finite-free complex descent across a principal localization

Actual localized bases give finite-free original-ring models of every target
term, preserving zero terms. The proved differential descent constructs a
bounded finite-free complex with precisely the original lower and upper term
bounds, and an actual chain isomorphism after scalar localization. The ring
is arbitrary, including zero-ring localizations. Projective stabilization is
not asserted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Every actual finite-free module over a principal localization has an actual
finite-free module model over the original ring, preserving zero objects. -/
theorem exists_finiteFree_localized_model (r : R)
    (N : ModuleCat.{u} (Localization (Submonoid.powers r)))
    [Module.Free (Localization (Submonoid.powers r)) N]
    [Module.Finite (Localization (Submonoid.powers r)) N] :
    ∃ M : ModuleCat.{u} R, Module.Free R M ∧ Module.Finite R M ∧
      (IsZero N → IsZero M) ∧ Nonempty
        (M.localizedModule (Submonoid.powers r) ≅ N) := by
  classical
  by_cases hN : IsZero N
  · let M := ModuleCat.of R (Fin 0 →₀ R)
    have hM : IsZero M := ModuleCat.isZero_of_subsingleton M
    refine ⟨M, inferInstance, inferInstance, fun _ => hM, ⟨?_⟩⟩
    exact ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map_isZero hM).iso hN
  · let S := Localization (Submonoid.powers r)
    let I := Module.Free.ChooseBasisIndex S N
    let M := ModuleCat.of R (I →₀ R)
    let bR : Module.Basis I R M := Finsupp.basisSingleOne
    let := ModuleCat.localizedModule_isLocalizedModule M (Submonoid.powers r)
    let b : Module.Basis I S (M.localizedModule (Submonoid.powers r)) :=
      bR.ofIsLocalizedModule
        S (Submonoid.powers r) (M.localizedModuleMkLinearMap (Submonoid.powers r))
    refine ⟨M, inferInstance, inferInstance, fun h => (hN h).elim, ⟨?_⟩⟩
    exact (b.repr.trans (Module.Free.chooseBasis S N).repr.symm).toModuleIso

/-- A genuinely bounded finite-free complex over R[r⁻¹] descends to a bounded
finite-free complex over R with the same term bounds and an actual chain isomorphism
after scalar localization. Neither noetherianity nor nontriviality is assumed. -/
theorem exists_bounded_finiteFree_complex_descent (r : R)
    (K : CochainComplex (ModuleCat.{u} (Localization (Submonoid.powers r))) ℤ)
    (a b : ℤ) (hbound : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hfree : ∀ i, Module.Free (Localization (Submonoid.powers r)) (K.X i))
    (hfinite : ∀ i, Module.Finite (Localization (Submonoid.powers r)) (K.X i)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, i < a ∨ b < i → IsZero (P.X i)) ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty ((localize r (.up ℤ)).obj P ≅ K) := by
  classical
  have hm (i : ℤ) : ∃ M : ModuleCat.{u} R, Module.Free R M ∧ Module.Finite R M ∧
      (IsZero (K.X i) → IsZero M) ∧ Nonempty
        (M.localizedModule (Submonoid.powers r) ≅ K.X i) := by
    let := hfree i
    let := hfinite i
    exact exists_finiteFree_localized_model r (K.X i)
  choose M hMfree hMfinite hMzero hMe using hm
  have hfp (i : ℤ) : Module.FinitePresentation R (M i) := by
    let := hMfree i
    let := hMfinite i
    exact Module.finitePresentation_of_projective R (M i)
  have hz (i : ℤ) (hi : i ∉ Finset.Icc a b) : IsZero (M i) := by
    apply hMzero i
    apply hbound i
    simpa only [Finset.mem_Icc, not_and_or, not_le] using hi
  obtain ⟨δ, hδ, e⟩ := exists_complex_descent_with_terms r M (Finset.Icc a b) hz hfp K
    (fun i => (hMe i).some)
  exact ⟨CochainComplex.of M δ hδ, fun i hi => hMzero i (hbound i hi),
    fun i => ⟨hMfree i, hMfinite i⟩, e⟩

end Quillen.ModuleComplex.PrincipalLocalization

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.ModuleComplex.ProjectiveStabilization
public import Quillen.Algebra.ModuleComplex.PrincipalFreeDescent

/-!
# Principal-open descent after projective stabilization

The actual finite-free stabilization and differential denominator descent
extend every bounded finite-projective localized complex after adjoining its
shift. The comparison is an actual chain-homotopy equivalence, with explicit
original-ring bounds. This is extension up to a shifted summand and does not
assert extension of the original complex or remove the K₀ obstruction.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Every bounded finite-projective complex over a principal localization
extends after adjoining its actual shift, up to a genuine chain-homotopy
equivalence. The extension is finite free with bounds `[a - 1, b]`. -/
theorem exists_bounded_finiteFree_stable_descent (r : R)
    (K : CochainComplex (ModuleCat.{u} (Localization (Submonoid.powers r))) ℤ)
    (a b : ℤ) (hbound : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite (Localization (Submonoid.powers r)) (K.X i))
    (hprojective : ∀ i, Module.Projective (Localization (Submonoid.powers r)) (K.X i)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, i < a - 1 ∨ b < i → IsZero (P.X i)) ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty (HomotopyEquiv ((localize r (.up ℤ)).obj P) (K ⊞ K⟦(1 : ℤ)⟧)) := by
  obtain ⟨T, hTb, hTf, ⟨eT⟩⟩ :=
    exists_bounded_finiteFree_stabilization K a b hbound hfinite hprojective
  obtain ⟨P, hPb, hPf, ⟨eP⟩⟩ := exists_bounded_finiteFree_complex_descent r T (a - 1) b
    hTb (fun i => (hTf i).1) (fun i => (hTf i).2)
  exact ⟨P, hPb, hPf, ⟨(HomotopyEquiv.ofIso eP).trans eT⟩⟩


end Quillen.ModuleComplex.PrincipalLocalization

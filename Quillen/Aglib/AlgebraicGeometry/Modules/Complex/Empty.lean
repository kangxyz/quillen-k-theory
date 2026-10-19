/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual acyclicity on an empty scheme

Every ordinary module-sheaf complex on a scheme with no points is acyclic: each
homology module is zero by stalk detection. Consequently restriction along an
open immersion with empty source, in particular the bottom open, is acyclic.
No boundedness, flatness, or perfectness hypothesis is needed.

Intended upstream owner: `Aglib.AlgebraicGeometry.Modules.Complex.Empty`.
The current consumer is the actual empty-open supported global Model comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Opens

/-- The scheme associated to the bottom open has no points. -/
instance isEmpty_toScheme_bot (X : Scheme.{u}) : IsEmpty ((⊥ : X.Opens) : Scheme) :=
  ⟨fun x => x.property⟩

end AlgebraicGeometry.Scheme.Opens

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- An actual complex on a scheme with no points has zero homology in every degree. -/
theorem acyclic_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (K : CochainComplex X.Modules ℤ) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (Scheme.Modules.isZero_iff_stalks _).mpr (fun x => isEmptyElim x)

/-- Restriction to any actual empty open immersion is acyclic. -/
theorem restrict_acyclic_of_isEmpty {U X : Scheme.{u}} [IsEmpty U]
    (j : U ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) :
    ((restrict j).obj K).Acyclic :=
  acyclic_of_isEmpty _

/-- Restriction to the bottom open is acyclic without an additional support premise. -/
theorem restrict_bot_acyclic {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) :
    ((restrict (⊥ : X.Opens).ι).obj K).Acyclic :=
  restrict_acyclic_of_isEmpty _ K

end AlgebraicGeometry.Scheme.Modules.Complex

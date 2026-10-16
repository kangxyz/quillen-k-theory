/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.CentralEndomorphism
public import Quillen.Aglib.Algebra.Category.FGModuleCat.SmallModelLocalization

/-!
# Dévissage for a locally nilpotent central endomorphism

A natural endomorphism of the identity gives a genuine dévissage property:
objects on which it vanishes. Its powers give actual finite image filtrations.
This construction will be applied to multiplication by an element on the
category of finite modules supported on its principal closed subset.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteModuleLocalization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

/-- The actual small abelian category of finite modules supported on `V(f)`. -/
abbrev PrincipalSupport := (smallTorsion (Submonoid.powers f)).FullSubcategory

/-- The faithful concrete representation in actual finite `R`-modules. -/
abbrev principalRepresentation : PrincipalSupport f ⥤ FGModuleCat.{u} R :=
  (smallTorsion (Submonoid.powers f)).ι ⋙ (equivSmallModel (FGModuleCat.{u} R)).inverse

/-- Multiplication by `f` on the actual supported category. -/
abbrev principalScalar : 𝟭 (PrincipalSupport f) ⟶ 𝟭 (PrincipalSupport f) :=
  PrincipalSupportDevissage.scalar (principalRepresentation f) f

/-- Supported finite modules killed by `f`, as opposed to a power of `f`. -/
abbrev principalKilled : ObjectProperty (PrincipalSupport f) :=
  PrincipalSupportDevissage.killed (principalScalar f)

/-- The categorical killed property is exactly ordinary scalar annihilation. -/
theorem principalKilled_iff (M : PrincipalSupport f) :
    principalKilled f M ↔ ∀ m : (principalRepresentation f).obj M, f • m = 0 :=
  PrincipalSupportDevissage.scalar_killed_iff (principalRepresentation f) f M

/-- Every supported finite module has its genuine finite image filtration,
with all successive factors annihilated by `f`. -/
theorem principalFiltrationHypothesis : Devissage.FiltrationHypothesis (principalKilled f) := by
  apply PrincipalSupportDevissage.filtrationHypothesis
  intro M
  obtain ⟨n, hn⟩ := (smallTorsion_powers_iff_uniform f M.obj).1 M.property
  exact ⟨n, PrincipalSupportDevissage.scalar_power_eq_zero
    (principalRepresentation f) f M n hn⟩

end Quillen.FiniteModuleLocalization

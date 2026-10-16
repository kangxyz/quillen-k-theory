/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Support.PrincipalAffineSmallModel

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.RestrictionExact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Principal
public import Quillen.Localization.SmallModel
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Support
public import Aglib.CategoryTheory.SmallModel.Functor

/-!
# G-theory of the actual principal supported presentation

The general exact categorical support presentation is imported from the local Aglib candidate. This downstream leaf forms its G-theory, proves the Q-construction comparison, and identifies the original supported G-group.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The geometric support term of the principal-open localization sequence. -/
abbrev PrincipalSupportedG (n : ℕ) : Type u :=
  (abelianExactStructure (principalSmallSupport R r).FullSubcategory).K n

instance principalSupportComparison_mapQ_isEquivalence :
    (principalSupportComparison R r).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change (abelianExactStructure (SupportedAffineFiniteType R (principalOpen R
      r))).smallModel.inflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    exact (principalSupportComparison R r).toFunctor.mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).mp hf)
  · intro M N f hf
    change (abelianExactStructure (SupportedAffineFiniteType R (principalOpen R
      r))).smallModel.deflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    exact (principalSupportComparison R r).toFunctor.epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).mp hf)

/-- Canonical exact-presentation comparison of the two actual supported
G-theory groups. -/
def principalSupportedGEquiv (n : ℕ) :
    SupportedAffineG R (principalOpen R r) n ≃* PrincipalSupportedG R r n :=
  (principalSupportComparison R r).KEquivOfMapQIsEquivalence n

end AlgebraicGeometry.Scheme.Modules.Coherent

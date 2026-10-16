/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Principal
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison
public import Quillen.Localization.SmallModel
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Actual global coherent support in the principal-open small model

The support category used by the small-model localization theorem is
explicitly equivalent to the actual global coherent sheaves supported away
from the principal open. The resulting K-equivalence uses the same upper
universe as the public global `G` and `SupportedG` definitions.
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

/-- The compatible supported K-term in the upper universe. -/
abbrev CoherentPrincipalSupportedG (n : ℕ) : Type (u + 1) :=
  (abelianExactStructure (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSmallSupport
    (principalOpen R r)).FullSubcategory).K n

instance coherentPrincipalSupportComparison_mapQ_isEquivalence :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSupportComparison (principalOpen R
      r)).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change (abelianExactStructure
      (SupportedFiniteTypeSheaves (principalOpen R r))).smallModel.inflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    exact (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSupportComparison
      (principalOpen R r)).toFunctor.mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).mp hf)
  · intro M N f hf
    change (abelianExactStructure
      (SupportedFiniteTypeSheaves (principalOpen R r))).smallModel.deflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    exact (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSupportComparison
      (principalOpen R r)).toFunctor.epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).mp hf)

/-- The public actual supported G-group agrees with the compatible support
term of the localization theorem, in the same universe. -/
def coherentPrincipalSupportedGEquiv (n : ℕ) :
    SupportedG (principalOpen R r) n ≃* CoherentPrincipalSupportedG R r n :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.coherentGlobalSupportComparison (principalOpen R
    r)).KEquivOfMapQIsEquivalence n

end AlgebraicGeometry.Scheme.Modules.Coherent

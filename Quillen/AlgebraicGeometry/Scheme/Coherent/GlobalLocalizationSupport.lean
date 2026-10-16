/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.Localization.SmallModel
public import Quillen.Devissage.Setup
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.SmallModel

/-!
# Actual global coherent support in the open-restriction small model

The support category used by the small-model localization theorem is
explicitly equivalent to the actual global coherent sheaves supported away
from the selected open. The resulting K-equivalence uses the same upper
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

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The compatible supported K-term in the upper universe. -/
abbrev CoherentGlobalSupportedG (n : ℕ) : Type (u + 1) :=
  (abelianExactStructure (coherentGlobalSmallSupport j).FullSubcategory).K n

instance coherentGlobalSupportComparison_mapQ_isEquivalence :
    (coherentGlobalSupportComparison j).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.inflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    exact (coherentGlobalSupportComparison j).toFunctor.mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).mp hf)
  · intro M N f hf
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.deflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    exact (coherentGlobalSupportComparison j).toFunctor.epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).mp hf)

/-- The public actual supported G-group agrees with the compatible support
term of the localization theorem, in the same universe. -/
def coherentGlobalSupportedGEquiv (n : ℕ) :
    SupportedG j n ≃* CoherentGlobalSupportedG j n :=
  (coherentGlobalSupportComparison j).KEquivOfMapQIsEquivalence n

end AlgebraicGeometry.Scheme.Modules.Coherent

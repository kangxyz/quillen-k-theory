/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RestrictionFunctoriality


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Quillen.Waldhausen.Functoriality.KMap

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-!
# Functoriality of actual open restriction on perfect-complex K-theory

The geometric identity and composition isomorphisms for sheaf restriction
lift to strict and locally perfect complexes. The original S-construction
K-maps inherit strict identity and composition laws. The original inclusion
from strict to locally perfect complexes commutes with restriction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

@[simp high]
theorem strictKRestrict_id (X : Scheme.{u}) (n : ℕ) :
    strictKRestrict (𝟙 X) n = MonoidHom.id (StrictK X n) :=
  (Waldhausen.KMap_eq_of_iso (strictRestrict_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (strictWaldhausen X).cof (strictWaldhausen X).weq)
    (strictRestrictIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem strictKRestrict_comp {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    strictKRestrict (i ≫ j) n = (strictKRestrict i n).comp (strictKRestrict j n) :=
  (Waldhausen.KMap_eq_of_iso (strictRestrict_waldhausenExact (i ≫ j))
    ((strictRestrict_waldhausenExact j).comp (strictRestrict_waldhausenExact i))
    (strictRestrictCompIso i j) n).trans
    (Quillen.Waldhausen.KMap_comp_KMap
      (strictRestrict_waldhausenExact j) (strictRestrict_waldhausenExact i) n).symm

@[simp high]
theorem perfectKRestrict_id (X : Scheme.{u}) (n : ℕ) :
    perfectKRestrict (𝟙 X) n = MonoidHom.id (PerfectK X n) :=
  (Waldhausen.KMap_eq_of_iso (perfectRestrict_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (perfectWaldhausen X).cof (perfectWaldhausen X).weq)
    (perfectRestrictIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem perfectKRestrict_comp {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    perfectKRestrict (i ≫ j) n = (perfectKRestrict i n).comp (perfectKRestrict j n) :=
  (Waldhausen.KMap_eq_of_iso (perfectRestrict_waldhausenExact (i ≫ j))
    ((perfectRestrict_waldhausenExact j).comp (perfectRestrict_waldhausenExact i))
    (perfectRestrictCompIso i j) n).trans
    (Quillen.Waldhausen.KMap_comp_KMap
      (perfectRestrict_waldhausenExact j) (perfectRestrict_waldhausenExact i) n).symm

/-- The original strict-to-local comparison commutes with actual open restriction. -/
theorem strictToPerfectKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (perfectKRestrict j n).comp (strictToPerfectKMap X n) =
      (strictToPerfectKMap U n).comp (strictKRestrict j n) := by
  unfold perfectKRestrict strictToPerfectKMap strictKRestrict Waldhausen.subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes

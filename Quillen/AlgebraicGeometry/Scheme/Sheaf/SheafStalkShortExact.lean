/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ClosedPushforwardExactness
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Actual module stalks jointly reflect short exactness
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- Exactness is detected on the actual module stalks of arbitrary module sheaves. -/
theorem exact_of_moduleStalk {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : ∀ x, (S.map (moduleStalk X x)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology]
  apply (isZero_iff_stalks _).mpr
  intro x
  have hz := (S.map (moduleStalk X x)).exact_iff_isZero_homology.mp (hS x)
  have hObj : IsZero ((moduleStalk X x).obj S.homology) :=
    hz.of_iso (S.mapHomologyIso (moduleStalk X x)).symm
  exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hObj).of_iso
    ((moduleStalkForgetIso X x).app S.homology).symm

/-- The three short-exactness conditions are detected jointly by actual module stalks. -/
theorem shortExact_of_moduleStalk {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : ∀ x, (S.map (moduleStalk X x)).ShortExact) : S.ShortExact where
  exact := exact_of_moduleStalk S (fun x => (hS x).exact)
  mono_f := mono_of_moduleStalk S.f (fun x => (hS x).mono_f)
  epi_g := epi_of_moduleStalk S.g (fun x => (hS x).epi_g)

/-- Faithful scalar restriction reflects all three short-exactness conditions. -/
theorem shortExact_of_restrictScalars {A B : Type u} [Ring A] [Ring B]
    (α : A →+* B) (S : ShortComplex (ModuleCat.{u} B))
    (hS : (S.map (ModuleCat.restrictScalars α)).ShortExact) : S.ShortExact := by
  let F := ModuleCat.restrictScalars α
  have hm : Mono (F.map S.f) := hS.mono_f
  have he : Epi (F.map S.g) := hS.epi_g
  exact
    { exact := F.reflects_exact_of_faithful S hS.exact
      mono_f := F.mono_of_mono_map hm
      epi_g := F.epi_of_epi_map he }

end Quillen.SchemeSheaf

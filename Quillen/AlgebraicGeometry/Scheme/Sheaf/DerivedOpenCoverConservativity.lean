/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Algebra.Homology.DerivedCategory.ExactFunctorHomology
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenCoverExactness
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedOpenBaseChange
/-! # Genuine open-cover detection in the bounded-below derived category

Actual derived restriction maps jointly reflect isomorphisms by the exact-functor homology
comparison and genuine open-cover reflection on module sheaves in every degree. The same
statement is retained for the original geometric derived open pullbacks. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
/-- The original standard ambient module-sheaf derived categories. -/
local instance openCoverDerivedStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (a i)] (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
include hcover in
/-- Actual derived restriction along a genuine open cover jointly reflects isomorphisms. -/
theorem isIso_of_derivedRestriction_openCover {K L : DerivedCategory.Plus X.Modules}
    (q : K ⟶ L) (hq : ∀ i, IsIso ((derivedRestrictionPlus (a i)).map q)) : IsIso q := by
  apply (DerivedCategory.Plus.isIso_iff q).mpr
  intro n
  apply isIso_of_restrict_openCover Y a hcover
  intro i
  let := hq i
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (a i)).rightDerivedFunctorPlusHomologyIso n) q).mp
    (show IsIso (((derivedRestrictionPlus (a i)) ⋙
      DerivedCategory.Plus.homologyFunctor (Y i).Modules n).map q) from by
        change IsIso ((DerivedCategory.Plus.homologyFunctor (Y i).Modules n).map
          ((derivedRestrictionPlus (a i)).map q))
        infer_instance)
include hcover in
/-- The literal derived geometric open pullbacks jointly reflect isomorphisms. -/
theorem isIso_of_derivedOpenPullback_openCover {K L : DerivedCategory.Plus X.Modules}
    (q : K ⟶ L) (hq : ∀ i, IsIso ((derivedFlatPullbackPlus (a i)).map q)) : IsIso q := by
  apply isIso_of_derivedRestriction_openCover Y a hcover q
  intro i
  let := hq i
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (a i)).rightDerivedFunctorPlusIso
      (Scheme.Modules.restrictFunctorIsoPullback (a i))) q).mpr
    (show IsIso ((derivedFlatPullbackPlus (a i)).map q) from inferInstance)
end Quillen.SchemeSheaf

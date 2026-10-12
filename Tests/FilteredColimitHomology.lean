/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso

/-! Regression consumers for natural filtered-colimit homology comparisons. -/

open CategoryTheory Limits
noncomputable section
universe u v w w' t
namespace Tests.FilteredColimitHomology

variable {R : Type v} [Ring R]
variable {J : Type w} [Category.{w'} J] [IsFiltered J]
  [UnivLE.{w, u}] [UnivLE.{w', u}]
variable {ι : Type t} {c : ComplexShape ι}

/-- Objectwise quasi-isomorphisms remain quasi-isomorphisms after filtered colimit. -/
theorem quasiIso_colimMap
    {F G : J ⥤ HomologicalComplex (ModuleCat.{u} R) c}
    (η : F ⟶ G) [∀ j, QuasiIso (η.app j)] : QuasiIso (colim.map η) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n
  let e := ModuleCat.filteredColimitHomologyNatIso R J c n
  have h : H.map (colim.map η) = e.hom.app F ≫ colim.map (Functor.whiskerRight η H) ≫
      e.inv.app G := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv (e.app G)).2 (e.hom.naturality η)
  change IsIso (H.map (colim.map η))
  rw [h]
  have : IsIso (Functor.whiskerRight η H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    change IsIso (HomologicalComplex.homologyMap (η.app j) n)
    infer_instance
  infer_instance

end Tests.FilteredColimitHomology

-- The coefficient ring need not fit in the universe of the module carriers.
example (R : Type (u + 1)) [Ring R]
    (F : ℕ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (colimit F).homology n ≅
      colimit (F ⋙ HomologicalComplex.homologyFunctor _ _ n) :=
  ModuleCat.filteredColimitHomologyIso R ℕ (ComplexShape.down ℕ) n F

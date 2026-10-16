/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# The actual single-of-cycles map

The original map from cycles in degree a retains its literal homology map and is a quasi-isomorphism under the exact stated lower-term and upper-cohomology bounds.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry Opposite ModuleCat HomologicalComplex
open AlgebraicGeometry.Scheme.Modules.Complex AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
/-- A map from the original cycle sheaf, placed in its original degree,
to the original complex. Its only nonzero component is the cycle inclusion. -/
def singleCyclesMap {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a : ℤ) :
    (CochainComplex.singleFunctor X.Modules a).obj (K.cycles a) ⟶ K :=
  mkHomFromSingle (K.iCycles a) (by intro j hj; simp)

/-- The single-cycle map induces exactly the original cycle-to-homology map. -/
theorem singleCyclesMap_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a : ℤ) :
    (singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv ≫
      homologyMap (singleCyclesMap K a) a = K.homologyπ a := by
  have hc : (singleObjCyclesSelfIso (.up ℤ) a (K.cycles a)).inv ≫
      cyclesMap (singleCyclesMap K a) a = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles a), Category.assoc, cyclesMap_i]
    dsimp only [singleCyclesMap]
    rw [mkHomFromSingle_f, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles]
    simp
  rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc, homologyπ_naturality,
    ← Category.assoc, hc, Category.id_comp]

/-- When the original complex starts at its sole cohomological degree, the
actual cycle inclusion is a quasi-isomorphism from a single complex. -/
theorem singleCyclesMap_quasiIso {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsLE a] : QuasiIso (singleCyclesMap K a) := by
  have : IsIso (K.homologyπ a) := by
    change IsIso ((K.isoHomologyπ (a - 1) a (by simp)
      ((K.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)).hom)
    infer_instance
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = a
  · subst i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have h := singleCyclesMap_homology K a
    have : IsIso ((singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv ≫
        homologyMap (singleCyclesMap K a) a) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff
      (singleObjHomologySelfIso (.up ℤ) a (K.cycles a)).inv _).mp inferInstance
  · apply (quasiIsoAt_iff_exactAt _ i
      (exactAt_single_obj (.up ℤ) a (K.cycles a) i hi)).mpr
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact K.exactAt_of_isGE a i hi
    · exact K.exactAt_of_isLE a i hi


end Quillen.PerfectComplexes.ProjectiveLine
end
end

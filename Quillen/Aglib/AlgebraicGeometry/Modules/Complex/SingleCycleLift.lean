/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Actual single maps from specified cycle maps

An original map into the cycles gives the literal single-complex chain map, and its homology map is the supplied composite with the homology projection.
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
/-- An actual morphism into the cycle sheaf gives the corresponding original
single-complex chain map, without a projectivity hypothesis. -/
def singleCycleLift {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (b : ℤ)
    (V : X.Modules) (v : V ⟶ K.cycles b) :
    (CochainComplex.singleFunctor X.Modules b).obj V ⟶ K :=
  HomologicalComplex.mkHomFromSingle (v ≫ K.iCycles b) (by intro j hj; simp)

/-- The original homology map of the cycle lift is its specified map to homology. -/
theorem singleCycleLift_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (b : ℤ)
    (V : X.Modules) (v : V ⟶ K.cycles b) :
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) b V).inv ≫
      HomologicalComplex.homologyMap (singleCycleLift K b V v) b = v ≫ K.homologyπ b := by
  have hc : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) b V).inv ≫
      HomologicalComplex.cyclesMap (singleCycleLift K b V v) b = v := by
    rw [← cancel_mono (K.iCycles b), Category.assoc, HomologicalComplex.cyclesMap_i]
    dsimp only [singleCycleLift]
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles]
    simp
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]


end Quillen.PerfectComplexes.ProjectiveLine
end
end

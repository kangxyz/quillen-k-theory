/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.ClassifyingSpace.Constant
public import Quillen.Topology.Realization.HomotopyBridge
public import Quillen.Topology.HomotopyFiber.Basic
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Quillen.Localization.Serre.Localization
public import Quillen.Devissage.Setup
public import Quillen.CategoryTheory.QConstruction.ZeroFunctor

/-! # The categorical nullhomotopy data for Serre localization

The quotient after the exact inclusion of the Serre subcategory is naturally
isomorphic, at the Q-category level, to the constant zero functor. This is
actual comparison data; a homotopy-fiber equivalence is not asserted here.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- Canonical categorical nullhomotopy data for the quotient composed with
inclusion of the Serre class. -/
def quotientInclusionZeroIso :
    Devissage.mapQ P ⋙ quotientMapQ P ≅
      (Functor.const (CategoryTheory.ObjectProperty.subcategoryExactStructure P).QCategory).obj
        (quotientExactStructure P).qZero :=
  (quotientExactStructure P).qFunctorIsoConstZero _ (fun X =>
    (quotient_isZero_obj_iff P X.obj.of.obj).2 X.obj.of.property)

/-- Realizing the categorical zero comparison gives an actual nullhomotopy
of the quotient map composed with the inclusion map. -/
def quotientInclusionNullhomotopy :
    ((classifyingSpaceMap (quotientMapQ P)).hom.comp
      (classifyingSpaceMap (Devissage.mapQ P)).hom).Homotopy
      (ContinuousMap.const _ (quotientExactStructure P).kBasepoint) :=
  (classifyingSpaceNaturalTransformationHomotopy (quotientInclusionZeroIso P).hom).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The genuine map from the Serre Q-space to the path-space homotopy fiber
of the quotient. Proving it is a homotopy equivalence is the still-open
homotopical localization theorem. -/
def localizationFiberComparison :
    C((CategoryTheory.ObjectProperty.subcategoryExactStructure P).KSpace,
      HomotopyFiber (classifyingSpaceMap (quotientMapQ P)).hom
        (quotientExactStructure P).kBasepoint) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (Devissage.mapQ P)).hom
    (quotientInclusionNullhomotopy P)

/-- The fiber comparison really lies over the inclusion, strictly. -/
@[simp]
theorem localizationFiberComparison_projection :
    (HomotopyFiber.projection (classifyingSpaceMap (quotientMapQ P)).hom
      (quotientExactStructure P).kBasepoint).comp (localizationFiberComparison P) =
      (classifyingSpaceMap (Devissage.mapQ P)).hom :=
  HomotopyFiber.projection_lift _ _ _ _

end Quillen.SerreLocalization

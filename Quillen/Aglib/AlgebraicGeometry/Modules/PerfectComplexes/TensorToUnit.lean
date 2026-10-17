/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorByLine
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalScalar

/-!
# Scalar and perfect specializations of the canonical tensor-to-unit map

The general transformation associated to an actual arrow `L ⟶ O_X`, its section/restriction
formulas and its ordinary-complex/single comparisons have one implementation in Aglib.
The original global-scalar equation and the chart-trivialized perfect wrappers remain here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory AlgebraicGeometry Opposite SheafOfModulesOfCommRing
namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Modules

/-- The original unit scalar becomes the original scalar on every coefficient module. -/
theorem moduleLineCoordinate_unitMul (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.tensorToUnit (unitMul X r) =
      (tensorLeftUnitIso X.sheaf).hom ≫ globalScalar X r := by
  apply NatTrans.ext
  funext M
  apply moduleTensor_hom_ext
  intro U a m
  change Γ(X, U) at a
  rw [AlgebraicGeometry.Scheme.Modules.tensorToUnit_section]
  have hu := congrArg (fun g => g.app (op U) (a ⊗ₜ[Γ(X, U)] m))
    (associatedSheafUnit_tensorLeftUnitIso X.sheaf M)
  change ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
    (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m) = a • m at hu
  let s : Γ(X, U) := (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom r
  change (a * s) • m = s •
      (((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U a m))
  rw [hu, smul_smul, mul_comm]

variable {X : Scheme.{u}} (L : X.Modules) {ι : Type v}
  (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ i y, j i y = x)
  (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)

/-- The same actual map between the existing perfect line tensor and the identity. -/
def perfectLineCoordinate (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    perfectTensorByLine L Y j hc e ⟶ 𝟭 (Perfect X) where
  app K := (locallyPerfect X).homMk
    ((AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K.obj)
  naturality K M g := by
    apply (locallyPerfect X).ι.map_injective
    exact (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).naturality g.hom

/-- Faithful inclusion retains the literal canonical complex tensor-to-unit map. -/
theorem perfectLineCoordinate_original (f : L ⟶ SheafOfModules.unit X.ringCatSheaf)
    (K : Perfect X) :
    (locallyPerfect X).ι.map ((perfectLineCoordinate L Y j hc e f).app K) =
      (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app K.obj := rfl

end Quillen.PerfectComplexes

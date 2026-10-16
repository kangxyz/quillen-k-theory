/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.ModuleColumns
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing
public import Aglib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# The canonical negative twist on the two-chart line

For each module sheaf, the kernel of the paired chart obstructions glues the actual graph columns
(1,t) and (s,1). Both chart isomorphisms preserve the original kernel inclusion.
-/
@[expose] public section

open ModuleCat
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- The paired direct-image obstructions to lying in both original chart columns. -/
def twistMinusObstruction :=
  prod.lift
    (AlgebraicGeometry.Scheme.Modules.subobjectObstruction (plusChart R)
      (moduleFirstColumn (plusChart R) M (polynomialCoordinate R)))
    (AlgebraicGeometry.Scheme.Modules.subobjectObstruction (minusChart R)
      (moduleSecondColumn (minusChart R) M (polynomialCoordinate R)))

/-- The canonical kernel sheaf gluing the negative-twist chart columns. -/
def twistMinus : (twoChartLine R).Modules := kernel (twistMinusObstruction R M)

/-- The original kernel inclusion into the module square. -/
def twistMinusInclusion : twistMinus R M ⟶ M ⨯ M := kernel.ι (twistMinusObstruction R M)

instance twistMinusInclusion_mono : Mono (twistMinusInclusion R M) := by
  change Mono (kernel.ι _)
  infer_instance

lemma twistMinusObstruction_plus_zero :
    moduleFirstColumn (plusChart R) M (polynomialCoordinate R) ≫
      (Scheme.Modules.restrictFunctor (plusChart R)).map (twistMinusObstruction R M) = 0 := by
  have h := AlgebraicGeometry.Scheme.Modules.overlapCompatible_obstruction_zero (plusChart R)
    (minusChart R)
    (moduleFirstColumn (plusChart R) M (polynomialCoordinate R))
    (moduleSecondColumn (minusChart R) M (polynomialCoordinate R))
    (moduleColumnTransition (plusChart R) (minusChart R) M (overlapCoordinateUnit R))
    (moduleColumns_compatible (plusChart R) (minusChart R) M
      (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl)
  exact CategoryTheory.Limits.map_prod_lift_comp_eq_zero (Scheme.Modules.restrictFunctor
    (plusChart R)) _ _ _
    (AlgebraicGeometry.Scheme.Modules.subobjectObstruction_local_zero _ _) h.1

lemma twistMinusObstruction_minus_zero :
    moduleSecondColumn (minusChart R) M (polynomialCoordinate R) ≫
      (Scheme.Modules.restrictFunctor (minusChart R)).map (twistMinusObstruction R M) = 0 := by
  have h := AlgebraicGeometry.Scheme.Modules.overlapCompatible_obstruction_zero (plusChart R)
    (minusChart R)
    (moduleFirstColumn (plusChart R) M (polynomialCoordinate R))
    (moduleSecondColumn (minusChart R) M (polynomialCoordinate R))
    (moduleColumnTransition (plusChart R) (minusChart R) M (overlapCoordinateUnit R))
    (moduleColumns_compatible (plusChart R) (minusChart R) M
      (polynomialCoordinate R) (polynomialCoordinate R) (overlapCoordinateUnit R) rfl rfl)
  exact CategoryTheory.Limits.map_prod_lift_comp_eq_zero (Scheme.Modules.restrictFunctor
    (minusChart R)) _ _ _
    h.2 (AlgebraicGeometry.Scheme.Modules.subobjectObstruction_local_zero _ _)

/-- The positive chart column is the kernel of the restricted global obstruction. -/
def twistMinusPlusIsKernel : IsLimit (KernelFork.ofι
    (moduleFirstColumn (plusChart R) M (polynomialCoordinate R))
    (twistMinusObstruction_plus_zero R M)) := by
  let := moduleFirstColumn_mono (plusChart R) M (polynomialCoordinate R)
  exact isKernelOfComp ((Scheme.Modules.restrictFunctor (plusChart R)).map prod.fst)
    ((Scheme.Modules.restrictFunctor (plusChart R)).map
      (AlgebraicGeometry.Scheme.Modules.subobjectObstruction (plusChart R)
        (moduleFirstColumn (plusChart R) M (polynomialCoordinate R))))
    (AlgebraicGeometry.Scheme.Modules.subobjectObstructionKernelIsLimit _ _)
      (twistMinusObstruction_plus_zero R M)
    (by rw [← Functor.map_comp]; exact congrArg _ (prod.lift_fst _ _))

/-- The negative chart column is the kernel of the restricted global obstruction. -/
def twistMinusMinusIsKernel : IsLimit (KernelFork.ofι
    (moduleSecondColumn (minusChart R) M (polynomialCoordinate R))
    (twistMinusObstruction_minus_zero R M)) := by
  let := moduleSecondColumn_mono (minusChart R) M (polynomialCoordinate R)
  exact isKernelOfComp ((Scheme.Modules.restrictFunctor (minusChart R)).map prod.snd)
    ((Scheme.Modules.restrictFunctor (minusChart R)).map
      (AlgebraicGeometry.Scheme.Modules.subobjectObstruction (minusChart R)
        (moduleSecondColumn (minusChart R) M (polynomialCoordinate R))))
    (AlgebraicGeometry.Scheme.Modules.subobjectObstructionKernelIsLimit _ _)
      (twistMinusObstruction_minus_zero R M)
    (by rw [← Functor.map_comp]; exact congrArg _ (prod.lift_snd _ _))

/-- Positive-chart identification preserving the original kernel inclusion. -/
def twistMinusPlusIso : (twistMinus R M).restrict (plusChart R) ≅ M.restrict (plusChart R) :=
  (KernelFork.mapIsLimit _ (kernelIsKernel (twistMinusObstruction R M))
    (Scheme.Modules.restrictFunctor (plusChart R))).conePointUniqueUpToIso
      (twistMinusPlusIsKernel R M)

/-- Negative-chart identification preserving the original kernel inclusion. -/
def twistMinusMinusIso : (twistMinus R M).restrict (minusChart R) ≅ M.restrict (minusChart R) :=
  (KernelFork.mapIsLimit _ (kernelIsKernel (twistMinusObstruction R M))
    (Scheme.Modules.restrictFunctor (minusChart R))).conePointUniqueUpToIso
      (twistMinusMinusIsKernel R M)

lemma twistMinusInclusion_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (twistMinusInclusion R M) =
      (twistMinusPlusIso R M).hom ≫ moduleFirstColumn (plusChart R) M (polynomialCoordinate R) :=
  ((KernelFork.mapIsLimit _ (kernelIsKernel (twistMinusObstruction R M))
    (Scheme.Modules.restrictFunctor (plusChart R))).conePointUniqueUpToIso_hom_comp
      (twistMinusPlusIsKernel R M) WalkingParallelPair.zero).symm

lemma twistMinusInclusion_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (twistMinusInclusion R M) =
      (twistMinusMinusIso R M).hom ≫ moduleSecondColumn (minusChart R) M (polynomialCoordinate R) :=
  ((KernelFork.mapIsLimit _ (kernelIsKernel (twistMinusObstruction R M))
    (Scheme.Modules.restrictFunctor (minusChart R))).conePointUniqueUpToIso_hom_comp
      (twistMinusMinusIsKernel R M) WalkingParallelPair.zero).symm

end AlgebraicGeometry.Scheme.ProjectiveLine

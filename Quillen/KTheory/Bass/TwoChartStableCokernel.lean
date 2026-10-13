/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.TwoChartSigns
public import Quillen.Topology.Prespectrum.ConeStableCokernel
public import Quillen.Topology.Prespectrum.StableShift

/-!
# Two-chart degree-minus-one cone presentations

A proved surjective pair of chart inclusions converts the actual cone cokernel into the
classical chart difference. The original signed parameter-loop shift then identifies degree
minus one of the unchanged looped cone, with its literal Laurent representative map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.LoopPrespectrum
universe u
namespace Quillen.Bass
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f))
  [Subsingleton (stableHomotopyGroup E (-1))]
  {A B : AddCommGrpCat.{u}} (i : A ⊞ B ⟶ (stableHomotopyFunctor 0).obj E) [Epi i]
  (p : A ⟶ (stableHomotopyFunctor 0).obj F) (m : B ⟶ (stableHomotopyFunctor 0).obj F)
  (h : i ≫ (stableHomotopyFunctor 0).map f = biprod.desc p m)

/-- Original chart generation and cone exactness give the actual signed chart cokernel. -/
def chartDifferenceConeCokernelIso :
    cokernel (biprod.desc p (-m)) ≅ stableHomotopyGroup (mappingCone f) 0 :=
  chartDifferenceCokernelIsoOfEpi i ((stableHomotopyFunctor 0).map f) p m h ≪≫
    stableMappingConeZeroCokernelIso f hf

/-- The chart cokernel comparison retains each original target representative. -/
@[reassoc]
theorem chartDifferenceConeCokernelIso_π :
    cokernel.π (biprod.desc p (-m)) ≫ (chartDifferenceConeCokernelIso f hf i p m h).hom =
      (stableHomotopyFunctor 0).map (mappingConeInclusion f) := by
  simp only [chartDifferenceConeCokernelIso, Iso.trans_hom, ← Category.assoc,
    chartDifferenceCokernelIsoOfEpi_π, stableMappingConeZeroCokernelIso_π]

/-- The original integer-graded loop shift identifies the unchanged first looped cone. -/
def chartDifferenceLoopedConeIso :
    cokernel (biprod.desc p (-m)) ≅
      stableHomotopyGroup (parameterLooping (mappingCone f)) (-1) :=
  chartDifferenceConeCokernelIso f hf i p m h ≪≫
    (eqToIso (congrArg (stableHomotopyGroup (mappingCone f))
      (show (0 : ℤ) = -1 + 1 by decide))) ≪≫
      (parameterStableHomotopyIso (mappingCone f) (-1)).symm

/-- Original target classes enter the actual cone and then the genuine signed loop shift. -/
@[reassoc]
theorem chartDifferenceLoopedConeIso_π :
    cokernel.π (biprod.desc p (-m)) ≫ (chartDifferenceLoopedConeIso f hf i p m h).hom =
      (stableHomotopyFunctor 0).map (mappingConeInclusion f) ≫
        (eqToHom (congrArg (stableHomotopyGroup (mappingCone f))
          (show (0 : ℤ) = -1 + 1 by decide))) ≫
          (parameterStableHomotopyIso (mappingCone f) (-1)).inv := by
  simp only [chartDifferenceLoopedConeIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, chartDifferenceConeCokernelIso_π, eqToIso.hom]

end Quillen.Bass

namespace Quillen.Bass
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f)) (d : ℤ)
  [Subsingleton (stableHomotopyGroup E (d - 1))]
  {A B : AddCommGrpCat.{u}} (i : A ⊞ B ⟶ (stableHomotopyFunctor d).obj E) [Epi i]
  (p : A ⟶ (stableHomotopyFunctor d).obj F) (m : B ⟶ (stableHomotopyFunctor d).obj F)
  (h : i ≫ (stableHomotopyFunctor d).map f = biprod.desc p m)

/-- Original chart generation and cone exactness identify the signed-degree chart cokernel. -/
def chartDifferenceConeDegreeCokernelIso :
    cokernel (biprod.desc p (-m)) ≅ stableHomotopyGroup (mappingCone f) d :=
  chartDifferenceCokernelIsoOfEpi i ((stableHomotopyFunctor d).map f) p m h ≪≫
    stableMappingConeDegreeCokernelIso f hf d

/-- The signed-degree chart comparison retains the original target representative arrow. -/
@[reassoc]
theorem chartDifferenceConeDegreeCokernelIso_π :
    cokernel.π (biprod.desc p (-m)) ≫
      (chartDifferenceConeDegreeCokernelIso f hf d i p m h).hom =
      (stableHomotopyFunctor d).map (mappingConeInclusion f) := by
  simp only [chartDifferenceConeDegreeCokernelIso, Iso.trans_hom, ← Category.assoc,
    chartDifferenceCokernelIsoOfEpi_π, stableMappingConeDegreeCokernelIso_π]

/-- The genuine signed loop shift identifies the chart cokernel with degree d minus one of
this same original looped cone. -/
def chartDifferenceLoopedConeDegreeIso :
    cokernel (biprod.desc p (-m)) ≅
      stableHomotopyGroup (parameterLooping (mappingCone f)) (d - 1) :=
  chartDifferenceConeDegreeCokernelIso f hf d i p m h ≪≫
    eqToIso (congrArg (stableHomotopyGroup (mappingCone f)) (sub_add_cancel d 1).symm) ≪≫
      (parameterStableHomotopyIso (mappingCone f) (d - 1)).symm

/-- Original signed-degree classes enter through the unchanged cone inclusion and actual shift.
-/
@[reassoc]
theorem chartDifferenceLoopedConeDegreeIso_π :
    cokernel.π (biprod.desc p (-m)) ≫
      (chartDifferenceLoopedConeDegreeIso f hf d i p m h).hom =
      (stableHomotopyFunctor d).map (mappingConeInclusion f) ≫
        eqToHom (congrArg (stableHomotopyGroup (mappingCone f)) (sub_add_cancel d 1).symm) ≫
          (parameterStableHomotopyIso (mappingCone f) (d - 1)).inv := by
  simp only [chartDifferenceLoopedConeDegreeIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, chartDifferenceConeDegreeCokernelIso_π, eqToIso.hom]

end Quillen.Bass

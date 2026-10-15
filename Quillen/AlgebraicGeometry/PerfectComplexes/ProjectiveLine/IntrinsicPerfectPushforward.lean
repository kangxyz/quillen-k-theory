/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.QuasicoherentRepresentative
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativePerfectPushforward

/-! # Actual projective-line direct image on arbitrary intrinsic perfect objects

The constructed quasicoherent representative and nonnoetherian strictification
supply a genuine global strict model. The original projection's bounded-below
derived direct image is therefore perfect over every commutative ring.
The strict representative is asserted objectwise; no natural choice of models
or functorial diagonal-generation statement is inferred from these isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The standard derived category of module sheaves, used for intrinsic perfect direct images. -/
local instance intrinsicProjectionStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- Every intrinsic perfect bounded-below derived object on the actual line
has a genuine global strict model, with no replacement premise on the caller. -/
theorem exists_strict_model_of_perfect_plus (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    ∃ P : StrictPerfect (twoChartLine R),
      Nonempty ((strictToDerivedPlus (twoChartLine R)).obj P ≅ K) := by
  obtain ⟨L, hLq, ⟨eL⟩⟩ := exists_quasicoherent_model_of_perfect_plus R K hK
  have hL : locallyPerfect (twoChartLine R) L.obj :=
    (perfectDerivedObjects_toDerived_iff (twoChartLine R) L.obj).mp
      ((perfectDerivedObjects (twoChartLine R)).prop_of_iso
        (DerivedCategory.Plus.ι.mapIso eL.symm) hK)
  obtain ⟨a, ha⟩ := L.property
  have : L.obj.IsStrictlyGE a := ha
  obtain ⟨P, ⟨eP⟩⟩ := exists_strict_model_of_boundedBelow_quasicoherent R L.obj a hLq hL
  let e : (strictToDerivedPlus (twoChartLine R)).obj P ≅ DerivedCategory.Plus.Q.obj L :=
    DerivedCategory.Plus.ι.preimageIso eP
  exact ⟨P, ⟨e ≪≫ eL⟩⟩

/-- The original actual projective-line projection preserves intrinsic
perfectness on every bounded-below derived input over any commutative ring.
The genuine QC representative is constructed by the proof, not supplied. -/
theorem perfect_derivedProjection_of_perfect (R : CommRingCat.{u})
    (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K)) :
    perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (projection R)).obj K)) := by
  obtain ⟨P, hPq, ⟨eP⟩⟩ := exists_quasicoherent_model_of_perfect_plus R K hK
  exact perfect_derivedProjection_of_quasicoherent_model R K hK P hPq eP

end Quillen.PerfectComplexes.ProjectiveLine

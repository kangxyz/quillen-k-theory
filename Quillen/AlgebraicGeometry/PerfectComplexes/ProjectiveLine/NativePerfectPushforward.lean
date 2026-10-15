/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.Strictification
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BoundedDerivedPushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPushforwardComparison

/-! # Actual projective-line direct image from quasicoherent representatives

The proved nonnoetherian strictification supplies perfectness of the original
projection's derived direct image for bounded-below, termwise quasicoherent,
locally perfect representatives. Arbitrary intrinsic perfect objects still
require a genuine quasicoherent representative; that existence is not an axiom
or an implicit input to the unrestricted projection theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
namespace Quillen.PerfectComplexes.ProjectiveLine

/-- The standard derived category of module sheaves, used for perfect projection pushforward. -/
local instance nativePushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _

/-- The original affine projection takes a bounded-below quasicoherent
locally perfect representative to an intrinsically perfect derived object,
over every commutative ring. Its terms need not be vector bundles or bounded above. -/
theorem perfect_derivedProjection_of_quasicoherent_plus
    (R : CommRingCat.{u}) (K : CochainComplex.Plus (twoChartLine R).Modules)
    (hqc : ∀ i, (K.obj.X i).IsQuasicoherent)
    (hK : locallyPerfect (twoChartLine R) K.obj) :
    perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (projection R)).obj (DerivedCategory.Plus.Q.obj K))) := by
  obtain ⟨c, hc⟩ := K.property
  have : K.obj.IsStrictlyGE c := hc
  obtain ⟨P, ⟨eP⟩⟩ := exists_strict_model_of_boundedBelow_quasicoherent R K.obj c hqc hK
  let e : (strictToDerivedPlus (twoChartLine R)).obj P ≅ DerivedCategory.Plus.Q.obj K :=
    DerivedCategory.Plus.ι.preimageIso eP
  obtain ⟨a, b, hab⟩ := P.property.1
  have hp := perfect_derivedPushforward_of_bounded_vectorBundle_terms R
    ((strictToPlus (twoChartLine R)).obj P) a b
    (fun i hi => hab i (Or.inl hi)) (fun i hi => hab i (Or.inr hi)) P.property.2
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso ((derivedPushforwardPlus (projection R)).mapIso e)) hp

/-- An intrinsic perfect input with a supplied genuine bounded-below QC
representative has perfect actual derived projection. Constructing that
representative for arbitrary perfect inputs remains a separate obligation. -/
theorem perfect_derivedProjection_of_quasicoherent_model
    (R : CommRingCat.{u}) (K : DerivedCategory.Plus (twoChartLine R).Modules)
    (hK : perfectDerivedObjects (twoChartLine R) (DerivedCategory.Plus.ι.obj K))
    (P : CochainComplex.Plus (twoChartLine R).Modules)
    (hqc : ∀ i, (P.obj.X i).IsQuasicoherent) (e : DerivedCategory.Plus.Q.obj P ≅ K) :
    perfectDerivedObjects (Spec R) (DerivedCategory.Plus.ι.obj
      ((derivedPushforwardPlus (projection R)).obj K)) := by
  have hP : locallyPerfect (twoChartLine R) P.obj :=
    (perfectDerivedObjects_toDerived_iff (twoChartLine R) P.obj).mp
      ((perfectDerivedObjects (twoChartLine R)).prop_of_iso
        (DerivedCategory.Plus.ι.mapIso e.symm) hK)
  exact (perfectDerivedObjects (Spec R)).prop_of_iso
    (DerivedCategory.Plus.ι.mapIso ((derivedPushforwardPlus (projection R)).mapIso e))
    (perfect_derivedProjection_of_quasicoherent_plus R P hqc hP)

end Quillen.PerfectComplexes.ProjectiveLine

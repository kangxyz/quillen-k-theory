/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.PullbackPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Locality.QuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5PositiveUnitModel

/-! # The canonical native positive unit and its actual weak model transformation

Original affine-chart QIs reflect the actual global cochain QI. The result is
then lifted by literal underlying maps into the original flasque-perfect model,
where the natural weak unit gives the original positive coefficient K-map.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.ProjectiveLine


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

/-- The native affine projection has the same actual canonical cochain unit. -/
theorem positivePlusUnit_nativeAffine_quasiIso (R : CommRingCat.{u})
    (K : CochainComplex.Plus (Spec R).Modules) (hK : locallyPerfect (Spec R) K.obj) :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit
      (nativeProjection.app ⟨Spec R, inferInstance⟩).hom).app K).hom := by
  apply quasiIso_of_restrict_openCover (fun _ : Unit => Spec R) (fun _ => 𝟙 (Spec R))
    (fun x => ⟨(), x, rfl⟩)
  intro i
  exact AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit_restrict_quasiIso
    (nativeAffineIso R).hom (projection R)
    (nativeProjection.app ⟨Spec R, inferInstance⟩).hom (𝟙 (Spec R))
    (nativeAffineProjection_isPullback R) K
    (positivePlusUnit_affine_quasiIso R _ (locallyPerfect_restrict (𝟙 (Spec R)) hK))

/-- Every native QC base has the same original canonical QI, with no term-QC premise. -/
theorem positivePlusUnit_native_quasiIso (X : QuasiCompactSchemes.{u})
    (K : CochainComplex.Plus X.obj.Modules) (hK : locallyPerfect X.obj K.obj) :
    QuasiIso ((AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit
      (nativeProjection.app X).hom).app K).hom := by
  apply quasiIso_of_restrict_openCover
    (fun i => Spec (X.obj.affineOpenCover.X i)) X.obj.affineOpenCover.f
    (fun x => ⟨_, X.obj.affineOpenCover.covers x⟩)
  intro i
  let U : QuasiCompactSchemes.{u} := ⟨Spec (X.obj.affineOpenCover.X i), inferInstance⟩
  let j : U ⟶ X := ⟨X.obj.affineOpenCover.f i⟩
  exact AlgebraicGeometry.Scheme.Modules.Godement.pullbackPushforwardPlusUnit_restrict_quasiIso
    (nativeLineFunctor.map j).hom
    (nativeProjection.app U).hom (nativeProjection.app X).hom j.hom
    (nativeMap_isPullback j) K
    (positivePlusUnit_nativeAffine_quasiIso (X.obj.affineOpenCover.X i) _
      (locallyPerfect_restrict j.hom hK))

lemma positiveUnit_weak (X : QuasiCompactSchemes.{u}) (A : FlasqueBoundedBelow.Obj X.obj) :
    (FlasqueBoundedBelow.waldhausen X.obj).weq ((positiveUnit X).app A) :=
  positivePlusUnit_native_quasiIso X _ A.property.1.1

/-- The actual natural weak unit gives equality of original positive K-maps in every degree. -/
theorem positive_KMap_eq_id (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Waldhausen.KMap (positive_exact X) n =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen X.obj).K n) :=
  (Waldhausen.KMap_eq_of_weakNatTrans
    (Waldhausen.IsExact.id (FlasqueBoundedBelow.waldhausen X.obj).cof
      (FlasqueBoundedBelow.waldhausen X.obj).weq)
    (positive_exact X) (positiveUnit X) (positiveUnit_weak X) n).symm.trans
      (Waldhausen.KMap_id (FlasqueBoundedBelow.waldhausen X.obj) n)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativePositiveUnit

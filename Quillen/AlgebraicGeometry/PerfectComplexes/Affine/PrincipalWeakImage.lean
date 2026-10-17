/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Stabilization


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenWeakImage
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PrincipalProjectiveExtension
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! # Actual stabilization density in the principal-open witnessed image

Every affine principal-open strict target, after adding its original shift,
lies in the actual one-arrow restriction image. The proof uses the forward
chain map of the genuine geometric homotopy equivalence. A given actual weak
strict comparison transports this membership to a locally perfect target.
No App2, affine strictification, unstabilized extension or K-zero surjectivity
is assumed or asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.OpenWeakImage

/-- Stabilized strict targets belong to the actual witnessed restriction image,
without a geometric map-factorization assumption. -/
theorem principal_strict_shiftSum_mem (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    Waldhausen.ApproximationImage.objects (perfectWaldhausen _)
      (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r))
      (shiftSum ((strictToPerfect _).obj P)) := by
  obtain ⟨Q, ⟨e⟩⟩ := Affine.exists_principal_strict_extension_after_shift R r P
  exact ⟨(strictToPerfect _).obj Q, ObjectProperty.homMk e.hom, e.quasiIso_hom⟩

/-- A specified actual strict comparison suffices to transport stabilized
membership; existence of that comparison is kept as a separate input. -/
theorem principal_shiftSum_mem_of_strict_comparison (R : CommRingCat.{u}) (r : R)
    (B : Perfect (Spec (.of (Localization.Away r))))
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (f : (strictToPerfect _).obj P ⟶ B) (hf : (perfectWaldhausen _).weq f) :
    Waldhausen.ApproximationImage.objects (perfectWaldhausen _)
      (perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) (shiftSum
        B) :=
  Waldhausen.ApproximationImage.mem_of_weak _ _ (shiftSumMap f) (shiftSumMap_weak f hf)
    (principal_strict_shiftSum_mem R r P)

/-- The genuine strict-density object in the named actual image category. -/
def principalStrictShiftSum (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    Obj (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) :=
  ⟨shiftSum ((strictToPerfect _).obj P), principal_strict_shiftSum_mem R r P⟩

/-- Its actual complex is exactly the original sum with the original shift. -/
@[simp] theorem principalStrictShiftSum_obj (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    (principalStrictShiftSum R r P).obj.obj = (P.obj ⊞ P.obj⟦(1 : ℤ)⟧) := rfl

end Quillen.PerfectComplexes.OpenWeakImage

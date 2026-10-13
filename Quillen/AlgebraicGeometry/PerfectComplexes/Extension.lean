/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalTriangles

/-!
# Actual extension closure of locally perfect complexes

Near a point both endpoints of a short exact sequence admit strict models
on a common open. The inverse rotation of the actual derived exact triangle
is then locally a chain mapping-cone triangle. This proves the middle
complex locally perfect, rather than postulating extension closure.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Local perfectness is closed under actual short exact sequences of sheaf
complexes. No global strict representative or resolution property is assumed. -/
theorem locallyPerfect_of_shortExact {X : Scheme.{u}} {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) (h₁ : locallyPerfect X S.X₁) (h₃ : locallyPerfect X S.X₃) :
    locallyPerfect X S.X₂ := by
  apply locallyPerfect_of_openImmersion_models
  intro x
  obtain ⟨U, hxU, ⟨P, ⟨eP⟩⟩, ⟨Q, ⟨eQ⟩⟩⟩ := exists_common_strictModels h₁ h₃ x
  let SU := S.map (restrict U.ι)
  have hSU : SU.ShortExact := hS.map_of_exact (restrict U.ι)
  let T := shortExactTriangle hSU
  let Q' := (shiftFunctor (Complex U.toScheme) (-1)).obj Q.obj
  let eQ' : T.invRotate.obj₁ ≅ (toDerived U.toScheme).obj Q' :=
    (shiftFunctor (Derived U.toScheme) (-1)).mapIso eQ ≪≫
      ((toDerived U.toScheme).commShiftIso (-1)).symm.app Q.obj
  obtain ⟨Y, j, hj, y, hy, h⟩ := exists_local_strictModel_of_triangle T.invRotate
    (inv_rot_of_distTriang T (shortExactTriangle_distinguished hSU))
    (strictPerfect_shift Q.property (-1)) P.property eQ' eP (Iso.refl _) ⟨x, hxU⟩
  let := hj
  refine ⟨Y, j ≫ U.ι, inferInstance, y, ?_, ?_⟩
  · change U.ι (j y) = x
    rw [hy]
    rfl
  · exact h.of_iso ((restrictCompIso j U.ι).app S.X₂)

instance locallyPerfect_extensionClosed (X : Scheme.{u}) :
    (abelianExactStructure (Complex X)).IsExtensionClosed (locallyPerfect X) where
  prop_middle := locallyPerfect_of_shortExact

instance locallyPerfect_closedUnderFiniteProducts (X : Scheme.{u}) :
    (locallyPerfect X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (locallyPerfect X)

end Quillen.PerfectComplexes

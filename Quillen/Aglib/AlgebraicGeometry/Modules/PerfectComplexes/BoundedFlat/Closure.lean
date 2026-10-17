/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure

/-!
# Shifts and cones of bounded-flat perfect complexes

The original term bounds and flat finite-sum arguments preserve actual shifts and mapping cones.
-/
@[expose] public section




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

theorem boundedFlatPerfect_shift {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : boundedFlatPerfect X K) (n : ℤ) :
    boundedFlatPerfect X ((shiftFunctor (CochainComplex X.Modules ℤ) n).obj K) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨Complex.locallyPerfect_shift hp n,
    ⟨b-n, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, fun i => hf (i+n)⟩
  intro i hi
  change IsZero (K.X (i+n))
  exact K.isZero_of_isStrictlyLE b (i+n) (by omega)

theorem boundedFlatPerfect_mappingCone {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : boundedFlatPerfect X K) (hL : boundedFlatPerfect X L) (f : K ⟶ L) :
    boundedFlatPerfect X (CochainComplex.mappingCone f) := by
  obtain ⟨hpK, ⟨b, hb⟩, hfK⟩ := hK
  obtain ⟨hpL, ⟨c, hc⟩, hfL⟩ := hL
  refine ⟨Complex.locallyPerfect_mappingCone hpK hpL f,
    ⟨max (b-1) c, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, ?_⟩
  · intro n hn
    exact (CochainComplex.mappingCone.isZero_X_iff f n).mpr
      ⟨K.isZero_of_isStrictlyLE b (n+1) (by omega), L.isZero_of_isStrictlyLE c n (by omega)⟩
  · intro n
    exact (stalkwiseFlat X).prop_of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) rfl).symm
      (stalkwiseFlat_biprod X (hfK (n+1)) (hfL n))

end Quillen.PerfectComplexes

end

end

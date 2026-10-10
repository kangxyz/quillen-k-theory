/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Fibration.Rows.ReflexiveFactorization
import Quillen.PerfectComplexes.BoundedFlat.Basic
import Quillen.PerfectComplexes.OpenFibration

/-!
# Actual shifts, cones and joint cylinders in the bounded-flat model

The explicit bounds and genuine flat finite-sum property retain shifted and
mapping-cone complexes. The existing exact identity-cone cylinder therefore
supplies the structural JointData required by approximation on this actual
Waldhausen model, without an added cylinder hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CochainComplex Quillen.SchemeSheaf
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

theorem boundedFlatPerfect_shift {X : Scheme.{u}} {K : Complex X}
    (hK : boundedFlatPerfect X K) (n : ℤ) :
    boundedFlatPerfect X ((shiftFunctor (Complex X) n).obj K) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨locallyPerfect_shift hp n,
    ⟨b-n, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, fun i => hf (i+n)⟩
  intro i hi
  change IsZero (K.X (i+n))
  exact K.isZero_of_isStrictlyLE b (i+n) (by omega)

theorem boundedFlatPerfect_mappingCone {X : Scheme.{u}} {K L : Complex X}
    (hK : boundedFlatPerfect X K) (hL : boundedFlatPerfect X L) (f : K ⟶ L) :
    boundedFlatPerfect X (CochainComplex.mappingCone f) := by
  obtain ⟨hpK, ⟨b, hb⟩, hfK⟩ := hK
  obtain ⟨hpL, ⟨c, hc⟩, hfL⟩ := hL
  refine ⟨locallyPerfect_mappingCone hpK hpL f,
    ⟨max (b-1) c, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, ?_⟩
  · intro n hn
    exact (CochainComplex.mappingCone.isZero_X_iff f n).mpr
      ⟨K.isZero_of_isStrictlyLE b (n+1) (by omega), L.isZero_of_isStrictlyLE c n (by omega)⟩
  · intro n
    exact (stalkwiseFlat X).prop_of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) rfl).symm
      (stalkwiseFlat_biprod X (hfK (n+1)) (hfL n))

/-- The genuine exact joint-cylinder data required by approximation is constructed
on the original bounded-flat category, not assumed as an enhancement premise. -/
def boundedFlatPerfectJointData (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFlatPerfectWaldhausen X)) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfect X)
    (fun hK hL f => boundedFlatPerfect_mappingCone hK hL f)
    (fun _ hK => boundedFlatPerfect_shift hK 1) _

end Quillen.PerfectComplexes

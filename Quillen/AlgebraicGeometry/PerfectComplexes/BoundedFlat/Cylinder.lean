/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Rows.ComplexRelativeJoint
public import Quillen.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure

/-!
# Actual shifts, cones and joint cylinders in the bounded-flat model

The explicit bounds and genuine flat finite-sum property retain shifted and
mapping-cone complexes. The existing exact identity-cone cylinder therefore
supplies the structural JointData required by approximation on this actual
Waldhausen model, without an added cylinder hypothesis.
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

/-- The genuine exact joint-cylinder data required by approximation is constructed
on the original bounded-flat category, not assumed as an enhancement premise. -/
def boundedFlatPerfectJointData (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFlatPerfectWaldhausen X)) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfect X)
    (fun hK hL f => boundedFlatPerfect_mappingCone hK hL f)
    (fun _ hK => boundedFlatPerfect_shift hK 1) _

end Quillen.PerfectComplexes

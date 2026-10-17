/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Closure


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

/-- The genuine exact joint-cylinder data required by approximation is constructed
on the original bounded-flat category, not assumed as an enhancement premise. -/
def boundedFlatPerfectJointData (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFlatPerfectWaldhausen X)) :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFlatPerfect X)
    (fun hK hL f => boundedFlatPerfect_mappingCone hK hL f)
    (fun _ hK => boundedFlatPerfect_shift hK 1) _

end Quillen.PerfectComplexes

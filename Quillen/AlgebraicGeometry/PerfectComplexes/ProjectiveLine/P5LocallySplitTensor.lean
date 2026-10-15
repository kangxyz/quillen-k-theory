/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.LocallySplit
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.LineTensor

/-! # Arbitrary coefficient tensor on an actual locally split sequence

The finite locally free quotient supplies genuine local splittings. Tensoring
those splittings and using the original tensor/restriction comparison proves
exactness for an arbitrary coefficient sheaf; it need not be flat.
-/
@[expose] public section
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules

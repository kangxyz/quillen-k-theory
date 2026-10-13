/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.Separation.Basic

/-!
# T1 separation of path spaces

The original compact-open path space in a T1 space is T1, because its continuous
map to the pointwise function space is injective.
-/
@[expose] public section

namespace Quillen

instance pathT1Space {X : Type*} [TopologicalSpace X] [T1Space X] (x y : X) :
    T1Space (Path x y) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

end Quillen

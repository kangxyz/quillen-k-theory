/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Resolution.Theorem

/-!
# Public Quillen finite-resolution theorem

`Quillen.Resolution.KEquiv` and `inclusionKMap_bijective` prove the canonical
all-degree comparison from actual objectwise finite admissible resolutions
and the standard resolving closure conditions. No uniform bound is required.
The exact Q-inclusion is the forward map of the classifying-space homotopy
equivalence. Length-one and uniformly bounded specializations remain available.
-/
@[expose] public section

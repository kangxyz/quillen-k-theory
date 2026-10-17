/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Homotopy.Path

/-!
# Mapping a specified projection rectangle preserves all whole paths and interior times

Intended upstream module: `Aglib.Topology.Path.MappedProjectionRectangle`.

For a continuous map between arbitrary topological spaces, five named boundary paths, and a
homotopy between the specified boundary words, mapping preserves both whole words and every
interior time.

Current coefficient-seed and mixed-route consumers: `CoefficientBassPositiveJ0Rectangles`,
`CoefficientBassPositiveLeftRectangles`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u v
namespace Path.Homotopy
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {a b c d e : X} (f : C(X, Y))
variable (A : Path a b) (B : Path b c) (Q : Path c e) (L : Path a d) (F : Path d e)

/-- Map the exact source and target words of an existing projection rectangle. -/
def mapProjectionRectangle
    (H : (B.trans Q).Homotopy (A.symm.trans (L.trans F))) :
    ((B.map f.continuous).trans (Q.map f.continuous)).Homotopy
      ((A.map f.continuous).symm.trans
        ((L.map f.continuous).trans (F.map f.continuous))) :=
  (H.map f).cast (by simp only [Path.map_trans])
    (by simp only [Path.map_trans, Path.map_symm])

/-- Mapping and renaming the whole boundary words leaves both interior clocks untouched. -/
theorem mapProjectionRectangle_apply
    (H : (B.trans Q).Homotopy (A.symm.trans (L.trans F))) (r s : unitInterval) :
    mapProjectionRectangle f A B Q L F H (r, s) = f (H (r, s)) := rfl

end Path.Homotopy

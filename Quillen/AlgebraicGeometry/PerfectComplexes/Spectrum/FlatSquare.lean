/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit

/-!
# Whole spectrum homotopies of actual flat geometric squares

A literal commuting square of flat scheme maps induces a whole coherent homotopy between
its original contravariant spectrum composites. This uses the existing geometric composition
comparisons. No higher coherence between these tracks is asserted.
-/
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Quillen.PerfectComplexes

/-- The two actual spectrum composites around a flat geometric square are homotopic. -/
def perfectFlatPrespectrumSquareHomotopy {X Y Z W : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (u : X ⟶ W) (q : W ⟶ Z)
    [Flat p] [Flat v] [Flat u] [Flat q] (h : p ≫ v = u ≫ q) :
    LoopPrespectrum.Homotopy
      (perfectFlatPrespectrumMap v ≫ perfectFlatPrespectrumMap p)
      (perfectFlatPrespectrumMap q ≫ perfectFlatPrespectrumMap u) := by
  have H := perfectFlatPrespectrumCompHomotopy u q
  have e : perfectFlatPrespectrumMap (p ≫ v) = perfectFlatPrespectrumMap (u ≫ q) := by
    congr 1
  rw [← e] at H
  exact (perfectFlatPrespectrumCompHomotopy p v).symm.trans H

end Quillen.PerfectComplexes

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.Limits.SequentialExactness
public import Quillen.Topology.Prespectrum.StableHomotopy

/-!
The original stable homomorphisms preserve levelwise positive-degree exact pairs, using actual
sequential abelian colimits. The constant prespectrum map induces the zero stable map; no stable
mapping-cone theorem is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum

/-- Original maps that are levelwise exact on positive homotopy groups induce
an exact pair on the actual integer-graded stable colimits. -/
theorem stableHomotopyMap_exact_of_levelwise {E F G : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G)
    (h : ∀ n k, Function.MulExact
      (piMap k (f.map n) (f.map_point n))
      (piMap k (g.map n) (g.map_point n))) (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map g) := by
  apply sequentialColimit_exact (stableSystemMap f d) (stableSystemMap g d)
  intro n
  exact h ((-d).toNat+n+2) (d.toNat+n+1)

/-- The genuine constant prespectrum map induces the zero stable homomorphism. -/
@[simp] theorem stableHomotopyMap_zero (E F : LoopPrespectrum.{u}) (d : ℤ) :
    (stableHomotopyFunctor d).map (zeroHom E F) = 0 := by
  change colimMap (stableSystemMap (zeroHom E F) d) = 0
  apply colimit.hom_ext
  intro n
  rw [ι_colimMap, comp_zero]
  have hz : (stableSystemMap (zeroHom E F) d).app n = 0 := by
    apply AddCommGrpCat.ext
    intro a
    change Additive.ofMul (piMap (d.toNat+n+1)
      (ContinuousMap.const (E.space ((-d).toNat+n+2)) (F.point ((-d).toNat+n+2)))
      rfl a.toMul) = 0
    rw [piMap_const]
    rfl
  rw [hz, zero_comp]

end Quillen.LoopPrespectrum

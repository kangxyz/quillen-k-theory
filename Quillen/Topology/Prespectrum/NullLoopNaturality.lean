/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! Literal coefficient naturality of original null-conjugated loop maps. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- Naturality of the supplied original loop and null tracks preserves their exact concatenation.
-/
theorem Homotopy.nullLoopMap_naturality {E F E' F' : LoopPrespectrum.{u}}
    {f : E ⟶ F} {f' : E' ⟶ F'} (a : E ⟶ E') (b : F ⟶ F')
    (H : Homotopy f f) (H' : Homotopy f' f')
    (N : Homotopy f (zeroHom E F)) (N' : Homotopy f' (zeroHom E' F'))
    (hH : ∀ n, (H.postcomp b).level n = (H'.precomp a).level n)
    (hN : ∀ n, (N.postcomp b).level n = (N'.precomp a).level n) :
    H.nullLoopMap N ≫ parameterLoopingMap b = a ≫ H'.nullLoopMap N' := by
  have h (n : ℕ) : ((H.conjugateToZero N).postcomp b).level n =
      ((H'.conjugateToZero N').precomp a).level n := by
    simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.precomp_trans,
      Homotopy.postcomp_symm, Homotopy.precomp_symm]
    apply Homotopy.trans_level_congr
    · exact Homotopy.symm_level_congr _ _ n (hN n)
    · exact Homotopy.trans_level_congr _ _ _ _ n (hH n) (hN n)
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  exact DFunLike.congr_fun (h n) (s, x)

end Quillen.LoopPrespectrum

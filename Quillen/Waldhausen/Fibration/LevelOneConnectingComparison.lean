/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.Fibration.SpectrumComparison
public import Quillen.Topology.HomotopyFiber.BasedLESNaturality

/-!
# The original change-of-weak boundary at spectrum level one

The actual small-model homeomorphisms and whole canonical fiber comparison
preserve the original geometric connecting homomorphism at level one.
This does not identify it with the signed stable connecting homomorphism;
that comparison additionally requires the structure-map coordinate sign.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Fibration
open IteratedS LoopPrespectrum
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The actual fiber homeomorphism is the based map of its original strict square. -/
theorem originalFiberToSpectrumLevelOne_mapAt :
    (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun =
      HomotopyFiber.mapAt (p := changeWeakMap N) (q := (changeWeakPrespectrumMap N).map 1)
        V.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
        (smallModelDeloopingHomeomorph_naturality (changeWeak_exact N))
        N.coarse.kBasepoint ((originalPrespectrum N.coarse).point 1)
        N.coarse.smallModelDeloopingHomeomorph_basepoint := by
  ext z
  apply Subtype.ext
  rfl

/-- Both chosen zero points are retained by the original whole-path fiber homeomorphism. -/
theorem originalFiberToSpectrumLevelOne_basepoint :
    originalFiberToSpectrumLevelOne N
        (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
          V.kBasepoint (changeWeakMap_basepoint N)) =
      (homotopyFiber (changeWeakPrespectrumMap N)).point 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact V.smallModelDeloopingHomeomorph_basepoint
  · apply ContinuousMap.ext
    intro t
    exact N.coarse.smallModelDeloopingHomeomorph_basepoint

/-- The original canonical fiber K-map is exactly the specified level-one spectrum comparison. -/
theorem originalFiberToSpectrumLevelOne_canonicalFiberKMap (n : ℕ) :
    (piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
        (originalFiberToSpectrumLevelOne_basepoint N)).comp (canonicalFiberKMap N n) =
      (piMap n ((canonicalFiberPrespectrumMap N).map 1)
        ((canonicalFiberPrespectrumMap N).map_point 1)).comp
          ((acyclicStructure N).smallModelKEquiv n).toMonoidHom := by
  change (piMap n _ _).comp (piMap n _ _) =
    (piMap n _ _).comp (piMap n _ _)
  rw [← homotopyGroupMapHom_comp, ← homotopyGroupMapHom_comp]
  congr 1
  exact canonicalFiberPrespectrumMap_level_one_square N

/-- The original fiber homeomorphism preserves the geometric boundary with its based points. -/
theorem originalFiberToSpectrumLevelOne_connecting (n : ℕ) :
    (piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
        (originalFiberToSpectrumLevelOne_basepoint N)).comp
      (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N) n) =
    (HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n).comp
        (N.coarse.smallModelKEquiv (n + 1)).toMonoidHom := by
  have h := HomotopyFiber.connectingHom_mapAt_natural
    (f := changeWeakMap N) (g := (changeWeakPrespectrumMap N).map 1)
    V.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    N.coarse.smallModelDeloopingHomeomorph.toHomotopyEquiv.toFun
    (smallModelDeloopingHomeomorph_naturality (changeWeak_exact N))
    V.kBasepoint N.coarse.kBasepoint ((originalPrespectrum V).point 1)
    ((originalPrespectrum N.coarse).point 1) (changeWeakMap_basepoint N)
    ((changeWeakPrespectrumMap N).map_point 1)
    V.smallModelDeloopingHomeomorph_basepoint
    N.coarse.smallModelDeloopingHomeomorph_basepoint n
  change (piMap n _ _).comp _ =
    (HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n).comp (piMap (n + 1) _ _)
  simpa only [← originalFiberToSpectrumLevelOne_mapAt] using h

/-- The unchanged original K-boundary agrees with the actual geometric boundary at level one. -/
theorem canonicalFiberPrespectrumMap_levelOne_connecting
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (a : N.coarse.K (n + 1)) :
    piMap n ((canonicalFiberPrespectrumMap N).map 1)
        ((canonicalFiberPrespectrumMap N).map_point 1)
      ((acyclicStructure N).smallModelKEquiv n (changeWeakConnectingHom N h n a)) =
    HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n
      (N.coarse.smallModelKEquiv (n + 1) a) := by
  have hs := DFunLike.congr_fun (originalFiberToSpectrumLevelOne_canonicalFiberKMap N n)
    (changeWeakConnectingHom N h n a)
  simp only [MonoidHom.comp_apply] at hs
  exact hs.symm.trans ((congrArg
    (piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
      (originalFiberToSpectrumLevelOne_basepoint N))
    (canonicalFiberKMap_connecting N h n a)).trans
      (DFunLike.congr_fun (originalFiberToSpectrumLevelOne_connecting N n) a))

end Quillen.Waldhausen.Fibration

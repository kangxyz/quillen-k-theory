/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.PushoutConeFamilyRecovery
public import Quillen.Topology.Prespectrum.HomotopySquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositionCellDescent

/-! Regression for zero-, one-, and two-dimensional original double-quotient families. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.PushoutConeFamily

variable {A B C L Y : Quillen.LoopPrespectrum.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {c : HomotopyPushout.prespectrum f g ⟶ L}

-- Dimension zero retains the actual map, including its cone cylinder inputs.
example (h : mappingCone c ⟶ Y) (t : Fin 0 → unitInterval) (n : ℕ)
    (x : (mappingCone c).space n) :
    ((PushoutConeFamily.ofHomotopy (Quillen.LoopPrespectrum.Homotopy.refl h)).restrict
      (ContinuousMap.const (Fin 0 → unitInterval) 0)).desc n (t, x) = h.map n x :=
  PushoutConeFamily.ofFamily_desc_restrict (Quillen.LoopPrespectrum.Homotopy.refl h).level
    (Quillen.LoopPrespectrum.Homotopy.refl h).at_point
    (Quillen.LoopPrespectrum.Homotopy.refl h).comm _ n t x

/-- The literal first coordinate of a one-dimensional cube. -/
def oneCoordinate : C((Fin 1 → unitInterval), unitInterval) :=
  ⟨fun t ↦ t 0, by fun_prop⟩

-- Dimension one retains both original maps and the entire previously chosen path.
example {l r : mappingCone c ⟶ Y} (H : Homotopy l r) (n : ℕ)
    (t : Fin 1 → unitInterval) (x : (mappingCone c).space n) :
    ((PushoutConeFamily.ofHomotopy H).restrict oneCoordinate).desc n (t, x) =
      H.level n (t 0, x) :=
  PushoutConeFamily.ofFamily_desc_restrict H.level H.at_point H.comm oneCoordinate n t x

example {l r : mappingCone c ⟶ Y} (H : Homotopy l r) (n : ℕ)
    (x : (mappingCone c).space n) :
    ((PushoutConeFamily.ofHomotopy H).restrict oneCoordinate).desc n ((fun _ ↦ 1), x) =
      r.map n x :=
  (PushoutConeFamily.ofFamily_desc_restrict H.level H.at_point H.comm oneCoordinate
    n (fun _ ↦ 1) x).trans (H.at_one n x)

variable {f₀₀ f₀₁ f₁₀ f₁₁ : mappingCone c ⟶ Y}
  {H₀ : Homotopy f₀₀ f₀₁} {H₁ : Homotopy f₁₀ f₁₁}
  {J : Homotopy f₀₀ f₁₀} {K : Homotopy f₀₁ f₁₁}

/-- The exact native cells of a fixed chosen square, with independent finite cube coordinates. -/
def squareCells (S : H₀.Square H₁ J K) :
    PushoutConeFamily (Fin 2 → unitInterval) f g c Y :=
  PushoutConeFamily.ofFamily
    (fun n ↦ ⟨fun z ↦ S.level n (z.1 0, (z.1 1, z.2)), by fun_prop⟩)
    (fun n t ↦ S.at_point n (t 0) (t 1))
    (fun n t x z ↦ S.comm n (t 0) (t 1) x z)

/-- The actual lower face insertion, without identifying the other cube coordinate. -/
def lowerFace : C((Fin 1 → unitInterval), (Fin 2 → unitInterval)) :=
  ⟨fun t ↦ ![0, t 0], by fun_prop⟩

-- The full lower face is exactly the old filler, at every native input.
example (S : H₀.Square H₁ J K) (n : ℕ) (t : Fin 1 → unitInterval)
    (x : (mappingCone c).space n) :
    ((squareCells S).restrict lowerFace).desc n (t, x) = H₀.level n (t 0, x) := by
  exact (PushoutConeFamily.ofFamily_desc_restrict _ _ _ lowerFace n t x).trans
    (S.at_zero n (t 0) x)

-- The same full face survives independent parameter looping, not just its endpoints.
example (S : H₀.Square H₁ J K) (n : ℕ) (t : Fin 1 → unitInterval)
    (x : (parameterLooping (mappingCone c)).space n) (s : unitInterval) :
    Path.toContinuousMap (((squareCells S).restrict lowerFace).looped n (t, x)) s =
      H₀.level n (t 0, Path.toContinuousMap x s) := by
  exact (PushoutConeFamily.ofFamily_desc_restrict _ _ _ lowerFace n t
    (Path.toContinuousMap x s)).trans (S.at_zero n (t 0) (Path.toContinuousMap x s))

end QuillenTest.PushoutConeFamily

#print axioms Quillen.LoopPrespectrum.PushoutConeFamily.desc
#print axioms Quillen.LoopPrespectrum.PushoutConeFamily.desc_restrict
#print axioms Quillen.LoopPrespectrum.PushoutConeFamily.looped_structure
#print axioms Quillen.LoopPrespectrum.PushoutConeFamily.ofFamily_desc
#print axioms Quillen.PerfectComplexes.BassMWhole.compositionCells_looped

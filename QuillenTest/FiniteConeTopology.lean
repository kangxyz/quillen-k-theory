/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.FiniteConeTopology
public import Quillen.Topology.Prespectrum.LoopTranspose

/-! Regression for the unchanged cone action object and actual finite Model levels. -/
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.KTheory.Bass.FiniteConeTopology
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) :
    iterate Q 1 F = ConeTrack.diagram Q F := rfl

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (i : ℕ) (X : C) :
    (iterate Q (i + 1) F).obj X = mappingCone
      (StrictSquare.comparison ((iterate Q i F).mapArrow.mapArrow.obj (Q.obj X))) := rfl

example (F : C ⥤ Model.{w}) (i j : ℕ) (X : C) (m : ℕ) :
    T1Space ((loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) :=
  inferInstance

example (F : C ⥤ Model.{w}) (i : ℕ) (X : C) (m : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((loops i ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).point m))) :=
  modelLoopsIterate_point_homotopyExtensionProperty Q i i F X m

example (F : C ⥤ Model.{w}) (i : ℕ) (X : C) (m : ℕ)
    (hm : i + 2 ≤ m) (k : ℕ) (hk : k + i < m)
    (x : (loops i ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) :
    Subsingleton (HomotopyGroup.Pi k
      ((loops i ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)).space m) x) := by
  have h := modelLoopsIterate_homotopyGroup_subsingleton Q i i F X
    (m - (i + 2)) k (by omega)
  rw [show m - (i + 2) + i + 2 = m by omega] at h
  exact h x

example (F : C ⥤ Model.{w}) (i : ℕ) (X : C) (n k : ℕ) (hk : k < n + 2)
    (x : ((iterate Q i (F ⋙ prespectrumFunctor)).obj X).space (n + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((iterate Q i (F ⋙ prespectrumFunctor)).obj X).space (n + 2)) x) :=
  modelLoopsIterate_homotopyGroup_subsingleton Q i 0 F X n k hk x

#print axioms iterate_point_homotopyExtensionProperty
#print axioms iterate_homotopyGroup_subsingleton
#print axioms loops_homotopyGroup_subsingleton
#print axioms modelLoopsIterate_point_homotopyExtensionProperty
#print axioms modelLoopsIterate_homotopyGroup_subsingleton

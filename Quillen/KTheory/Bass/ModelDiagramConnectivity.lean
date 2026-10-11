/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramVanishing
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Genuine finite connectivity and points of every original model-diagram Bass stage

The original iterated-S point topology and all-point vanishing propagate through every actual
Bass iterate for any index category and actual square functor. The precise range is k+i<m above
cutoffi+2, at every original point. No stage topology or future-growth premise is required.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w})

/-- Every original model-diagram Bass stage is T1 at each actual level. -/
instance modelDiagramIterateSpaceT1Space (X : C) (m : ℕ) :
    T1Space ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :=
  @strictDiagramIterateSpaceT1Space _ _ Q i (F ⋙ prespectrumFunctor)
    (fun Y n ↦ prespectrumSpaceT1Space (F.obj Y) n) X m

/-- The literal chosen points remain well-based at every level and every actual iterate. -/
theorem modelDiagramIterate_point_homotopyExtensionProperty (X : C) (m : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point m))) := by
  let : ∀ Y n, T1Space (((F ⋙ prespectrumFunctor).obj Y).space n) :=
    fun Y n ↦ prespectrumSpaceT1Space (F.obj Y) n
  exact strictDiagramIterate_point_homotopyExtensionProperty Q i (F ⋙ prespectrumFunctor)
    (fun Y n ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) n) X m

/-- All original points satisfy the actual one-degree-per-iterate vanishing range. -/
theorem modelDiagramIterate_homotopyGroup_subsingleton_at (X : C)
    (n k : ℕ) (hk : k < n + 2)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (n + i + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (n + i + 2)) x) := by
  let : ∀ Y m, T1Space (((F ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (F.obj Y) m
  have h := strictDiagramIterate_homotopyGroup_subsingleton Q i (F ⋙ prespectrumFunctor)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) m) 0
    (fun Y m t ht y ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (m + 1) t (by omega) y) X n k hk
  rw [Nat.zero_add] at h
  exact h x

/-- The same genuine vanishing bound expressed at an arbitrary level above the exact cutoff. -/
theorem modelDiagramIterate_homotopyGroup_subsingleton_of_le (X : C) (m : ℕ)
    (hm : i + 2 ≤ m) (k : ℕ) (hk : k + i < m)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) :
    Subsingleton (HomotopyGroup.Pi k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space m) x) := by
  have h := modelDiagramIterate_homotopyGroup_subsingleton_at Q i F X
    (m - (i + 2)) k (by omega)
  rw [show m - (i + 2) + i + 2 = m by omega] at h
  exact h x

end Quillen.KTheory.Bass

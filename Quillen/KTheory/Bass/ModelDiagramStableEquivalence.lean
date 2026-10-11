/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.StrictDiagramStableEquivalence
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence

/-!
# Bass preservation for original iterated-S model diagrams

Any actual strict model diagrams on the same index category supply their original S-prespectra.
The proved original S-model topology and all-point growth discharge every initial hypothesis
of finite Bass preservation for an arbitrary actual square functor. The resulting arrow is the
unchanged iterate of the supplied original natural transformation. A categorical exact-equivalence
specialization proves its stability directly from the actual original forward model maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Original model diagrams need no additional topology or growth inputs for Bass preservation. -/
theorem modelDiagramIterate_map_isStableEquivalence (i : ℕ) (F G : C ⥤ Model.{w})
    (η : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor)
    (hη : ∀ X, IsStableEquivalence (η.app X)) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map η).app X) := by
  let : ∀ Y m, T1Space (((F ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (F.obj Y) m
  let : ∀ Y m, T1Space (((G ⋙ prespectrumFunctor).obj Y).space m) :=
    fun Y m ↦ prespectrumSpaceT1Space (G.obj Y) m
  exact strictDiagramIterate_map_isStableEquivalence_of_linearGrowth Q i
    (F ⋙ prespectrumFunctor) (G ⋙ prespectrumFunctor)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (F.obj Y) m)
    (fun Y m ↦ prespectrum_point_homotopyExtensionProperty (G.obj Y) m) 0 0
    (fun Y n k hk x ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (F.obj Y) (n + 1) k (by omega) x)
    (fun Y n k hk x ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (G.obj Y) (n + 1) k (by omega) x) η hη X

/-- Exact categorical equivalences preserve the actual model-map Bass iterates, with no stable
premise and with the original forward functors retained literally. -/
theorem modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence
    (i : ℕ) (F G : C ⥤ Model.{w}) (η : F ⟶ G)
    (e : ∀ X, F.obj X ≌ G.obj X)
    (he : ∀ X, (e X).functor = (η.app X).functor)
    (hinv : ∀ X, IsExact (G.obj X).waldhausen.cof (G.obj X).waldhausen.weq
      (F.obj X).waldhausen.cof (F.obj X).waldhausen.weq (e X).inverse) (X : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map
      (Functor.whiskerRight η prespectrumFunctor)).app X) := by
  apply modelDiagramIterate_map_isStableEquivalence Q i F G
    (Functor.whiskerRight η prespectrumFunctor) _ X
  intro Y
  have hF : IsExact (F.obj Y).waldhausen.cof (F.obj Y).waldhausen.weq
      (G.obj Y).waldhausen.cof (G.obj Y).waldhausen.weq (e Y).functor := by
    rw [he Y]
    exact (η.app Y).exact
  have h0 : (e Y).functor.obj (F.obj Y).waldhausen.zero = (G.obj Y).waldhausen.zero := by
    rw [he Y]
    exact (η.app Y).zero
  have hf : ExactModelEquivalence.forward (e Y) hF h0 = η.app Y :=
    Model.Hom.ext (he Y)
  have hs := ExactModelEquivalence.isStableEquivalence (e Y) hF (hinv Y) h0
  rw [hf] at hs
  exact hs

end Quillen.KTheory.Bass

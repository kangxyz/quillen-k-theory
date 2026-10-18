/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SectionChangeIndexModel
public import Quillen.KTheory.Bass.ModelDiagramStableEquivalence

/-!
# Finite Bass stability of actual section restriction

The original forward restriction is retained. Only exactness of the categorical inverse is
used; no strictly chosen-zero-preserving inverse Model map is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.LoopPrespectrum
open CategoryTheory.SectionChangeIndex
universe u
namespace Quillen.Waldhausen.IteratedS.SectionChangeIndex
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{u, u})
    (W : ∀ d, Waldhausen.Structure (F.obj ⟨d⟩))
    (Z : ∀ d, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))
    (K : C ⥤ D)
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor)

/-- Every finite Bass iterate of actual restriction is a stable equivalence. -/
theorem restrictionModel_iterate_isStableEquivalence
    (Q : C ⥤ Arrow (Arrow C)) (i : ℕ) (c : C) :
    IsStableEquivalence (((strictDiagramIterate Q i).map
      (Functor.whiskerRight (restrictionModel F W Z hZ hmap K hExact)
        prespectrumFunctor)).app c) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence
    Q i _ _ (restrictionModel F W Z hZ hmap K hExact)
    (fun c => (underFunctor F K c).asEquivalence) (fun _ => rfl)
  exact fun c => restriction_inverse_exact F W Z hZ hmap K c

end Quillen.Waldhausen.IteratedS.SectionChangeIndex

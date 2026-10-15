/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveTelescopeComponents
public import Quillen.Topology.LocalCoefficients.HomotopyCorrection

/-!
# Abelian monodromy correction at the actual projective telescope translation

The component-reflection condition in finite track descent is discharged by the
proved projective-complement argument. The conclusion retains the specified two
homotopies and their actual coefficient maps on any given homology class.
-/

@[expose] public section

open Quillen.LocalCoefficients

noncomputable section
open CategoryTheory
universe u
namespace Quillen.FiniteProjectiveModule
open LocalCoefficients
variable (R : Type u) [Ring R]

/-- Two tracks ending at the original projective translation admit the required
abelian coefficient correction on each actual local homology class. -/
theorem projectiveTelescopeTranslation_homology_track_correction (P : IsoCategory Rᵐᵒᵖ)
    {f : C(ClassifyingSpace (ProjectiveTelescope R), ClassifyingSpace (ProjectiveTelescope R))}
    (H K : f.Homotopy (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom)
    {A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R))}
    (hA : AbelianMonodromy A) (n : ℕ) (x : homology (pullback f A) n) :
    ∃ T : A ≅ A,
      coefficientHomologyMap
          (pullbackMap (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom T.hom) n
        (coefficientHomologyMap (homotopyPullbackIso H A).hom n x) =
      coefficientHomologyMap (homotopyPullbackIso K A).hom n x := by
  obtain ⟨s, hs⟩ := homology_finite_homotopy_correction H K hA n x
  exact hs (fun a _ b _ h ↦ (projectiveTelescopeTranslation_joined_iff R P a b).mp h)

end Quillen.FiniteProjectiveModule

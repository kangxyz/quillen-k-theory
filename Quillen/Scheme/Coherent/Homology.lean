/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Quillen.Scheme.Coherent.Localization.GluingLocality

/-!
# Local coherence and actual coherent homology

On locally noetherian schemes, actual coherence is local on arbitrary open
neighborhoods and is preserved by actual homology of termwise coherent
complexes. No quasi-compactness or boundedness is needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace Quillen.CoherentScheme

/-- Coherence is local on actual open neighborhoods of a locally noetherian scheme. -/
theorem coherent_of_openNeighborhoods {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      coherent U.toScheme (M.restrict U.ι)) : coherent X M := by
  classical
  choose U hU hc using hM
  have hfp (x : X) : (M.restrict (U x).ι).IsFinitePresentation := by
    let : IsLocallyNoetherian (U x).toScheme := isLocallyNoetherian_of_isOpenImmersion (U x).ι
    exact coherent_finitePresentation (hc x)
  have : M.IsFinitePresentation := finitePresentation_of_openCover M U (by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hU x⟩) hfp
  exact coherent_of_finitePresentation M

/-- Actual homology of a termwise coherent complex is coherent. -/
theorem coherent_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : CochainComplex X.Modules ℤ) (hK : ∀ n, coherent X (K.X n)) (i : ℤ) :
    coherent X (K.homology i) := by
  let S := K.sc i
  have hk := (coherent X).prop_kernel S.g (hK _) (hK _)
  have hc := (coherent X).prop_cokernel (kernel.lift S.g S.f S.zero) (hK _) hk
  exact (coherent X).prop_of_iso S.homologyIsoCokernelLift.symm hc

end Quillen.CoherentScheme

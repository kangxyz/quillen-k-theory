/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.SmallComparison
public import Quillen.Resolution.Theorem

/-!
# The canonical scheme comparison from actual finite resolutions

This is the general geometric adapter to the proved unbounded Quillen
resolution theorem. Its input consists of actual finite conflation towers,
with no common bound. Discharging these towers from arbitrary-dimensional
regularity remains a separate commutative-algebra/geometric theorem.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf
variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- Objectwise actual finite resolutions pass to the chosen small model;
no uniform bound is introduced. -/
theorem coherentSmallResolutionHypothesis
    (h : (CoherentScheme.coherentExactStructure X).ResolutionHypothesis
      (coherentVectorBundle X)) :
    (CoherentScheme.coherentExactStructure X).smallModel.ResolutionHypothesis
      (coherentSmallVectorBundle X) := by
  intro M
  let E := equivSmallModel.{u+1} (CoherentScheme.FiniteTypeSheaves X)
  obtain ⟨T⟩ := h (E.inverse.obj M)
  let T' := (CoherentScheme.coherentExactStructure X).originalToSmallModel.mapFiniteResolution
    (P' := coherentSmallVectorBundle X)
    (fun N hN => (coherentVectorBundle X).prop_of_iso (E.unitIso.app N) hN) T
  exact ⟨T'.ofIso (E.counitIso.app M)⟩

/-- The original canonical scheme K-to-G map is bijective when coherent
sheaves admit genuine finite vector-bundle resolutions. This theorem uses
the proved Quillen theorem rather than accepting it as an input field. -/
theorem schemeKToG_bijective_of_finite_resolutions
    [(CoherentScheme.coherentExactStructure X).IsKernelClosed (coherentVectorBundle X)]
    (h : (CoherentScheme.coherentExactStructure X).ResolutionHypothesis
      (coherentVectorBundle X)) (n : ℕ) :
    Function.Bijective (schemeKToG X n) := by
  have h₁ := (vectorBundleSmallLiftExact X).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := Resolution.inclusionKMap_bijective
    (CoherentScheme.coherentExactStructure X).smallModel (coherentSmallVectorBundle X)
    (coherentSmallResolutionHypothesis X h) n
  change Function.Bijective ((vectorBundleToCoherentExact X).smallModel.KMap n)
  rw [← vectorBundleSmall_factor X, ExactFunctor.KMap_comp]
  exact h₂.comp h₁

/-- Objectwise Ext-defined finite projective dimension produces the actual
affine finite-vector-bundle-resolution hypothesis. This is a homological
intermediate statement, not a substituted regularity assumption. -/
theorem coherentResolutionHypothesis_of_finite_projectiveDimension
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (h : ∀ M : CoherentScheme.FiniteModule.{u, u} R,
      projectiveDimension M.obj ≠ ⊤) :
    (CoherentScheme.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) := by
  intro M
  let N := (CoherentScheme.finiteTypeSheavesSpecModuleEquivalence R).functor.obj M
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff N.obj).mp (h N)
  have := hn
  obtain ⟨T, _⟩ := coherentResolution_length_le_of_projectiveDimensionLE R n M
  exact ⟨T⟩

end Quillen.SchemeSheaf

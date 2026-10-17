/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.SmallModel

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.FiniteProjectiveDimension

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
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

open AlgebraicGeometry.Scheme.Modules


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules
variable (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]

/-- The original canonical scheme K-to-G map is bijective when coherent
sheaves admit genuine finite vector-bundle resolutions. This theorem uses
the proved Quillen theorem rather than accepting it as an input field. -/
theorem schemeKToG_bijective_of_finite_resolutions
    [(AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).IsKernelClosed
      (coherentVectorBundle X)]
    (h : (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionHypothesis
      (coherentVectorBundle X)) (n : ℕ) :
    Function.Bijective (schemeKToG X n) := by
  have h₁ := (vectorBundleSmallLiftExact X).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := Resolution.inclusionKMap_bijective
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).smallModel
      (coherentSmallVectorBundle X)
    (coherentSmallResolutionHypothesis X h) n
  change Function.Bijective ((vectorBundleToCoherentExact X).smallModel.KMap n)
  rw [← vectorBundleSmall_factor X, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  exact h₂.comp h₁

end AlgebraicGeometry.Scheme.Modules

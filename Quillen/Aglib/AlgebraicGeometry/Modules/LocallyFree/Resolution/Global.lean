/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.ChartBounds
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality

/-!
# Actual global resolutions on regular schemes with the resolution property

The resolution property produces a genuine vector-bundle quotient of each
successive coherent syzygy. On every affine chart, that quotient has a
projective middle module, so projective dimension drops by one. At bound
zero, projectivity on the charts detects finite local freeness globally.
Quasi-compactness and regularity provide an objectwise bound by a finite
affine cover. Vector bundles are never asserted globally projective.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]

/-- Zero chart-module projective dimension means the original coherent
sheaf is an actual finite locally free sheaf. -/
theorem coherentVectorBundle_of_affineCoverDimensionLE_zero
    (U : X.AffineOpenCover.{v}) (M :
      AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X)
    (hM : AffineCoverDimensionLE U M 0) : coherentVectorBundle X M := by
  apply finiteLocallyFree_of_schemeOpenCover M.obj U.openCover
  intro i
  apply (coherentChartModule_projective_iff (U.X i) (U.f i) M).mp
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr (hM i)

/-- The ordinary resolution property and a bound on actual affine chart
modules construct an actual finite coherent conflation tower of that bound.
The syzygies are genuine coherent kernels, and every resolving term is a
finite locally free sheaf on the original scheme. -/
theorem coherentResolution_length_le_of_affineCoverDimensionLE
    [Scheme.HasResolutionProperty X] (U : X.AffineOpenCover.{v}) (n : ℕ)
    (M : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) (hM :
      AffineCoverDimensionLE U M n) :
    ∃ T : (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).FiniteResolution
        (coherentVectorBundle X) M, T.length ≤ n := by
  induction n generalizing M with
  | zero =>
    exact ⟨.of_mem (coherentVectorBundle_of_affineCoverDimensionLE_zero U M hM), le_rfl⟩
  | succ n ih =>
    obtain ⟨K, P, i, p, w, hP, hS⟩ := Scheme.exists_vectorBundle_shortExact X M
    have hK : AffineCoverDimensionLE U K n := by
      intro a
      have := hM a
      exact coherentChartModule_syzygy (U.X a) (U.f a) (ShortComplex.mk i p w) hS hP n
    obtain ⟨T, hT⟩ := ih K hK
    exact ⟨.step (ShortComplex.mk i p w) hS hP T, Nat.succ_le_succ hT⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Every coherent sheaf on a quasi-compact regular scheme with the ordinary
resolution property admits an actual finite global vector-bundle resolution.
The bound may depend on the sheaf, even if the scheme has infinite dimension. -/
theorem coherentResolutionHypothesis_of_regular_resolutionProperty
    [Scheme.IsRegular X] [CompactSpace X] [Scheme.HasResolutionProperty X] :
    (AlgebraicGeometry.Scheme.Modules.Coherent.coherentExactStructure X).ResolutionHypothesis
      (coherentVectorBundle X) := by
  intro M
  obtain ⟨n, hn⟩ := exists_finiteCoverDimensionLE_of_regular M
  obtain ⟨T, _⟩ := coherentResolution_length_le_of_affineCoverDimensionLE
    (Scheme.finiteAffineOpenCover X) n M hn
  exact ⟨T⟩

end AlgebraicGeometry.Scheme.Modules

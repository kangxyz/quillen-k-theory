/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatComparison
public import Quillen.Waldhausen.SConstruction.Iterated.VertexHEP

/-! Consumers retain every original positive inclusion level, its actual path-component coverage,
and extension of arbitrary specified homotopies at the unchanged chosen S-vertex. -/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u v
namespace Quillen.Tests.StableOmegaDetection

/-- Every target component is hit by the literal positive-level inclusion. -/
theorem boundedFlatInclusion_component_surjective (X : Scheme.{u}) [CompactSpace X] (n : ℕ)
    (y : (originalPrespectrum (perfectWaldhausen X)).space (n + 1)) :
    ∃ x, Joined ((exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X)
      (perfectWaldhausen X) (boundedFlatPerfectInclusion_exact X)).map (n + 1) x) y :=
  (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence X n).component_surjective y

/-- A specified homotopy at the actual S-vertex extends on its unchanged positive level. -/
theorem originalPositivePoint_extendsHomotopy
    {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C) (n : ℕ)
    (Z : TopCat.{max u v}) (p : C((originalPrespectrum W).space (n + 1), Z))
    (H : C(unitInterval × PUnit.{max u v + 1}, Z))
    (hzero : ∀ a, H (0, a) = p ((originalPrespectrum W).point (n + 1))) :
    ∃ K : C(unitInterval × (originalPrespectrum W).space (n + 1), Z),
      (∀ x, K (0, x) = p x) ∧
      ∀ t a, K (t, (originalPrespectrum W).point (n + 1)) = H (t, a) :=
  homotopyExtensionProperty_continuous
    (originalPrespectrum_positivePoint_homotopyExtensionProperty W n) Z p H hzero

end Quillen.Tests.StableOmegaDetection

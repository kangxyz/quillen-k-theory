/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.CoherentHomology

/-! # Actual coherent homology consumers for locally perfect complexes -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.Tests.PerfectCoherentHomology
open PerfectComplexes

/-- No compactness or termwise coherence hypothesis appears in each degree. -/
theorem actual_homology_coherent {X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] (K : Perfect X) (i : ℤ) :
    CoherentScheme.affineLocallyFiniteType X (K.obj.homology i) :=
  locallyPerfect_coherent_homology K.property i

/-- A quasi-compact noetherian base gives bounded coherent cohomology, not
bounded original terms. -/
theorem actual_homology_bounded {X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X] (K : Perfect X) :
    (∀ i, CoherentScheme.affineLocallyFiniteType X (K.obj.homology i)) ∧
      ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (K.obj.homology i) :=
  locallyPerfect_bounded_coherent_homology K.property

/-- The actual complex homology map is retained on underlying sheaves. -/
theorem original_homology_map {X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] (i : ℤ) {K L : Perfect X} (f : K ⟶ L) :
    ((coherentHomology X i).map f).hom = HomologicalComplex.homologyMap f.hom i := rfl

/-- Arbitrary original quasi-isomorphisms induce coherent isomorphisms. -/
theorem quasiIso_homology_isIso {X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] (i : ℤ) {K L : Perfect X} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso ((coherentHomology X i).map f) := coherentHomology_map_isIso i f

/-- The natural comparison is between the existing two restriction functors. -/
theorem original_open_naturality {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (i : ℤ) {K L : Perfect X} (f : K ⟶ L) :
    (perfectRestrict j ⋙ coherentHomology U i).map f ≫
      (coherentHomologyRestrictIso j i).hom.app L =
    (coherentHomologyRestrictIso j i).hom.app K ≫
      (coherentHomology X i ⋙ CoherentScheme.finiteTypeSheavesRestriction j).map f :=
  (coherentHomologyRestrictIso j i).hom.naturality f

end Quillen.Tests.PerfectCoherentHomology

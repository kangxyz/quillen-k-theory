/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.StalkFlat
public import Quillen.AlgebraicGeometry.PerfectComplexes.Strict

/-! # Actual vector-bundle flat-stalk consumers

The statements retain arbitrary schemes, actual stalk rings, arbitrary
geometric pullback and the original strict-perfect complex terms.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
namespace QuillenTest.VectorBundleStalkFlat

open Quillen

/-- Vector bundles have flat actual module stalks on an arbitrary scheme. -/
theorem original_stalk (X : Scheme.{u}) (M : X.Modules)
    [IsFiniteLocallyFree X M] (x : X) :
    Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj M) :=
  stalkwiseFlat_of_finiteLocallyFree M x

/-- No flatness of the scheme map is needed for flat vector-bundle pullback. -/
theorem arbitrary_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [IsFiniteLocallyFree Y M] : stalkwiseFlat X ((Scheme.Modules.pullback f).obj M) :=
  stalkwiseFlat_pullback f (stalkwiseFlat_of_finiteLocallyFree M)

/-- The local criterion imposes no finite generation condition on the tested sheaf. -/
theorem arbitrary_sheaf_locality (X : Scheme.{u}) (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      stalkwiseFlat U.toScheme (M.restrict U.ι)) : stalkwiseFlat X M :=
  stalkwiseFlat_of_locally_restrict M h

/-- Empty open restrictions are included. -/
theorem empty_open (X : Scheme.{u}) (M : X.Modules) (h : stalkwiseFlat X M) :
    stalkwiseFlat (⊥ : X.Opens).toScheme (M.restrict (⊥ : X.Opens).ι) :=
  stalkwiseFlat_restrict _ h

/-- The original strict-perfect terms meet the actual flat-replacement comparison hypotheses. -/
theorem strict_perfect_terms (X : Scheme.{u})
    (K : AlgebraicGeometry.Scheme.Modules.Complex.StrictPerfect X) :
    ∀ n, stalkwiseFlat X (K.obj.X n) := by
  intro n
  let := K.property.2 n
  exact stalkwiseFlat_of_finiteLocallyFree _

end QuillenTest.VectorBundleStalkFlat

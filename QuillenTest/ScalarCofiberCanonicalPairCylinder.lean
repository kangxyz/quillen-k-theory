/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberCanonicalPairCylinder

/-! # Whole original canonical pair-cylinder consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Additivity Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.ExtensionCategory MonoidalCategory
open scoped Topology Simplicial
universe u
namespace QuillenTest.ScalarCofiberCanonicalPairCylinder
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => perfectWaldhausen X
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)

/-- The original quotient-first pair retains its literal right identity component. -/
theorem original_pair_component (K L : Perfect X) :
    (perfectOpenScalarCanonicalPairTransformation j r q hq).app (K, L) =
      ((perfectOpenScalarRebasedZeroToCone j r q hq).app K,
        𝟙 ((Quillen.rebaseFunctor (𝟭 (Perfect X)) (V).zero (W).zero
          (((hF).zero (V).isZero).iso (W).isZero)).obj L)) :=
  perfectOpenScalarCanonicalPairTransformation_app j r q hq K L

/-- The complete simplicial first projection is the old canonical zero cylinder. -/
theorem original_whole_first_cylinder :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫ sSetMap (fst_exact W W) =
      sSetMap (fst_exact V V) ▷ Δ[1] ≫
        (perfectOpenScalarCanonicalLeftHomotopy j r q hq).h :=
  perfectOpenScalarCanonicalPairHomotopy_fst j r q hq

/-- The complete simplicial second projection is the unchanged identity cylinder. -/
theorem original_whole_second_cylinder :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫ sSetMap (snd_exact W W) =
      CartesianMonoidalCategory.fst
        (sSet (productStructure V V).cof (productStructure V V).weq) Δ[1] ≫
          sSetMap ((snd_exact V V).comp (hF).rebase) :=
  perfectOpenScalarCanonicalPairHomotopy_snd j r q hq

/-- The original first component retains every independent realization time and input. -/
theorem original_first_time (t : unitInterval) (x : (productStructure V V).Delooping) :
    deloopingMap (fst_exact W W) (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarCanonicalLeftHomotopy j r q hq)
        (t, deloopingMap (fst_exact V V) x) :=
  perfectOpenScalarCanonicalPairRealization_fst j r q hq t x

/-- The right component retains the same whole input while its identity time is constant. -/
theorem original_second_time (t : unitInterval) (x : (productStructure V V).Delooping) :
    deloopingMap (snd_exact W W) (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      deloopingMap ((snd_exact V V).comp (hF).rebase) x :=
  perfectOpenScalarCanonicalPairRealization_snd j r q hq t x

/-- The original product comparison sees exactly the full left track and fixed right input. -/
theorem original_product_projection (t : unitInterval)
    (x : (productStructure V V).Delooping) :
    Product.deloopingComparison W W
        (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      (realizationSimplicialHomotopy (perfectOpenScalarCanonicalLeftHomotopy j r q hq)
        (t, deloopingMap (fst_exact V V) x),
        deloopingMap (hF).rebase (deloopingMap (snd_exact V V) x)) :=
  perfectOpenScalarCanonicalPairRealization_projection j r q hq t x

/-- Every original cylinder time fixes the chosen product zero. -/
theorem original_full_zero (t : unitInterval) :
    perfectOpenScalarCanonicalPairRealization j r q hq
        (t, (productStructure V V).kBasepoint) = (productStructure W W).kBasepoint :=
  perfectOpenScalarCanonicalPairRealization_zero j r q hq t

/-- The entire spatial boundary remains fixed, including a single spatial coordinate. -/
theorem original_degree_zero_boundary (t : unitInterval)
    (p : GenLoop (Fin 1) (productStructure V V).Delooping (productStructure V V).kBasepoint)
    (z : Fin 1 → unitInterval) (hz : z ∈ Cube.boundary (Fin 1)) :
    perfectOpenScalarCanonicalPairRealization j r q hq (t, p z) =
      (productStructure W W).kBasepoint := by
  exact (congrArg (fun x : (productStructure V V).Delooping ↦
    perfectOpenScalarCanonicalPairRealization j r q hq (t, x))
    (p.property z hz)).trans (perfectOpenScalarCanonicalPairRealization_zero j r q hq t)

end QuillenTest.ScalarCofiberCanonicalPairCylinder

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalDescent

/-! # Actual geometric cover detection consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u w
namespace Quillen.Tests.PerfectLocalDescent
open PerfectComplexes

/-- Two actual local models glue their perfection, with no global strict model supplied. -/
theorem binary_models_perfect {X : Scheme.{u}} {K : Complex X} (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (P : Perfect U.toScheme) (Q : Perfect V.toScheme)
    (eP : (toDerived U.toScheme).obj ((restrict U.ι).obj K) ≅ (toDerived U.toScheme).obj P.obj)
    (eQ : (toDerived V.toScheme).obj ((restrict V.ι).obj K) ≅ (toDerived V.toScheme).obj Q.obj) :
    locallyPerfect X K :=
  locallyPerfect_of_binaryOpenCover U V hUV
    ((locallyPerfect_iff_of_derivedIso eP).mpr P.property)
    ((locallyPerfect_iff_of_derivedIso eQ).mpr Q.property)

/-- Vanishing restrictions make every original sheaf map with this target zero. -/
theorem actual_sheaf_map_zero {X : Scheme.{u}} {ι : Type w} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (M N : X.Modules)
    (hN : ∀ i, IsZero ((Scheme.Modules.restrictFunctor (U i).ι).obj N)) (f : M ⟶ N) : f = 0 :=
  (SchemeSheaf.isZero_of_openCover N U hU hN).eq_of_tgt _ _

/-- Local acyclicity forces actual global homology to vanish in every degree. -/
theorem actual_homology_zero {X : Scheme.{u}} {ι : Type w} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (K : Complex X)
    (hK : ∀ i, ((restrict (U i).ι).obj K).Acyclic) (n : ℤ) : IsZero (K.homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (acyclic_of_openCover K U hU hK n)

/-- The actual global original localization map is invertible after local quasi-isomorphism tests.
  -/
theorem original_derived_map_iso {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    {ι : Type w} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hf : ∀ i, QuasiIso ((restrict (U i).ι).map f)) : IsIso ((toDerived X).map f) := by
  let := quasiIso_of_openCover f U hU hf
  infer_instance
end Quillen.Tests.PerfectLocalDescent

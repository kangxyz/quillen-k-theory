/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.Strictification
public import Mathlib.Data.ZMod.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives
/-!
# Affine strictification regression statements

Records homology and principal-open comparisons for strict-perfect representatives,
including the zero principal open over `ZMod 6`. Further statements express
finite-free attachment as surjectivity on module elements and obtain a chain
quasi-isomorphism from a strict-perfect module complex.
-/

@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.Affine
attribute [local instance] Quillen.PerfectComplexes.Affine.standardDerivedModules
  Quillen.PerfectComplexes.Affine.standardDerivedSheaves
namespace QuillenTest.AffineStrictification

open Quillen

/-- The strict model retains every actual homology object of an arbitrary
locally-perfect ambient sheaf complex. -/
theorem actual_strict_model_homology (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (hK : locallyPerfect (Spec R) K) :
    ∃ P : StrictPerfect (Spec R),
      Nonempty ((DerivedCategory.Q (C := (Spec R).Modules)).obj P.obj ≅
        (DerivedCategory.Q (C := (Spec R).Modules)).obj K) ∧
      ∀ i, Nonempty (P.obj.homology i ≅ K.homology i) := by
  obtain ⟨P, ⟨e⟩⟩ := locallyPerfect_exists_strictPerfect_representative R hK
  refine ⟨P, ⟨e⟩, fun i => ⟨?_⟩⟩
  exact ((DerivedCategory.homologyFunctorFactors (Spec R).Modules i).app P.obj).symm ≪≫
    (DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (Spec R).Modules i).app K

/-- The global model compares under the original geometric restriction,
including restrictions to empty principal opens. -/
theorem actual_restricted_strict_model (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ) (hK : locallyPerfect (Spec R) K) (r : R) :
    ∃ P : StrictPerfect (Spec R),
      Nonempty ((DerivedCategory.Q).obj ((restrict
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj P.obj)
        ≅
        (DerivedCategory.Q).obj
          ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
          r)).obj K)) := by
  obtain ⟨P, ⟨e⟩⟩ := locallyPerfect_exists_strictPerfect_representative R hK
  exact ⟨P, ⟨restrictDerivedIso _ e⟩⟩

/-- A zero-divisor base is permitted, with literal restriction to the empty
principal open defined by zero. -/
theorem actual_zmod_six_empty_restriction
    (K : CochainComplex (Spec (CommRingCat.of (ZMod 6))).Modules ℤ)
    (hK : locallyPerfect _ K) :
    ∃ P : StrictPerfect (Spec (CommRingCat.of (ZMod 6))),
      Nonempty ((DerivedCategory.Q).obj ((restrict
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
        (CommRingCat.of (ZMod 6)) 0)).obj P.obj) ≅
        (DerivedCategory.Q).obj
          ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
          (CommRingCat.of (ZMod 6)) 0)).obj K)) :=
  actual_restricted_strict_model _ K hK 0

/-- The finite-free attachment uses the actual homology map of a genuine
chain map; the claimed epimorphism is surjective on original module elements. -/
theorem actual_finiteFree_attachment_surjective (R : CommRingCat.{u})
    (K : ModuleComplex R) (n : ℤ) [K.IsLE n] [Module.Finite R (K.homology n)] :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K),
      Function.Surjective (homologyMap f n) ∧ (CochainComplex.mappingCone f).IsLE (n-1) := by
  obtain ⟨m, f, hf, hc⟩ := Quillen.ModuleComplex.exists_finiteFree_single_lowering_top K n
  exact ⟨m, f, (ModuleCat.epi_iff_surjective _).mp hf, hc⟩

/-- Actual principal local models give a genuine global chain comparison for
module complexes because the constructed source is proved K-projective. -/
theorem actual_module_chain_model (R : CommRingCat.{u})
    (K : ModuleComplex R) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : locallyPerfect (Spec R) ((associatedComplex R).obj K)) :
    ∃ (P : ModuleComplex R) (f : P ⟶ K), moduleStrictPerfect R P ∧ QuasiIso f := by
  obtain ⟨P, hP, ⟨e⟩⟩ := finiteProjectiveDerived_of_locallyPerfect_associated R K a b hK
  have := isKProjective_of_moduleStrictPerfect R hP
  obtain ⟨f, hf⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective e.hom
  have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
  exact ⟨P, f, hP, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) f).mp inferInstance⟩

end QuillenTest.AffineStrictification

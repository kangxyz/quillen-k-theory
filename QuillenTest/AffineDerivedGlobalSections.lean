/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedGlobalSections
public import QuillenTest.AffineCechSections

/-!
# Consumers of actual derived global sections and open free generators

These tests retain the original right-derived functor and injective-resolution
complex over the zero-divisor ring `ZMod 6`. The quasicoherent result is degree
one; arbitrary flasque coefficients give all positive degrees. On arbitrary
schemes, the actual free-generator morphisms represent restriction, injectives
lift restricted sections even from the empty open, and short exact sequences
with flasque kernel lift sections without conditions on the other terms.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Quillen.SchemeSheaf Quillen.SchemeSheaf.AffineDerived
open QuillenTest.AffineCechSections

namespace QuillenTest.AffineDerivedGlobalSections

open Quillen

lemma torsion_ring_quasicoherent_first_derived
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent] :
    IsZero ((moduleSpecΓFunctor.rightDerived 1).obj M) :=
  isZero_rightDerived_globalSections_one M

lemma torsion_ring_flasque_all_positive_derived
    (M : (Spec torsionRing).Modules) [TopCat.Presheaf.IsFlasque M.presheaf] (n : ℕ) :
    IsZero ((moduleSpecΓFunctor.rightDerived (n + 1)).obj M) :=
  isZero_rightDerived_globalSections_succ_of_flasque M n

lemma torsion_ring_original_resolution_exact_one
    (M : (Spec torsionRing).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) :
    ((moduleSpecΓFunctor.mapHomologicalComplex _).obj I.cocomplex).ExactAt 1 :=
  globalSections_injectiveResolution_exact_one M I

lemma actual_open_restriction_represented (X : Scheme.{u}) {U V : X.Opens}
    (h : U ⟶ V) (M : X.Modules) (p : openFree X V ⟶ M) :
    openFreeHomEquiv X U M ((openFreeFunctor X).map h ≫ p) =
      M.presheaf.map h.op (openFreeHomEquiv X V M p) :=
  openFreeHomEquiv_naturality_open X h M p

lemma injective_empty_open_section_extends (X : Scheme.{u})
    (M : X.Modules) [Injective M] (s : Γ(M, ⊥)) :
    ∃ t : Γ(M, ⊤), M.presheaf.map (homOfLE (show (⊥ : X.Opens) ≤ ⊤ from bot_le)).op t = s :=
  injective_sections_restrict_surjective X M _ s

lemma flasque_kernel_original_section_lift {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [TopCat.Presheaf.IsFlasque S.X₁.presheaf] (U : X.Opens) (s : Γ(S.X₃, U)) :
    ∃ t : Γ(S.X₂, U), S.g.app U t = s :=
  sections_surjective_of_flasque_kernel hS U s

lemma original_injective_resolution_kernel_flasque {X : Scheme.{u}}
    (M : X.Modules) [TopCat.Presheaf.IsFlasque M.presheaf]
    (I : CategoryTheory.InjectiveResolution M) (n : ℕ) :
    TopCat.Presheaf.IsFlasque (kernel (I.cocomplex.d (n + 1) (n + 2))).presheaf :=
  injectiveResolution_kernel_isFlasque M I n

end QuillenTest.AffineDerivedGlobalSections

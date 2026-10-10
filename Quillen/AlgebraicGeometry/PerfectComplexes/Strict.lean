/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.ComplexSubcategory
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Exact
public import Mathlib.Algebra.Homology.Single

/-!
# Strict perfect complexes on an actual scheme

A strict perfect complex is a globally bounded cochain complex of finite
locally free module sheaves. Its Waldhausen cofibrations are degreewise
short exact sequences with strict-perfect quotient, and its weak equivalences
are actual quasi-isomorphisms of sheaf complexes. Extension closure is
proved from the already-established local vector-bundle splitting theorem.

Strict-perfect K-theory is not identified with all-perfect K-theory here.
That comparison requires geometric resolution hypotheses and a theorem.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Actual cochain complexes of module sheaves on the scheme. -/
abbrev Complex (X : Scheme.{u}) := CochainComplex X.Modules ℤ

/-- Strict boundedness concerns the terms, not merely the cohomology. -/
def IsBounded {X : Scheme.{u}} (K : Complex X) : Prop :=
  ∃ (a b : ℤ), ∀ (n : ℤ), n < a ∨ b < n → IsZero (K.X n)

/-- Globally bounded complexes of finite locally free sheaves. -/
def strictPerfect (X : Scheme.{u}) : ObjectProperty (Complex X) := fun K ↦
  IsBounded K ∧ ∀ n : ℤ, SchemeSheaf.IsFiniteLocallyFree X (K.X n)

/-- The full category of strict perfect complexes. -/
abbrev StrictPerfect (X : Scheme.{u}) := (strictPerfect X).FullSubcategory

variable {X : Scheme.{u}}

/-- Every zero complex is strict perfect. -/
theorem strictPerfect_of_isZero {K : Complex X} (hK : IsZero K) : strictPerfect X K := by
  have h (n : ℤ) : IsZero (K.X n) :=
    (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨⟨0, 0, fun n _ ↦ h n⟩, fun n ↦ SchemeSheaf.finiteLocallyFree_of_isZero (h n)⟩

instance strictPerfect_containsZero : (strictPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, strictPerfect_of_isZero (isZero_zero _)⟩

/-- Strict perfectness is invariant under actual chain isomorphism. -/
theorem strictPerfect_of_iso {K L : Complex X} (e : K ≅ L)
    (hK : strictPerfect X K) : strictPerfect X L := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  let en (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e
  refine ⟨⟨a, b, fun n hn ↦ (hb n hn).of_iso (en n).symm⟩, ?_⟩
  intro n
  exact (SchemeSheaf.finiteLocallyFree_iff_of_iso (en n)).1 (hv n)

instance strictPerfect_closedUnderIsomorphisms : (strictPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hK := strictPerfect_of_iso e hK

/-- A short exact extension of strict perfect complexes is strict perfect. -/
theorem strictPerfect_of_shortExact {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) (h₁ : strictPerfect X S.X₁) (h₃ : strictPerfect X S.X₃) :
    strictPerfect X S.X₂ := by
  obtain ⟨⟨a, b, hb₁⟩, hv₁⟩ := h₁
  obtain ⟨⟨c, d, hb₃⟩, hv₃⟩ := h₃
  have hs (n : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  constructor
  · refine ⟨min a c, max b d, fun n hn ↦ ?_⟩
    have h₁ : IsZero (S.X₁.X n) := hb₁ n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_left _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_left _ _) h)))
    have h₃ : IsZero (S.X₃.X n) := hb₃ n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_right _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_right _ _) h)))
    exact (hs n).exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  · intro n
    exact @SchemeSheaf.finiteLocallyFree_of_shortExact X _ (hs n) (hv₁ n) (hv₃ n)

instance strictPerfect_extensionClosed :
    (abelianExactStructure (Complex X)).IsExtensionClosed (strictPerfect X) where
  prop_middle := strictPerfect_of_shortExact

instance strictPerfect_closedUnderFiniteProducts :
    (strictPerfect X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (strictPerfect X)

/-- The genuine quasi-isomorphism Waldhausen structure on strict perfect
complexes, with all axioms derived from the preceding closure proofs. -/
def strictWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (StrictPerfect X) :=
  Waldhausen.complexSubcategory (strictPerfect X)

/-- Connective S-construction K-groups of strict perfect complexes.
These are not defined using the ordinary Q-category of complexes. -/
abbrev StrictK (X : Scheme.{u}) (n : ℕ) := (strictWaldhausen X).K n

/-- A vector bundle, placed in degree zero, is a strict perfect complex. -/
theorem single_strictPerfect (M : X.Modules) [SchemeSheaf.IsFiniteLocallyFree X M] :
    strictPerfect X ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) := by
  constructor
  · refine ⟨0, 0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa only [HomologicalComplex.single_obj_X_self] using
        (inferInstance : SchemeSheaf.IsFiniteLocallyFree X M)
    · exact SchemeSheaf.finiteLocallyFree_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The canonical degree-zero inclusion of vector bundles into strict perfect
complexes. A comparison on K-theory still requires its comparison theorem. -/
def vectorBundleInclusion (X : Scheme.{u}) : SchemeSheaf.FiniteLocallyFree X ⥤ StrictPerfect X :=
  (strictPerfect X).lift
    ((SchemeSheaf.finiteLocallyFree X).ι ⋙
      HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)
    (fun M ↦ single_strictPerfect M.obj)

end Quillen.PerfectComplexes

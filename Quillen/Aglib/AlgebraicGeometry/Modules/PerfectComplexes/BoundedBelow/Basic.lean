/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.Algebra.Homology.Embedding.CochainComplex.TruncGE
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Homology
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Lower-bounded locally perfect complexes

Objects retain their actual sheaf complexes with an explicit existential lower term bound. Zero, isomorphism, extension, finite-product and shift closure and the literal inclusion are unchanged.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory

open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.BoundedBelow

/-- The actual original locally perfect complexes with lower-bounded terms. -/
def objects (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  locallyPerfect X K ∧ ∃ a : ℤ, K.IsStrictlyGE a

/-- The full subcategory of locally perfect complexes whose terms vanish below some degree. -/
abbrev Obj (X : Scheme.{u}) := (objects X).FullSubcategory

variable {X : Scheme.{u}}

lemma objects_of_isZero {K : CochainComplex X.Modules ℤ} (hK : IsZero K) : objects X K := by
  refine ⟨locallyPerfect_of_strictPerfect (strictPerfect_of_isZero hK), 0, ?_⟩
  exact (CochainComplex.isStrictlyGE_iff _ _).mpr
    (fun n _ => (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK)

instance containsZero : (objects X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, objects_of_isZero (isZero_zero _)⟩

lemma objects_of_iso {K L : CochainComplex X.Modules ℤ} (e : K ≅ L) (hK : objects X K) :
    objects X L := by
  obtain ⟨hp, a, ha⟩ := hK
  let := ha
  exact ⟨locallyPerfect_of_iso e hp, a, CochainComplex.isStrictlyGE_of_iso e a⟩

instance closedUnderIsomorphisms : (objects X).IsClosedUnderIsomorphisms where
  of_iso e hK := objects_of_iso e hK

lemma objects_of_shortExact {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : objects X S.X₁) (h₃ : objects X S.X₃) : objects X S.X₂ := by
  obtain ⟨hp₁, a, ha⟩ := h₁
  obtain ⟨hp₃, b, hb⟩ := h₃
  let := ha
  let := hb
  refine ⟨locallyPerfect_of_shortExact hS hp₁ hp₃, min a b,
    (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
  intro n hn
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  exact hs.exact.isZero_X₂
    ((S.X₁.isZero_of_isStrictlyGE a n (by omega)).eq_of_src _ _)
    ((S.X₃.isZero_of_isStrictlyGE b n (by omega)).eq_of_tgt _ _)

instance extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed (objects X) where
  prop_middle := objects_of_shortExact

instance closedUnderFiniteProducts : (objects X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts (objects X)

lemma objects_shift {K : CochainComplex X.Modules ℤ} (hK : objects X K) (n : ℤ) : objects X
    (K⟦n⟧) := by
  obtain ⟨hp, a, ha⟩ := hK
  let := ha
  refine ⟨locallyPerfect_shift hp n, a - n,
    (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
  intro i hi
  change IsZero (K.X (i + n))
  exact K.isZero_of_isStrictlyGE a (i + n) (by omega)

/-- The inclusion that forgets the lower bound on the terms of a locally perfect complex. -/
def inclusion (X : Scheme.{u}) : Obj X ⥤ Perfect X :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

end Quillen.PerfectComplexes.BoundedBelow

end

end

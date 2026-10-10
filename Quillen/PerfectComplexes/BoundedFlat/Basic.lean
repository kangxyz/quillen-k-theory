/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Scheme.Sheaf.FlatExtensions
import Quillen.Scheme.Sheaf.FlatCochainResolution
import Quillen.PerfectComplexes.KTheory
import Quillen.Algebra.Homology.BoundedAboveComplex

/-!
# The actual bounded-flat locally-perfect Waldhausen model

Objects retain their original sheaf complexes and chain maps, with explicit
termwise upper bound, stalkwise-flat terms and the original local-perfect
predicate. Actual extension closure gives ambient quotient cofibrations and
original quasi-isomorphisms. The honest inclusion into Perfect is exact;
no equivalence with that larger category is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open Quillen.SchemeSheaf Quillen.CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Actual bounded-above, degreewise stalkwise-flat, locally perfect complexes. -/
def boundedFlatPerfect (X : Scheme.{u}) : ObjectProperty (Complex X) := fun K =>
  locallyPerfect X K ∧ boundedAbove X.Modules K ∧ ∀ n, stalkwiseFlat X (K.X n)

abbrev BoundedFlatPerfect (X : Scheme.{u}) := (boundedFlatPerfect X).FullSubcategory

variable {X : Scheme.{u}}

theorem boundedFlatPerfect_of_isZero {K : Complex X} (hK : IsZero K) :
    boundedFlatPerfect X K := by
  have hz (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨locallyPerfect_of_strictPerfect (strictPerfect_of_isZero hK),
    ⟨0, (CochainComplex.isStrictlyLE_iff _ _).mpr (fun n _ => hz n)⟩,
    fun n => stalkwiseFlat_of_isZero _ (hz n)⟩

instance boundedFlatPerfect_containsZero : (boundedFlatPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedFlatPerfect_of_isZero (isZero_zero _)⟩

theorem boundedFlatPerfect_of_iso {K L : Complex X} (e : K ≅ L)
    (hK : boundedFlatPerfect X K) : boundedFlatPerfect X L := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  let en (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e
  refine ⟨locallyPerfect_of_iso e hp, ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, ?_⟩
  · intro n hn
    exact (K.isZero_of_isStrictlyLE b n hn).of_iso (en n).symm
  · intro n
    exact (stalkwiseFlat X).prop_of_iso (en n) (hf n)

instance boundedFlatPerfect_closedUnderIsomorphisms :
    (boundedFlatPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hK := boundedFlatPerfect_of_iso e hK

theorem boundedFlatPerfect_of_shortExact {S : ShortComplex (Complex X)}
    (hS : S.ShortExact) (h₁ : boundedFlatPerfect X S.X₁)
    (h₃ : boundedFlatPerfect X S.X₃) : boundedFlatPerfect X S.X₂ := by
  obtain ⟨hp₁, ⟨b, hb⟩, hf₁⟩ := h₁
  obtain ⟨hp₃, ⟨c, hc⟩, hf₃⟩ := h₃
  have hs (n : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  refine ⟨locallyPerfect_of_shortExact hS hp₁ hp₃,
    ⟨max b c, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩, ?_⟩
  · intro n hn
    have h₁ := S.X₁.isZero_of_isStrictlyLE b n (by omega)
    have h₃ := S.X₃.isZero_of_isStrictlyLE c n (by omega)
    exact (hs n).exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  · intro n
    exact stalkwiseFlat_middle_of_shortExact (hs n) (hf₁ n) (hf₃ n)

instance boundedFlatPerfect_extensionClosed :
    (abelianExactStructure (Complex X)).IsExtensionClosed (boundedFlatPerfect X) where
  prop_middle := boundedFlatPerfect_of_shortExact

instance boundedFlatPerfect_closedUnderFiniteProducts :
    (boundedFlatPerfect X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (Complex X)).extensionClosed_finiteProducts (boundedFlatPerfect X)

/-- Actual Waldhausen structure, with ambient admissible monomorphisms and original quasi-isomorphisms. -/
def boundedFlatPerfectWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (BoundedFlatPerfect X) :=
  Waldhausen.complexSubcategory (boundedFlatPerfect X)

/-- The honest inclusion into the original locally-perfect model. -/
def boundedFlatPerfectInclusion (X : Scheme.{u}) : BoundedFlatPerfect X ⥤ Perfect X :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

theorem boundedFlatPerfectInclusion_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (boundedFlatPerfectInclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

end Quillen.PerfectComplexes

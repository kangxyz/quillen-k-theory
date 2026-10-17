/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.Flat.Extensions
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.Resolution
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.Basic

/-!
# Bounded-above flat locally perfect complexes

The original local-perfect predicate, an explicit upper term bound and stalkwise-flat terms define
the full chain category. Actual closure and the literal inclusion into perfect complexes are
preserved.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Actual bounded-above, degreewise stalkwise-flat, locally perfect complexes. -/
def boundedFlatPerfect (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  locallyPerfect X K ∧ _root_.CochainComplex.boundedAbove X.Modules K ∧ ∀ n, stalkwiseFlat X (K.X n)

/-- The full category of locally perfect complexes on `X` that are bounded above in their terms and
have stalkwise-flat terms. -/
abbrev BoundedFlatPerfect (X : Scheme.{u}) := (boundedFlatPerfect X).FullSubcategory

variable {X : Scheme.{u}}

theorem boundedFlatPerfect_of_isZero {K : CochainComplex X.Modules ℤ} (hK : IsZero K) :
    boundedFlatPerfect X K := by
  have hz (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨locallyPerfect_of_strictPerfect (strictPerfect_of_isZero hK),
    ⟨0, (CochainComplex.isStrictlyLE_iff _ _).mpr (fun n _ => hz n)⟩,
    fun n => stalkwiseFlat_of_isZero _ (hz n)⟩

instance boundedFlatPerfect_containsZero : (boundedFlatPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedFlatPerfect_of_isZero (isZero_zero _)⟩

theorem boundedFlatPerfect_of_iso {K L : CochainComplex X.Modules ℤ} (e : K ≅ L)
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

theorem boundedFlatPerfect_of_shortExact {S : ShortComplex (CochainComplex X.Modules ℤ)}
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
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (boundedFlatPerfect X) where
  prop_middle := boundedFlatPerfect_of_shortExact

instance boundedFlatPerfect_closedUnderFiniteProducts :
    (boundedFlatPerfect X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (boundedFlatPerfect X)

/-- The honest inclusion into the original locally-perfect model. -/
def boundedFlatPerfectInclusion (X : Scheme.{u}) : BoundedFlatPerfect X ⥤ Perfect X :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

end Quillen.PerfectComplexes

end

end

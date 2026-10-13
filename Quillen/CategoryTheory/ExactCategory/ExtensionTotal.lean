/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.ExactCategory.Basic
public import Quillen.CategoryTheory.Subdivision
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# The actual total extension category

Grayson's total category is modeled by subdivision of admissible inflations.
Thus morphisms shrink the kernel and enlarge the middle object. This stage
constructs the category and its middle-object projection; the quotient-object
projection to the original Q category requires a separate construction.
-/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [Limits.HasFiniteBiproducts C] (E : ExactStructure C)

instance inflation_isMultiplicative : E.inflation.IsMultiplicative where

/-- The original objects and their admissible monomorphisms. -/
abbrev InflationCategory := WideSubcategory E.inflation

/-- The total extension category, in Grayson's subdivision model. -/
abbrev ExtensionTotal := Quillen.Subdivision E.InflationCategory

/-- An original admissible monomorphism as a total extension object. -/
def extensionTotalOf {A B : C} (i : A ⟶ B) (hi : E.inflation i) : E.ExtensionTotal :=
  Quillen.Subdivision.of (A := (⟨A⟩ : E.InflationCategory))
    (B := (⟨B⟩ : E.InflationCategory)) ⟨i, hi⟩

/-- Retain the actual middle object of an extension. -/
def extensionTotalMiddle : E.ExtensionTotal ⥤ C :=
  Quillen.Subdivision.codomain ⋙ wideSubcategoryInclusion E.inflation

/-- A genuine quotient presentation for a total extension object. -/
structure ExtensionQuotientData (x : E.ExtensionTotal) where
  /-- The quotient object. -/
  obj : C
  /-- The quotient map from the middle object. -/
  π : x.base.obj ⟶ obj
  /-- The kernel inclusion is annihilated. -/
  zero : x.fiber.unop.hom.hom ≫ π = 0
  /-- The quotient belongs to the original exact structure. -/
  conflation : E.conflation (ShortComplex.mk x.fiber.unop.hom.hom π zero)

/-- Recover the quotient from the actual inflation axiom, without extra exactness data. -/
def extensionQuotientData (x : E.ExtensionTotal) : E.ExtensionQuotientData x := by
  apply Classical.choice
  obtain ⟨Q, p, h, hc⟩ := x.fiber.unop.hom.property
  exact ⟨⟨Q, p, h, hc⟩⟩

/-- Recovered quotient presentations have the categorical cokernel universal property. -/
def ExtensionQuotientData.isColimit {x : E.ExtensionTotal}
    (q : E.ExtensionQuotientData x) : IsColimit (CokernelCofork.ofπ q.π q.zero) :=
  E.cokernel _ q.conflation

/-- Quotient choices are canonically isomorphic by their actual universal properties. -/
def ExtensionQuotientData.iso {x : E.ExtensionTotal}
    (q r : E.ExtensionQuotientData x) : q.obj ≅ r.obj :=
  (q.isColimit E).coconePointUniqueUpToIso (r.isColimit E)

/-- The canonical quotient isomorphism preserves the quotient map. -/
@[reassoc (attr := simp)]
theorem ExtensionQuotientData.π_iso_hom {x : E.ExtensionTotal}
    (q r : E.ExtensionQuotientData x) : q.π ≫ (q.iso E r).hom = r.π :=
  (q.isColimit E).comp_coconePointUniqueUpToIso_hom (r.isColimit E) WalkingParallelPair.one

end Quillen.ExactStructure

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.Isomorphisms
public import Quillen.CategoryTheory.ExactCategory.BaseChange
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# s-filtering subcategories and weak isomorphisms

The predicates below spell out the right and left conditions in Schlichting,
*Delooping the K-theory of exact categories*, Definitions 1.3 and 1.5. They refer
to the chosen exact structure, not to arbitrary categorical monos or epis.
Repleteness and extension closure are separate hypotheses on the full subcategory.
Weak isomorphisms are exactly the multiplicative closure of inflations with
cokernel in the subcategory and deflations with kernel in it (Definition 1.12).
Neither a calculus of fractions nor exactness of the quotient is assumed here.
-/
@[expose] public section


universe v u v' u'

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C) (A : ObjectProperty C)

/-- Closure under admissible subobjects for the specified exact structure. -/
def IsClosedUnderAdmissibleSubobjects : Prop :=
  ∀ ⦃X Y : C⦄ (i : X ⟶ Y), E.inflation i → A Y → A X

/-- Closure under admissible quotients for the specified exact structure. -/
def IsClosedUnderAdmissibleQuotients : Prop :=
  ∀ ⦃X Y : C⦄ (p : X ⟶ Y), E.deflation p → A X → A Y

/-- Both admissible subobject closure and admissible quotient closure. -/
structure IsClosedUnderAdmissibleSubquotients : Prop where
  subobjects : E.IsClosedUnderAdmissibleSubobjects A
  quotients : E.IsClosedUnderAdmissibleQuotients A

/-- Every map to an object of `A` factors through an admissible quotient in `A`. -/
def RightFiltering : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), A Y →
    ∃ (B : C) (_ : A B) (p : X ⟶ B) (g : B ⟶ Y), E.deflation p ∧ p ≫ g = f

/-- The dual filtering condition: maps out of `A` factor through admissible
subobjects that belong to `A`. -/
def LeftFiltering : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), A X →
    ∃ (B : C) (_ : A B) (g : X ⟶ B) (i : B ⟶ Y), E.inflation i ∧ g ≫ i = f

/-- An inflation from `A` can be followed by a deflation to `A` so that the
composite is still an inflation. -/
def RightSpecial : Prop :=
  ∀ ⦃X Y : C⦄ (i : X ⟶ Y), A X → E.inflation i →
    ∃ (B : C) (_ : A B) (p : Y ⟶ B), E.deflation p ∧ E.inflation (i ≫ p)

/-- The dual special condition. -/
def LeftSpecial : Prop :=
  ∀ ⦃X Y : C⦄ (p : X ⟶ Y), A Y → E.deflation p →
    ∃ (B : C) (_ : A B) (i : B ⟶ X), E.inflation i ∧ E.deflation (i ≫ p)

/-- The right s-filtering conditions for a full exact subcategory. Extension
closure and repleteness can be supplied independently of this predicate. -/
structure RightSFiltering : Prop where
  subquotients : E.IsClosedUnderAdmissibleSubquotients A
  filtering : E.RightFiltering A
  special : E.RightSpecial A

/-- The left s-filtering conditions, dual to `RightSFiltering`. -/
structure LeftSFiltering : Prop where
  subquotients : E.IsClosedUnderAdmissibleSubquotients A
  filtering : E.LeftFiltering A
  special : E.LeftSpecial A

/-- Admissible subquotient closure applied to one actual conflation. -/
lemma IsClosedUnderAdmissibleSubquotients.of_conflation
    (hA : E.IsClosedUnderAdmissibleSubquotients A) {S : ShortComplex C}
    (hS : E.conflation S) (h₂ : A S.X₂) : A S.X₁ ∧ A S.X₃ :=
  ⟨hA.subobjects S.f (E.inflation_of_conflation hS) h₂,
    hA.quotients S.g (E.deflation_of_conflation hS) h₂⟩

/-- An inflation whose actual conflation has cokernel in `A`. -/
def inflationWithCokernel : MorphismProperty C :=
  fun _ Y i => ∃ (Z : C) (p : Y ⟶ Z) (h : i ≫ p = 0),
    E.conflation (ShortComplex.mk i p h) ∧ A Z

/-- A deflation whose actual conflation has kernel in `A`. -/
def deflationWithKernel : MorphismProperty C :=
  fun X _ p => ∃ (Z : C) (i : Z ⟶ X) (h : i ≫ p = 0),
    E.conflation (ShortComplex.mk i p h) ∧ A Z

/-- The elementary weak isomorphisms in the exact quotient construction. -/
def weakIsomorphismGenerator : MorphismProperty C :=
  E.inflationWithCokernel A ⊔ E.deflationWithKernel A

/-- Finite composites (including empty composites) of the two elementary
classes. This does not assume saturation or a two-out-of-three property. -/
def weakIsomorphisms : MorphismProperty C :=
  (E.weakIsomorphismGenerator A).multiplicativeClosure

instance : (E.weakIsomorphisms A).IsMultiplicative := by
  unfold weakIsomorphisms
  infer_instance

lemma inflationWithCokernel_le_inflation : E.inflationWithCokernel A ≤ E.inflation := by
  rintro X Y i ⟨Z, p, h, hc, _⟩
  exact ⟨Z, p, h, hc⟩

lemma deflationWithKernel_le_deflation : E.deflationWithKernel A ≤ E.deflation := by
  rintro X Y p ⟨Z, i, h, hc, _⟩
  exact ⟨Z, i, h, hc⟩

lemma inflationWithCokernel_of_conflation {S : ShortComplex C}
    (hS : E.conflation S) (hA : A S.X₃) : E.inflationWithCokernel A S.f :=
  ⟨S.X₃, S.g, S.zero, hS, hA⟩

lemma deflationWithKernel_of_conflation {S : ShortComplex C}
    (hS : E.conflation S) (hA : A S.X₁) : E.deflationWithKernel A S.g :=
  ⟨S.X₁, S.f, S.zero, hS, hA⟩

lemma inflationWithCokernel_le_weakIsomorphisms :
    E.inflationWithCokernel A ≤ E.weakIsomorphisms A := by
  intro X Y f hf
  exact .of f (Or.inl hf)

lemma deflationWithKernel_le_weakIsomorphisms :
    E.deflationWithKernel A ≤ E.weakIsomorphisms A := by
  intro X Y f hf
  exact .of f (Or.inr hf)

lemma weakIsomorphisms_id (X : C) : E.weakIsomorphisms A (𝟙 X) :=
  MorphismProperty.id_mem _ X

lemma weakIsomorphisms_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : E.weakIsomorphisms A f) (hg : E.weakIsomorphisms A g) :
    E.weakIsomorphisms A (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ hf hg

/-- A practical induction principle: it suffices to check identities, the two
conflation generators, and composition. -/
lemma weakIsomorphisms_le_iff (W : MorphismProperty C) [W.IsMultiplicative] :
    E.weakIsomorphisms A ≤ W ↔
      E.inflationWithCokernel A ≤ W ∧ E.deflationWithKernel A ≤ W := by
  change (E.weakIsomorphismGenerator A).multiplicativeClosure ≤ W ↔ _
  rw [MorphismProperty.multiplicativeClosure_le_iff]
  exact sup_le_iff

/-- Enlarging the exact subcategory enlarges its weak isomorphisms. -/
lemma weakIsomorphisms_mono {B : ObjectProperty C} (hAB : A ≤ B) :
    E.weakIsomorphisms A ≤ E.weakIsomorphisms B := by
  refine (E.weakIsomorphisms_le_iff A (E.weakIsomorphisms B)).2 ?_
  constructor
  · rintro X Y i ⟨Z, p, h, hc, hZ⟩
    exact E.inflationWithCokernel_le_weakIsomorphisms B i ⟨Z, p, h, hc, hAB _ hZ⟩
  · rintro X Y p ⟨Z, i, h, hc, hZ⟩
    exact E.deflationWithKernel_le_weakIsomorphisms B p ⟨Z, i, h, hc, hAB _ hZ⟩

/-- Inverting the generating inflations and deflations suffices to invert every
weak isomorphism. No fraction-calculus hypothesis is needed. -/
lemma weakIsomorphisms_isInvertedBy_iff {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    (E.weakIsomorphisms A).IsInvertedBy F ↔
      (E.inflationWithCokernel A).IsInvertedBy F ∧
      (E.deflationWithKernel A).IsInvertedBy F := by
  change E.weakIsomorphisms A ≤ (MorphismProperty.isomorphisms D).inverseImage F ↔ _
  exact E.weakIsomorphisms_le_iff A _

/-- Right filtering gives a weak inflation annihilating every map to `A`.
This is the elementary cancellation step needed in a right fraction calculus. -/
lemma RightFiltering.exists_weakInflation_comp_eq_zero (hA : E.RightFiltering A)
    {X Y : C} (f : X ⟶ Y) (hY : A Y) :
    ∃ (K : C) (i : K ⟶ X), E.inflationWithCokernel A i ∧ i ≫ f = 0 := by
  obtain ⟨B, hB, p, g, hp, hpg⟩ := hA f hY
  obtain ⟨K, i, hi, hc⟩ := hp
  refine ⟨K, i, ⟨B, p, hi, hc, hB⟩, ?_⟩
  rw [← hpg, ← Category.assoc, hi, zero_comp]

/-- Left filtering gives the dual elementary cancellation step. -/
lemma LeftFiltering.exists_comp_weakDeflation_eq_zero (hA : E.LeftFiltering A)
    {X Y : C} (f : X ⟶ Y) (hX : A X) :
    ∃ (K : C) (p : Y ⟶ K), E.deflationWithKernel A p ∧ f ≫ p = 0 := by
  obtain ⟨B, hB, g, i, hi, hgi⟩ := hA f hX
  obtain ⟨K, p, hp, hc⟩ := hi
  refine ⟨K, p, ⟨B, i, hp, hc, hB⟩, ?_⟩
  rw [← hgi, Category.assoc, hp, comp_zero]

/-- The right Ore square for a generating inflation follows just from right
filtering: pull back its cokernel map and take a suitable admissible kernel. -/
lemma RightFiltering.rightOre_inflation (hA : E.RightFiltering A)
    {X Y Z : C} (i : X ⟶ Y) (hi : E.inflationWithCokernel A i) (f : Z ⟶ Y) :
    ∃ (T : C) (s : T ⟶ Z) (g : T ⟶ X),
      E.inflationWithCokernel A s ∧ s ≫ f = g ≫ i := by
  obtain ⟨B, p, hip, hc, hB⟩ := hi
  obtain ⟨T, s, hs, hz⟩ := hA.exists_weakInflation_comp_eq_zero E A (f ≫ p) hB
  let hk := E.kernel (ShortComplex.mk i p hip) hc
  let g := hk.lift (KernelFork.ofι (s ≫ f) (by simpa only [Category.assoc] using hz))
  refine ⟨T, s, g, hs, ?_⟩
  symm
  exact hk.fac (KernelFork.ofι (s ≫ f) (by simpa only [Category.assoc] using hz))
    WalkingParallelPair.zero

/-- The dual Ore square for a generating deflation follows from left filtering. -/
lemma LeftFiltering.leftOre_deflation (hA : E.LeftFiltering A)
    {X Y Z : C} (p : X ⟶ Y) (hp : E.deflationWithKernel A p) (f : X ⟶ Z) :
    ∃ (T : C) (s : Z ⟶ T) (g : Y ⟶ T),
      E.deflationWithKernel A s ∧ f ≫ s = p ≫ g := by
  obtain ⟨B, i, hip, hc, hB⟩ := hp
  obtain ⟨T, s, hs, hz⟩ := hA.exists_comp_weakDeflation_eq_zero E A (i ≫ f) hB
  let hk := E.cokernel (ShortComplex.mk i p hip) hc
  let g := hk.desc (CokernelCofork.ofπ (f ≫ s) (by simpa only [Category.assoc] using hz))
  refine ⟨T, s, g, hs, ?_⟩
  symm
  exact hk.fac (CokernelCofork.ofπ (f ≫ s) (by simpa only [Category.assoc] using hz))
    WalkingParallelPair.one

/-- Pullback gives the right Ore square for a generating deflation. -/
lemma rightOre_deflation {X Y Z : C} (p : X ⟶ Y)
    (hp : E.deflationWithKernel A p) (f : Z ⟶ Y) :
    ∃ (T : C) (s : T ⟶ Z) (g : T ⟶ X),
      E.deflationWithKernel A s ∧ s ≫ f = g ≫ p := by
  obtain ⟨B, i, hip, hc, hB⟩ := hp
  let S := ShortComplex.mk i p hip
  let : HasPullback p f := E.deflation.hasPullback f (E.deflation_of_conflation hc)
  refine ⟨pullback p f, pullback.snd p f, pullback.fst p f, ?_,
    (pullback.condition (f := p) (g := f)).symm⟩
  exact E.deflationWithKernel_of_conflation A (E.pullbackConflation_mem hc f) hB

/-- A right filtering subcategory gives an Ore square for each elementary
weak isomorphism. -/
lemma RightFiltering.rightOre_generator (hA : E.RightFiltering A)
    {X Y Z : C} (s : X ⟶ Y) (hs : E.weakIsomorphismGenerator A s) (f : Z ⟶ Y) :
    ∃ (T : C) (t : T ⟶ Z) (g : T ⟶ X),
      E.weakIsomorphisms A t ∧ t ≫ f = g ≫ s := by
  rcases hs with hi | hp
  · obtain ⟨T, t, g, ht, h⟩ := hA.rightOre_inflation E A s hi f
    exact ⟨T, t, g, E.inflationWithCokernel_le_weakIsomorphisms A t ht, h⟩
  · obtain ⟨T, t, g, ht, h⟩ := E.rightOre_deflation A s hp f
    exact ⟨T, t, g, E.deflationWithKernel_le_weakIsomorphisms A t ht, h⟩

/-- The right Ore condition extends from generators to all finite composites. -/
lemma RightFiltering.rightOre (hA : E.RightFiltering A)
    {X Y : C} {s : X ⟶ Y} (hs : E.weakIsomorphisms A s) :
    ∀ {Z : C} (f : Z ⟶ Y), ∃ (T : C) (t : T ⟶ Z) (g : T ⟶ X),
      E.weakIsomorphisms A t ∧ t ≫ f = g ≫ s := by
  induction hs with
  | of s hs => exact fun f => hA.rightOre_generator E A s hs f
  | id X =>
    intro Z f
    exact ⟨Z, 𝟙 Z, f, E.weakIsomorphisms_id A Z, by simp⟩
  | @comp_of X Y Z s r hs hr ih =>
    intro V f
    obtain ⟨T, t, g, ht, htg⟩ := hA.rightOre_generator E A r hr f
    obtain ⟨T', t', g', ht', htg'⟩ := ih g
    refine ⟨T', t' ≫ t, g', E.weakIsomorphisms_comp A ht' ht, ?_⟩
    calc
      (t' ≫ t) ≫ f = t' ≫ (t ≫ f) := Category.assoc _ _ _
      _ = t' ≫ (g ≫ r) := by rw [htg]
      _ = (t' ≫ g) ≫ r := (Category.assoc _ _ _).symm
      _ = (g' ≫ s) ≫ r := by rw [htg']
      _ = g' ≫ (s ≫ r) := Category.assoc _ _ _

/-- Generator cancellation follows by factoring a difference through the
kernel in `A`, then using the filtering axiom to annihilate that factor. -/
lemma RightFiltering.cancel_generator (hA : E.RightFiltering A)
    {X Y Z : C} (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Z)
    (hs : E.weakIsomorphismGenerator A s) (h : f₁ ≫ s = f₂ ≫ s) :
    ∃ (T : C) (t : T ⟶ X), E.weakIsomorphisms A t ∧ t ≫ f₁ = t ≫ f₂ := by
  rcases hs with hi | hp
  · let := E.mono_of_inflation (E.inflationWithCokernel_le_inflation A s hi)
    have hf : f₁ = f₂ := (cancel_mono s).1 h
    exact ⟨X, 𝟙 X, E.weakIsomorphisms_id A X, by simp [hf]⟩
  · obtain ⟨B, i, his, hc, hB⟩ := hp
    let hk := E.kernel (ShortComplex.mk i s his) hc
    have hz : (f₁ - f₂) ≫ s = 0 := by simp [Preadditive.sub_comp, h]
    let g := hk.lift (KernelFork.ofι (f₁ - f₂) hz)
    have hg : g ≫ i = f₁ - f₂ := hk.fac _ WalkingParallelPair.zero
    obtain ⟨T, t, ht, htg⟩ := hA.exists_weakInflation_comp_eq_zero E A g hB
    refine ⟨T, t, E.inflationWithCokernel_le_weakIsomorphisms A t ht, ?_⟩
    apply sub_eq_zero.mp
    rw [← Preadditive.comp_sub, ← hg, ← Category.assoc, htg, zero_comp]

/-- The cancellation axiom extends from elementary weak isomorphisms to all
finite composites. -/
lemma RightFiltering.cancel (hA : E.RightFiltering A)
    {Y Z : C} {s : Y ⟶ Z} (hs : E.weakIsomorphisms A s) :
    ∀ {X : C} (f₁ f₂ : X ⟶ Y), f₁ ≫ s = f₂ ≫ s →
      ∃ (T : C) (t : T ⟶ X), E.weakIsomorphisms A t ∧ t ≫ f₁ = t ≫ f₂ := by
  induction hs with
  | of s hs => exact fun f₁ f₂ h => hA.cancel_generator E A f₁ f₂ s hs h
  | id Y =>
    intro X f₁ f₂ h
    exact ⟨X, 𝟙 X, E.weakIsomorphisms_id A X, by simpa using h⟩
  | @comp_of Y Z V s r hs hr ih =>
    intro X f₁ f₂ h
    obtain ⟨T, t, ht, hft⟩ := hA.cancel_generator E A (f₁ ≫ s) (f₂ ≫ s) r hr
      (by simpa only [Category.assoc] using h)
    obtain ⟨T', t', ht', hft'⟩ := ih (t ≫ f₁) (t ≫ f₂)
      (by simpa only [Category.assoc] using hft)
    exact ⟨T', t' ≫ t, E.weakIsomorphisms_comp A ht' ht,
      by simpa only [Category.assoc] using hft'⟩

/-- Right filtering alone already yields a genuine right calculus of fractions
for the weak isomorphisms. The special axiom is needed later for exactness. -/
lemma RightFiltering.hasRightCalculusOfFractions (hA : E.RightFiltering A) :
    (E.weakIsomorphisms A).HasRightCalculusOfFractions where
  exists_rightFraction := by
    intro X Y φ
    obtain ⟨T, t, g, ht, h⟩ := hA.rightOre E A φ.hs φ.f
    exact ⟨⟨t, ht, g⟩, h⟩
  ext := by
    intro X Y Y' f₁ f₂ s hs h
    obtain ⟨T, t, ht, htf⟩ := hA.cancel E A hs f₁ f₂ h
    exact ⟨T, t, ht, htf⟩

/-- Pushout gives the left Ore square for a generating inflation. -/
lemma leftOre_inflation {X Y Z : C} (i : X ⟶ Y)
    (hi : E.inflationWithCokernel A i) (f : X ⟶ Z) :
    ∃ (T : C) (s : Z ⟶ T) (g : Y ⟶ T),
      E.inflationWithCokernel A s ∧ f ≫ s = i ≫ g := by
  obtain ⟨B, p, hip, hc, hB⟩ := hi
  let : HasPushout i f := E.inflation.hasPushout f (E.inflation_of_conflation hc)
  refine ⟨pushout i f, pushout.inr i f, pushout.inl i f, ?_,
    (pushout.condition (f := i) (g := f)).symm⟩
  exact E.inflationWithCokernel_of_conflation A (E.pushoutConflation_mem hc f) hB

/-- The left Ore condition on generating weak isomorphisms. -/
lemma LeftFiltering.leftOre_generator (hA : E.LeftFiltering A)
    {X Y Z : C} (s : X ⟶ Y) (hs : E.weakIsomorphismGenerator A s) (f : X ⟶ Z) :
    ∃ (T : C) (t : Z ⟶ T) (g : Y ⟶ T),
      E.weakIsomorphisms A t ∧ f ≫ t = s ≫ g := by
  rcases hs with hi | hp
  · obtain ⟨T, t, g, ht, h⟩ := E.leftOre_inflation A s hi f
    exact ⟨T, t, g, E.inflationWithCokernel_le_weakIsomorphisms A t ht, h⟩
  · obtain ⟨T, t, g, ht, h⟩ := hA.leftOre_deflation E A s hp f
    exact ⟨T, t, g, E.deflationWithKernel_le_weakIsomorphisms A t ht, h⟩

/-- The left Ore condition for all finite composites of weak generators. -/
lemma LeftFiltering.leftOre (hA : E.LeftFiltering A)
    {X Y : C} {s : X ⟶ Y} (hs : E.weakIsomorphisms A s) :
    ∀ {Z : C} (f : X ⟶ Z), ∃ (T : C) (t : Z ⟶ T) (g : Y ⟶ T),
      E.weakIsomorphisms A t ∧ f ≫ t = s ≫ g := by
  induction hs with
  | of s hs => exact fun f => hA.leftOre_generator E A s hs f
  | id X =>
    intro Z f
    exact ⟨Z, 𝟙 Z, f, E.weakIsomorphisms_id A Z, by simp⟩
  | @comp_of X Y Z s r hs hr ih =>
    intro V f
    obtain ⟨T, t, g, ht, htg⟩ := ih f
    obtain ⟨T', t', g', ht', htg'⟩ := hA.leftOre_generator E A r hr g
    refine ⟨T', t ≫ t', g', E.weakIsomorphisms_comp A ht ht', ?_⟩
    calc
      f ≫ (t ≫ t') = (f ≫ t) ≫ t' := (Category.assoc _ _ _).symm
      _ = (s ≫ g) ≫ t' := by rw [htg]
      _ = s ≫ (g ≫ t') := Category.assoc _ _ _
      _ = s ≫ (r ≫ g') := by rw [htg']
      _ = (s ≫ r) ≫ g' := (Category.assoc _ _ _).symm

/-- Left cancellation for generators factors a difference through a cokernel
in the subcategory, then annihilates it by left filtering. -/
lemma LeftFiltering.cancel_generator (hA : E.LeftFiltering A)
    {X Y Z : C} (f₁ f₂ : Y ⟶ Z) (s : X ⟶ Y)
    (hs : E.weakIsomorphismGenerator A s) (h : s ≫ f₁ = s ≫ f₂) :
    ∃ (T : C) (t : Z ⟶ T), E.weakIsomorphisms A t ∧ f₁ ≫ t = f₂ ≫ t := by
  rcases hs with hi | hp
  · obtain ⟨B, p, hsp, hc, hB⟩ := hi
    let hk := E.cokernel (ShortComplex.mk s p hsp) hc
    have hz : s ≫ (f₁ - f₂) = 0 := by simp [Preadditive.comp_sub, h]
    let g := hk.desc (CokernelCofork.ofπ (f₁ - f₂) hz)
    have hg : p ≫ g = f₁ - f₂ := hk.fac _ WalkingParallelPair.one
    obtain ⟨T, t, ht, htg⟩ := hA.exists_comp_weakDeflation_eq_zero E A g hB
    refine ⟨T, t, E.deflationWithKernel_le_weakIsomorphisms A t ht, ?_⟩
    apply sub_eq_zero.mp
    rw [← Preadditive.sub_comp, ← hg, Category.assoc, htg, comp_zero]
  · let := E.epi_of_deflation (E.deflationWithKernel_le_deflation A s hp)
    have hf : f₁ = f₂ := (cancel_epi s).1 h
    exact ⟨Z, 𝟙 Z, E.weakIsomorphisms_id A Z, by simp [hf]⟩

/-- Left cancellation for finite composites of weak generators. -/
lemma LeftFiltering.cancel (hA : E.LeftFiltering A)
    {X Y : C} {s : X ⟶ Y} (hs : E.weakIsomorphisms A s) :
    ∀ {Z : C} (f₁ f₂ : Y ⟶ Z), s ≫ f₁ = s ≫ f₂ →
      ∃ (T : C) (t : Z ⟶ T), E.weakIsomorphisms A t ∧ f₁ ≫ t = f₂ ≫ t := by
  induction hs with
  | of s hs => exact fun f₁ f₂ h => hA.cancel_generator E A f₁ f₂ s hs h
  | id Y =>
    intro Z f₁ f₂ h
    exact ⟨Z, 𝟙 Z, E.weakIsomorphisms_id A Z, by simpa using h⟩
  | @comp_of X Y V s r hs hr ih =>
    intro Z f₁ f₂ h
    obtain ⟨T, t, ht, hft⟩ := ih (r ≫ f₁) (r ≫ f₂)
      (by simpa only [Category.assoc] using h)
    obtain ⟨T', t', ht', hft'⟩ := hA.cancel_generator E A (f₁ ≫ t) (f₂ ≫ t) r hr
      (by simpa only [Category.assoc] using hft)
    exact ⟨T', t ≫ t', E.weakIsomorphisms_comp A ht ht',
      by simpa only [Category.assoc] using hft'⟩

/-- Left filtering yields a genuine left calculus of fractions. -/
lemma LeftFiltering.hasLeftCalculusOfFractions (hA : E.LeftFiltering A) :
    (E.weakIsomorphisms A).HasLeftCalculusOfFractions where
  exists_leftFraction := by
    intro X Y φ
    obtain ⟨T, t, g, ht, h⟩ := hA.leftOre E A φ.hs φ.f
    exact ⟨⟨g, t, ht⟩, h⟩
  ext := by
    intro X' X Y f₁ f₂ s hs h
    obtain ⟨T, t, ht, htf⟩ := hA.cancel E A hs f₁ f₂ h
    exact ⟨T, t, ht, htf⟩

/-- Admissible subquotient closure in particular implies repleteness. -/
lemma IsClosedUnderAdmissibleSubquotients.isClosedUnderIsomorphisms
    (hA : E.IsClosedUnderAdmissibleSubquotients A) : A.IsClosedUnderIsomorphisms where
  of_iso e hX := hA.quotients e.hom (E.deflation_of_iso e) hX

/-- A nonempty admissible-subobject-closed subcategory contains the zero object. -/
lemma IsClosedUnderAdmissibleSubobjects.zero_mem
    (hA : E.IsClosedUnderAdmissibleSubobjects A) {X : C} (hX : A X) : A 0 :=
  hA (0 : 0 ⟶ X) (E.inflation_zero X) hX

/-- Membership of the cokernel is independent of the chosen conflation. -/
lemma inflationWithCokernel_iff_of_conflation [A.IsClosedUnderIsomorphisms]
    {S : ShortComplex C} (hS : E.conflation S) :
    E.inflationWithCokernel A S.f ↔ A S.X₃ := by
  constructor
  · rintro ⟨Z, p, h, hc, hZ⟩
    exact A.prop_of_iso
      ((E.cokernel (ShortComplex.mk S.f p h) hc).coconePointUniqueUpToIso (E.cokernel S hS)) hZ
  · exact E.inflationWithCokernel_of_conflation A hS

/-- Membership of the kernel is independent of the chosen conflation. -/
lemma deflationWithKernel_iff_of_conflation [A.IsClosedUnderIsomorphisms]
    {S : ShortComplex C} (hS : E.conflation S) :
    E.deflationWithKernel A S.g ↔ A S.X₁ := by
  constructor
  · rintro ⟨Z, i, h, hc, hZ⟩
    exact A.prop_of_iso
      ((E.kernel (ShortComplex.mk i S.g h) hc).conePointUniqueUpToIso (E.kernel S hS)) hZ
  · exact E.deflationWithKernel_of_conflation A hS

/-- Every object of the subcategory maps to zero by a generating deflation. -/
lemma deflationWithKernel_to_zero {X : C} (hX : A X) :
    E.deflationWithKernel A (0 : X ⟶ 0) := by
  refine ⟨X, 𝟙 X, by simp, ?_, hX⟩
  exact E.conflation_of_inflation_of_isCokernel (E.inflation_id X)
    (cokernel.isColimitCoconeZeroCocone (𝟙 X))

/-- The zero object maps to every object of the subcategory by a generating inflation. -/
lemma inflationWithCokernel_from_zero {X : C} (hX : A X) :
    E.inflationWithCokernel A (0 : 0 ⟶ X) := by
  refine ⟨X, 𝟙 X, by simp, ?_, hX⟩
  exact E.conflation_of_isKernel _ (kernel.isLimitConeZeroCone (𝟙 X)) (E.deflation_id X)

/-- If the subcategory contains zero, every isomorphism is already an
inflation generator (not merely in a saturation of the weak class). -/
lemma inflationWithCokernel_of_iso (h₀ : A 0) {X Y : C} (e : X ≅ Y) :
    E.inflationWithCokernel A e.hom := by
  refine ⟨0, 0, by simp, ?_, h₀⟩
  exact E.conflation_of_inflation_of_isCokernel (E.inflation_of_iso e)
    (cokernel.isColimitCoconeZeroCocone e.hom)

lemma weakIsomorphisms_of_iso (h₀ : A 0) {X Y : C} (e : X ≅ Y) :
    E.weakIsomorphisms A e.hom :=
  E.inflationWithCokernel_le_weakIsomorphisms A e.hom
    (E.inflationWithCokernel_of_iso A h₀ e)

/-- Closure under changes of source and target by isomorphisms follows from
multiplicativity and the explicit zero-cokernel generators. -/
lemma weakIsomorphisms_respectsIso (h₀ : A 0) : (E.weakIsomorphisms A).RespectsIso := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro X Y f hf
  let : IsIso f := hf
  exact E.weakIsomorphisms_of_iso A h₀ (asIso f)

end Quillen.ExactStructure

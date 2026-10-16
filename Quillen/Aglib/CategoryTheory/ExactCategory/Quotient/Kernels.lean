/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Aglib.CategoryTheory.ExactCategory.Quotient.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels in a right-filtering exact quotient

Right fractions preserve actual ambient kernel universal properties. The
argument first proves preservation of monomorphisms by clearing a weak
isomorphism from an equality, then constructs the kernel lift by clearing the
zero composite. This is one half of quotient exactness, not an assumed exact
structure on the quotient.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactQuotient
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : ObjectProperty C)
  [Preadditive (ExactQuotient E A)] [(Q E A).Additive]

/-- Right filtering makes the quotient preserve ordinary monomorphisms. -/
lemma mono_map (hA : E.RightFiltering A) {X Y : C} (i : X ⟶ Y) [Mono i] :
    Mono ((Q E A).map i) := by
  apply Preadditive.mono_of_cancel_zero
  intro T a ha
  obtain ⟨T, rfl⟩ := obj_surjective E A T
  obtain ⟨φ, rfl⟩ := exists_rightFraction E A hA a
  have hzero : (Q E A).map (φ.f ≫ i) = (Q E A).map 0 := by
    calc
      (Q E A).map (φ.f ≫ i) = (Q E A).map φ.s ≫ (φ.map (Q E A) (inverts E A) ≫
          (Q E A).map i) := by simp
      _ = _ := by simp [ha]
  obtain ⟨T', t, ht, htf⟩ := (map_eq_iff_precomp E A hA _ _).1 hzero
  have htfi : t ≫ φ.f = 0 := by
    apply (cancel_mono i).1
    simpa only [Category.assoc, comp_zero, zero_comp] using htf
  let := inverts E A t ht
  have hf : (Q E A).map φ.f = 0 := by
    apply (cancel_epi ((Q E A).map t)).1
    simpa only [Functor.map_comp, Functor.map_zero, comp_zero] using congrArg (Q E A).map htfi
  apply (cancel_epi ((Q E A).map φ.s)).1
  simpa using hf

/-- A morphism into the image of an ambient kernel diagram factors through
its image, by a concrete right-fraction construction. -/
lemma exists_kernel_lift (hA : E.RightFiltering A) {K X Y : C}
    {i : K ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 0)
    (hk : IsLimit (KernelFork.ofι i h)) {T : ExactQuotient E A}
    (a : T ⟶ (Q E A).obj X) (ha : a ≫ (Q E A).map p = 0) :
    ∃ b : T ⟶ (Q E A).obj K, b ≫ (Q E A).map i = a := by
  obtain ⟨T, rfl⟩ := obj_surjective E A T
  obtain ⟨φ, rfl⟩ := exists_rightFraction E A hA a
  have hzero : (Q E A).map (φ.f ≫ p) = (Q E A).map 0 := by
    calc
      (Q E A).map (φ.f ≫ p) = (Q E A).map φ.s ≫ (φ.map (Q E A) (inverts E A) ≫
          (Q E A).map p) := by simp
      _ = _ := by simp [ha]
  obtain ⟨T', t, ht, htf⟩ := (map_eq_iff_precomp E A hA _ _).1 hzero
  have htp : (t ≫ φ.f) ≫ p = 0 := by
    simpa only [Category.assoc, comp_zero] using htf
  let k := hk.lift (KernelFork.ofι (t ≫ φ.f) htp)
  have hkfac : k ≫ i = t ≫ φ.f := hk.fac _ WalkingParallelPair.zero
  let := inverts E A t ht
  refine ⟨inv ((Q E A).map φ.s) ≫ inv ((Q E A).map t) ≫ (Q E A).map k, ?_⟩
  calc
    (inv ((Q E A).map φ.s) ≫ inv ((Q E A).map t) ≫ (Q E A).map k) ≫ (Q E A).map i =
        inv ((Q E A).map φ.s) ≫ inv ((Q E A).map t) ≫ (Q E A).map (k ≫ i) := by simp
    _ = inv ((Q E A).map φ.s) ≫ (Q E A).map φ.f := by rw [hkfac, Functor.map_comp]; simp
    _ = φ.map (Q E A) (inverts E A) := rfl

/-- The image of an actual kernel is an actual kernel, under right filtering. -/
def mapKernelIsLimit (hA : E.RightFiltering A) {K X Y : C}
    {i : K ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 0)
    (hk : IsLimit (KernelFork.ofι i h)) :
    IsLimit (KernelFork.ofι ((Q E A).map i) (show (Q E A).map i ≫ (Q E A).map p = 0 by
      rw [← Functor.map_comp, h, Functor.map_zero])) := by
  letI : Mono i := Fork.IsLimit.mono hk
  letI := mono_map E A hA i
  exact KernelFork.IsLimit.ofι' _ _ (fun a ha =>
    ⟨(exists_kernel_lift E A hA h hk a ha).choose,
      (exists_kernel_lift E A hA h hk a ha).choose_spec⟩)

/-- In particular, ambient conflations retain their kernel universal property. -/
def conflationKernelIsLimit (hA : E.RightFiltering A) {S : ShortComplex C}
    (hS : E.conflation S) :
    IsLimit (KernelFork.ofι (S.map (Q E A)).f (S.map (Q E A)).zero) :=
  mapKernelIsLimit E A hA S.zero (E.kernel S hS)


/-- The usual limit-preservation predicate for any ambient kernel diagram. -/
lemma preservesKernel (hA : E.RightFiltering A) {K X Y : C}
    {i : K ⟶ X} {p : X ⟶ Y} (h : i ≫ p = 0)
    (hk : IsLimit (KernelFork.ofι i h)) :
    PreservesLimit (parallelPair p 0) (Q E A) :=
  preservesLimit_of_preserves_limit_cone hk
    ((KernelFork.isLimitMapConeEquiv _ (Q E A)).2 (mapKernelIsLimit E A hA h hk))

/-- In particular the quotient preserves the kernel of every deflation. -/
lemma preservesKernel_of_conflation (hA : E.RightFiltering A)
    {S : ShortComplex C} (hS : E.conflation S) :
    PreservesLimit (parallelPair S.g 0) (Q E A) :=
  preservesKernel E A hA S.zero (E.kernel S hS)

end Quillen.ExactQuotient

namespace Quillen.ExactQuotient
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : ObjectProperty C)

/-- Kernel preservation for the concrete additive right-filtering quotient,
with no independently assumed additive quotient structure. -/
def rightMappedConflationKernelIsLimit (hA : E.RightFiltering A)
    {S : ShortComplex C} (hS : E.conflation S) :
    letI := rightPreadditive E A hA
    letI := rightQ_additive E A hA
    IsLimit (KernelFork.ofι (S.map (Q E A)).f (S.map (Q E A)).zero) := by
  let := rightPreadditive E A hA
  let := rightQ_additive E A hA
  exact conflationKernelIsLimit E A hA hS

end Quillen.ExactQuotient

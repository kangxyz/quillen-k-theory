/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.CategoryTheory.ExactCategory.Quotient.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# One-sided exactness of the left-filtering quotient

The actual left fraction calculus proves that the quotient preserves epimorphisms
and cokernels of the specified conflations. These are universal-property proofs,
not extra axioms in a proposed exact structure on the quotient. Kernel preservation
for the left s-filtering quotient still requires a separate argument.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactQuotient

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : ObjectProperty C)

section

variable [Preadditive (ExactQuotient E A)] [(Q E A).Additive]

/-- Left fractions show that every ambient epimorphism remains epic. -/
lemma epi_map (hA : E.LeftFiltering A) {X Y : C} (p : X ⟶ Y) [Epi p] :
    Epi ((Q E A).map p) := by
  apply Preadditive.epi_of_cancel_zero
  intro V f hf
  obtain ⟨Z, rfl⟩ := obj_surjective E A V
  obtain ⟨φ, rfl⟩ := exists_leftFraction E A hA f
  let := inverts E A φ.s φ.hs
  have hnum : (Q E A).map (p ≫ φ.f) = (Q E A).map (0 : X ⟶ φ.Y') := by
    have hh := congrArg (fun k => k ≫ (Q E A).map φ.s) hf
    simpa [MorphismProperty.LeftFraction.map, Category.assoc] using hh
  obtain ⟨T, t, ht, hpt⟩ := (map_eq_iff_postcomp E A hA _ _).1 hnum
  let := inverts E A t ht
  have hft : φ.f ≫ t = 0 := (cancel_epi p).1 (by
    simpa only [Category.assoc, zero_comp, comp_zero] using hpt)
  have hφ : (Q E A).map φ.f = 0 := by
    apply (cancel_mono ((Q E A).map t)).1
    simp [← Functor.map_comp, hft]
  simp [MorphismProperty.LeftFraction.map, hφ]

/-- In particular, the quotient preserves admissible epimorphisms. -/
lemma epi_map_deflation (hA : E.LeftFiltering A) {X Y : C} (p : X ⟶ Y)
    (hp : E.deflation p) : Epi ((Q E A).map p) := by
  let := E.epi_of_deflation hp
  exact epi_map E A hA p

/-- A map annihilating the first map of a conflation factors through the image
of its cokernel, by clearing the two left denominators. -/
lemma exists_cokernel_desc (hA : E.LeftFiltering A) {S : ShortComplex C}
    (hS : E.conflation S) {V : ExactQuotient E A} (f : (Q E A).obj S.X₂ ⟶ V)
    (hf : (Q E A).map S.f ≫ f = 0) :
    ∃ (g : (Q E A).obj S.X₃ ⟶ V), (Q E A).map S.g ≫ g = f := by
  obtain ⟨Z, rfl⟩ := obj_surjective E A V
  obtain ⟨φ, rfl⟩ := exists_leftFraction E A hA f
  let := inverts E A φ.s φ.hs
  have hnum : (Q E A).map (S.f ≫ φ.f) = (Q E A).map (0 : S.X₁ ⟶ φ.Y') := by
    have hh := congrArg (fun k => k ≫ (Q E A).map φ.s) hf
    simpa [MorphismProperty.LeftFraction.map, Category.assoc] using hh
  obtain ⟨T, t, ht, hpt⟩ := (map_eq_iff_postcomp E A hA _ _).1 hnum
  let := inverts E A t ht
  have hz : S.f ≫ (φ.f ≫ t) = 0 := by
    simpa only [Category.assoc, zero_comp] using hpt
  let hc := E.cokernel S hS
  let d := hc.desc (CokernelCofork.ofπ (φ.f ≫ t) hz)
  have hd : S.g ≫ d = φ.f ≫ t := hc.fac _ WalkingParallelPair.one
  refine ⟨(Q E A).map d ≫ inv ((Q E A).map t) ≫ inv ((Q E A).map φ.s), ?_⟩
  calc
    (Q E A).map S.g ≫ ((Q E A).map d ≫ inv ((Q E A).map t) ≫
        inv ((Q E A).map φ.s)) =
      (Q E A).map (S.g ≫ d) ≫ inv ((Q E A).map t) ≫ inv ((Q E A).map φ.s) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = (Q E A).map (φ.f ≫ t) ≫ inv ((Q E A).map t) ≫ inv ((Q E A).map φ.s) := by rw [hd]
    _ = φ.map (Q E A) (inverts E A) := by
      simp [Functor.map_comp, Category.assoc, MorphismProperty.LeftFraction.map]

/-- The image of a conflation has the actual cokernel universal property. -/
def mappedConflationCokernelIsColimit (hA : E.LeftFiltering A)
    {S : ShortComplex C} (hS : E.conflation S) :
    IsColimit (CokernelCofork.ofπ ((Q E A).map S.g)
      (show (Q E A).map S.f ≫ (Q E A).map S.g = 0 by
        rw [← Functor.map_comp, S.zero, Functor.map_zero])) := by
  let := epi_map_deflation E A hA S.g (E.deflation_of_conflation hS)
  refine Cofork.IsColimit.ofExistsUnique (fun s => ?_)
  obtain ⟨d, hd⟩ := exists_cokernel_desc E A hA hS s.π (CokernelCofork.condition s)
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact (cancel_epi ((Q E A).map S.g)).1 (hd'.trans hd.symm)

/-- The standard preservation predicate for the cokernel diagram of a
specified conflation. -/
lemma preservesCokernel_of_conflation (hA : E.LeftFiltering A)
    {S : ShortComplex C} (hS : E.conflation S) :
    PreservesColimit (parallelPair S.f 0) (Q E A) :=
  preservesColimit_of_preserves_colimit_cocone (E.cokernel S hS)
    ((CokernelCofork.isColimitMapCoconeEquiv _ (Q E A)).2
      (mappedConflationCokernelIsColimit E A hA hS))

end

/-- Cokernel preservation for the concrete additive quotient structure built
from left filtering. No additive structure is assumed in this specialization. -/
def leftMappedConflationCokernelIsColimit (hA : E.LeftFiltering A)
    {S : ShortComplex C} (hS : E.conflation S) :
    letI := leftPreadditive E A hA
    letI := leftQ_additive E A hA
    IsColimit (CokernelCofork.ofπ (S.map (Q E A)).g (S.map (Q E A)).zero) := by
  let := leftPreadditive E A hA
  let := leftQ_additive E A hA
  exact mappedConflationCokernelIsColimit E A hA hS

end Quillen.ExactQuotient

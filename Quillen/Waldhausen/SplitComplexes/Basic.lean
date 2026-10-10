/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Complexes
public import Quillen.Waldhausen.PointedFunctor

/-!
# Degreewise split cofibrations of actual complexes

A degreewise split monomorphism has a retraction in each degree; the
retractions are not required to form a chain map. Pushout stability is
proved by constructing the retraction in each degree. Together with the
actual quasi-isomorphism gluing theorem this gives a Waldhausen structure,
and the identity gives an exact comparison to the ambient-monomorphism
model. No comparison equivalence is asserted.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

universe v u

namespace Quillen.Waldhausen

/-- Cobase change of a split monomorphism is split, with no additivity
hypothesis on the category. -/
theorem isSplitMono_of_isPushout {C : Type*} [Category* C]
    {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    [IsSplitMono i] (h : IsPushout i f g j) : IsSplitMono j := by
  exact IsSplitMono.mk' {
    retraction := h.desc (retraction i ≫ f) (𝟙 D) (by simp)
    id := h.inr_desc _ _ _ }

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Termwise split monomorphisms, without requiring a chain retraction. -/
def degreewiseSplitMono : MorphismProperty (CochainComplex A ℤ) :=
  fun _ _ f ↦ ∀ n : ℤ, IsSplitMono (f.f n)

instance degreewiseSplitMono_multiplicative :
    (degreewiseSplitMono (A := A)).IsMultiplicative where
  id_mem _ _ := by dsimp; infer_instance
  comp_mem f g hf hg n := by
    let : IsSplitMono (f.f n) := hf n
    let : IsSplitMono (g.f n) := hg n
    change IsSplitMono (f.f n ≫ g.f n)
    infer_instance

/-- A degreewise split monomorphism is an ambient monomorphism. -/
theorem degreewiseSplitMono_mono {K L : CochainComplex A ℤ} {f : K ⟶ L}
    (hf : degreewiseSplitMono f) : Mono f :=
  mono_of_mono_f f (fun n ↦ by let := hf n; infer_instance)

/-- Chain isomorphisms are split in every degree. -/
theorem degreewiseSplitMono_of_isIso {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [IsIso f] : degreewiseSplitMono f := by
  intro n
  infer_instance

/-- Every arrow from a zero complex is degreewise split. -/
theorem degreewiseSplitMono_of_isZero {K L : CochainComplex A ℤ} (hK : IsZero K)
    (f : K ⟶ L) : degreewiseSplitMono f := by
  intro n
  have hn := (eval A (ComplexShape.up ℤ) n).map_isZero hK
  exact IsSplitMono.mk' ⟨hn.from_ _, hn.eq_of_src _ _⟩

/-- Degreewise split monomorphisms are stable under arbitrary pushout. -/
theorem degreewiseSplitMono_pushout
    {B D E P : CochainComplex A ℤ}
    {i : B ⟶ D} {f : B ⟶ E} {g : D ⟶ P} {j : E ⟶ P}
    (hi : degreewiseSplitMono i) (h : IsPushout i f g j) : degreewiseSplitMono j := by
  intro n
  let : IsSplitMono ((eval A (ComplexShape.up ℤ) n).map i) := hi n
  exact isSplitMono_of_isPushout (h.map (eval A (ComplexShape.up ℤ) n))

/-- The degreewise split, quasi-isomorphism Waldhausen structure on actual
cochain complexes in an abelian category. -/
def splitComplexes (A : Type u) [Category.{v} A] [Abelian A] :
    Structure (CochainComplex A ℤ) :=
  { complexes A with
    cof := degreewiseSplitMono
    cof_multiplicative := inferInstance
    cof_iso := by intro K L f hf; let := hf; exact degreewiseSplitMono_of_isIso f
    cof_zero K := degreewiseSplitMono_of_isZero (isZero_zero _) _
    pushout_exists i f _ :=
      ⟨pushout i f, pushout.inl _ _, pushout.inr _ _, .of_hasPushout _ _⟩
    cof_pushout hi h := degreewiseSplitMono_pushout hi h
    gluing a b d p hi hi' h h' ei ef eg ej ha hb hd :=
      (complexes A).gluing a b d p (degreewiseSplitMono_mono hi)
        (degreewiseSplitMono_mono hi') h h' ei ef eg ej ha hb hd }

/-- The identity comparison from degreewise split to ambient-monomorphism
cofibrations is Waldhausen-exact. -/
theorem splitComplexes_to_complexes_exact :
    IsExact (splitComplexes A).cof (splitComplexes A).weq
      (complexes A).cof (complexes A).weq (𝟭 (CochainComplex A ℤ)) where
  zero h := h
  cofibration _ h := degreewiseSplitMono_mono h
  weak _ h := h
  pushout _ h := h

/-- The induced comparison on genuine connective S-construction K-groups. -/
def splitComplexesKMap (n : ℕ) : (splitComplexes A).K n →* (complexes A).K n :=
  KMap splitComplexes_to_complexes_exact n

end Quillen.Waldhausen

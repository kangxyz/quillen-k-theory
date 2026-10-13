/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Devissage.CentralEndomorphism
public import Quillen.Devissage.FiltrationRefinement

/-!
# Dévissage for a finite family of locally nilpotent central operators

The filtration is built from actual images of the operators and refined by
pullback splicing. No bound uniform in the object is required.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.FiniteCentralDevissage
open PrincipalSupportDevissage
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Joint annihilation by a finite list of actual natural endomorphisms. -/
def killedByAll (ts : List (𝟭 C ⟶ 𝟭 C)) : ObjectProperty C :=
  fun X ↦ ∀ t ∈ ts, killed t X

instance killedByAll_containsZero (ts : List (𝟭 C ⟶ 𝟭 C)) :
    (killedByAll ts).ContainsZero :=
  ⟨⟨0, isZero_zero C, fun t _ ↦ (killed t).prop_of_isZero (isZero_zero C)⟩⟩

instance killedByAll_subobjects (ts : List (𝟭 C ⟶ 𝟭 C)) :
    (killedByAll ts).IsClosedUnderSubobjects where
  prop_of_mono i _ h t ht := (killed t).prop_of_mono i (h t ht)

instance killedByAll_quotients (ts : List (𝟭 C ⟶ 𝟭 C)) :
    (killedByAll ts).IsClosedUnderQuotients where
  prop_of_epi p _ h t ht := (killed t).prop_of_epi p (h t ht)

instance killedByAll_finiteProducts (ts : List (𝟭 C ⟶ 𝟭 C)) :
    (killedByAll ts).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := {
    limitsOfShape_le := by
      rintro X ⟨p⟩ t ht
      change t.app X = 0
      apply p.isLimit.hom_ext
      intro j
      have h : t.app (p.diag.obj j) = 0 := p.prop_diag_obj j t ht
      have hn := t.naturality (p.cone.π.app j)
      change p.cone.π.app j ≫ t.app (p.diag.obj j) =
        t.app X ≫ p.cone.π.app j at hn
      rw [h, comp_zero] at hn
      simpa only [zero_comp] using hn.symm }

/-- The one-operator image filtration preserves any subquotient-closed
property already satisfied by the object. -/
theorem filtration_preserving_property (P : ObjectProperty C)
    [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
    (t : 𝟭 C ⟶ 𝟭 C) (ts : List (𝟭 C ⟶ 𝟭 C))
    (hP : ∀ X, P X → killedByAll ts X)
    (n : ℕ) (X : C) (hX : P X) (h : power t X n = 0) :
    Nonempty ((abelianExactStructure C).Filtration (killedByAll (t :: ts)) X) := by
  induction n generalizing X with
  | zero => exact ⟨.zero ((IsZero.iff_id_eq_zero X).2 (by simpa using h))⟩
  | succ n ih =>
    let i := image.ι (t.app X)
    obtain ⟨F⟩ := ih (image (t.app X)) (P.prop_of_mono i hX) (image_power_eq_zero t X n h)
    refine ⟨.step (ShortComplex.mk i (cokernel.π i) (cokernel.condition i))
      { exact := ShortComplex.cokernelSequence_exact i } F ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with hs | hs
    · subst s
      exact killed_cokernel_image t X
    · exact hP _ (P.prop_of_epi (cokernel.π i) hX) s hs

/-- Finite lists of locally nilpotent central operators admit genuine finite
filtrations whose factors are annihilated by every operator in the list. -/
theorem filtrationHypothesis (ts : List (𝟭 C ⟶ 𝟭 C))
    (h : ∀ X : C, ∀ t ∈ ts, ∃ n : ℕ, power t X n = 0) :
    Devissage.FiltrationHypothesis (killedByAll ts) := by
  induction ts with
  | nil =>
    intro X
    let S := ShortComplex.mk (0 : (0 : C) ⟶ X) (𝟙 X) (by simp)
    have hS : S.ShortExact := { exact := (S.exact_iff_mono rfl).mpr inferInstance }
    exact ⟨.step S hS (.zero (isZero_zero C)) (by simp [killedByAll])⟩
  | cons t ts ih =>
    intro X
    obtain ⟨F⟩ := ih (fun Y s hs ↦ h Y s (List.mem_cons_of_mem t hs)) X
    apply F.refine
    intro Y hY
    obtain ⟨n, hn⟩ := h Y t (List.mem_cons_self ..)
    exact filtration_preserving_property (killedByAll ts) t ts (fun _ h ↦ h) n Y hY hn

/-- The canonical inclusion of jointly annihilated objects induces the
actual homotopical dévissage isomorphism in every degree. -/
def KEquiv {C : Type u} [Category.{u} C] [Abelian C]
    (ts : List (𝟭 C ⟶ 𝟭 C))
    (h : ∀ X : C, ∀ t ∈ ts, ∃ n : ℕ, power t X n = 0) (n : ℕ) :
    (Devissage.subcategoryExactStructure (killedByAll ts)).K n ≃*
      (abelianExactStructure C).K n :=
  Devissage.KEquiv _ (filtrationHypothesis ts h) n

end Quillen.FiniteCentralDevissage

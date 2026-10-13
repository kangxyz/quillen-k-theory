/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Devissage.Grothendieck

/-!
# Refining finite abelian filtrations

Actual pullbacks splice two finite filtrations across a short exact sequence.
Consequently a finite filtration can be refined by filtrations of its factors.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.ExactStructure.Filtration
variable {C : Type u} [Category.{v} C] [Abelian C] {P : ObjectProperty C}

/-- Transport a filtration along an actual isomorphism of its endpoint. -/
def ofIso {X Y : C} (F : (abelianExactStructure C).Filtration P X) (e : X ≅ Y) :
    (abelianExactStructure C).Filtration P Y := by
  cases F with
  | zero h => exact .zero (h.of_iso e.symm)
  | step S hS F hP =>
    let T := ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) (by simp)
    have et : S ≅ T := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp [T]) (by simp [T])
    exact .step T (ShortComplex.shortExact_of_iso et hS) F hP

/-- Pull back each filtration stage along an epimorphism, starting with a
chosen actual filtration of its kernel. -/
theorem liftEpi {B : C} (F : (abelianExactStructure C).Filtration P B)
    {X : C} (p : X ⟶ B) [Epi p]
    (K : (abelianExactStructure C).Filtration P (CategoryTheory.Limits.kernel p)) :
    Nonempty ((abelianExactStructure C).Filtration P X) := by
  induction F generalizing X with
  | zero hB =>
    exact ⟨K.ofIso (kernelIsoOfEq (hB.eq_of_tgt p 0) ≪≫ kernelZeroIsoSource)⟩
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let sq := IsPullback.of_hasPullback p S.f
    let m := cokernel.map (pullback.fst p S.f) S.f (pullback.snd p S.f) p sq.w
    let := Abelian.mono_cokernel_map_of_isPullback sq
    have : Epi m := by dsimp [m]; infer_instance
    have : IsIso m := isIso_of_mono_of_epi m
    let e : CategoryTheory.Limits.cokernel (pullback.fst p S.f) ≅ S.X₃ :=
      asIso m ≪≫ (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    let k := kernel.map (pullback.snd p S.f) p (pullback.fst p S.f) S.f sq.flip.w
    let := isIso_kernel_map_of_isPullback sq.flip
    obtain ⟨L⟩ := ih (pullback.snd p S.f) (K.ofIso (asIso k).symm)
    let T := ShortComplex.mk (pullback.fst p S.f)
      (cokernel.π (pullback.fst p S.f) ≫ e.hom) (by simp)
    have hT : T.ShortExact := by
      apply ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (S₁ := ShortComplex.mk (pullback.fst p S.f)
          (cokernel.π (pullback.fst p S.f)) (cokernel.condition _)) (S₂ := T)
          (Iso.refl _) (Iso.refl _) e (by simp [T]) (by simp [T]))
      exact { exact := ShortComplex.cokernelSequence_exact _ }
    exact ⟨.step T hT L hP⟩

/-- Splicing filtrations of the two ends constructs one of the middle object. -/
theorem extension (S : ShortComplex C) (hS : S.ShortExact)
    (F : (abelianExactStructure C).Filtration P S.X₁)
    (G : (abelianExactStructure C).Filtration P S.X₃) :
    Nonempty ((abelianExactStructure C).Filtration P S.X₂) := by
  let := hS.epi_g
  let e : S.X₁ ≅ CategoryTheory.Limits.kernel S.g := hS.fIsKernel.conePointUniqueUpToIso
    (limit.isLimit _)
  exact G.liftEpi S.g (F.ofIso e)

/-- Refinement is an actual filtration of the same object, obtained by
pullback splicing, rather than a relation on its Grothendieck class. -/
theorem refine {Q : ObjectProperty C} {X : C}
    (F : (abelianExactStructure C).Filtration Q X)
    (h : ∀ Y, Q Y → Nonempty ((abelianExactStructure C).Filtration P Y)) :
    Nonempty ((abelianExactStructure C).Filtration P X) := by
  induction F with
  | zero hX => exact ⟨.zero hX⟩
  | step S hS F hQ ih =>
    obtain ⟨L⟩ := ih
    obtain ⟨G⟩ := h S.X₃ hQ
    exact extension S hS L G

end Quillen.ExactStructure.Filtration

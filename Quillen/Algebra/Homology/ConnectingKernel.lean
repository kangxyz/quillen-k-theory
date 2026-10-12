/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The connecting map as an isomorphism onto a homology kernel

If the first map of a short exact sequence of complexes induces an epimorphism
in degree `i`, the original connecting morphism in the long exact sequence
identifies homology of the quotient in degree `i` with the kernel of the first
homology map in the next degree. No replacement of the connecting map is made.

For an addition map `X ⊞ X ⟶ X`, the kernel is identified with `X` by the first
projection. Its inverse has the explicit sign convention `a ↦ (a, -a)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

/-- An epimorphism on the first homology map makes the original connecting
morphism monic. Only the degree of its source is required. -/
theorem mono_δ_of_epi_homologyMap [Epi (HomologicalComplex.homologyMap S.f i)] :
    Mono (hS.δ i j hij) := by
  apply (ShortComplex.exact_iff_mono _ ?_).mp (hS.homology_exact₃ i j hij)
  change HomologicalComplex.homologyMap S.g i = 0
  rw [← cancel_epi (HomologicalComplex.homologyMap S.f i)]
  simp only [← HomologicalComplex.homologyMap_comp, S.zero,
    HomologicalComplex.homologyMap_zero, comp_zero]

/-- The original connecting morphism, with codomain restricted to the kernel
of the first homology map. -/
def δToKernel : S.X₃.homology i ⟶ kernel (HomologicalComplex.homologyMap S.f j) :=
  kernel.lift _ (hS.δ i j hij) (hS.δ_comp i j hij)

@[reassoc (attr := simp)]
theorem δToKernel_ι :
    hS.δToKernel i j hij ≫ kernel.ι (HomologicalComplex.homologyMap S.f j) = hS.δ i j hij :=
  kernel.lift_ι _ _ _

/-- Exactness of the actual long exact sequence proves the kernel restriction
is an isomorphism when the preceding first homology map is epic. -/
theorem isIso_δToKernel [Epi (HomologicalComplex.homologyMap S.f i)] :
    IsIso (hS.δToKernel i j hij) := by
  have : Mono (hS.δ i j hij) := hS.mono_δ_of_epi_homologyMap i j hij
  have : Mono (hS.δToKernel i j hij) :=
    mono_of_mono_fac (hS.δToKernel_ι i j hij)
  have : Epi (hS.δToKernel i j hij) := (hS.homology_exact₁ i j hij).epi_kernelLift
  exact isIso_of_mono_of_epi _

/-- The connecting isomorphism from quotient homology to the actual kernel
of the first homology map. -/
def connectingKernelIso [Epi (HomologicalComplex.homologyMap S.f i)] :
    S.X₃.homology i ≅ kernel (HomologicalComplex.homologyMap S.f j) :=
  have := hS.isIso_δToKernel i j hij
  asIso (hS.δToKernel i j hij)

@[reassoc (attr := simp)]
theorem connectingKernelIso_hom_ι [Epi (HomologicalComplex.homologyMap S.f i)] :
    (hS.connectingKernelIso i j hij).hom ≫ kernel.ι (HomologicalComplex.homologyMap S.f j) =
      hS.δ i j hij :=
  hS.δToKernel_ι i j hij

@[reassoc (attr := simp)]
theorem connectingKernelIso_inv_δ [Epi (HomologicalComplex.homologyMap S.f i)] :
    (hS.connectingKernelIso i j hij).inv ≫ hS.δ i j hij =
      kernel.ι (HomologicalComplex.homologyMap S.f j) := by
  rw [← hS.connectingKernelIso_hom_ι i j hij]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- The kernel of addition, identified by its first projection. The inverse
has sign convention `a ↦ (a, -a)`. -/
def kernelAdditionIso (X : C) : kernel (biprod.desc (𝟙 X) (𝟙 X)) ≅ X where
  hom := kernel.ι _ ≫ biprod.fst
  inv := kernel.lift _ (biprod.lift (𝟙 X) (-𝟙 X)) (by simp)
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (biprod.desc (𝟙 X) (𝟙 X)))).mp
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    apply biprod.hom_ext
    · simp
    · have h := kernel.condition (biprod.desc (𝟙 X) (𝟙 X))
      conv_lhs at h => arg 2; rw [biprod.desc_eq]
      rw [Preadditive.comp_add] at h
      simp only [Category.comp_id] at h
      simpa using (neg_eq_of_add_eq_zero_right h)
  inv_hom_id := by simp

@[reassoc, simp]
theorem kernelAdditionIso_hom (X : C) :
    (kernelAdditionIso X).hom =
      kernel.ι (biprod.desc (𝟙 X) (𝟙 X)) ≫ biprod.fst := rfl

@[reassoc (attr := simp)]
theorem kernelAdditionIso_inv_ι (X : C) :
    (kernelAdditionIso X).inv ≫ kernel.ι (biprod.desc (𝟙 X) (𝟙 X)) =
      biprod.lift (𝟙 X) (-𝟙 X) :=
  kernel.lift_ι _ _ _

end CategoryTheory.Limits

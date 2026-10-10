/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Devissage.ReflectorFiltration

/-! # Isomorphism and monotonicity laws for actual unit-kernel iteration -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ReflectorDevissage
variable {C : Type u} [Category.{v} C] [Abelian C]
  {T : C ⥤ C} (η : 𝟭 C ⟶ T)

/-- Unit naturality gives a canonical isomorphism of its actual kernels. -/
def kernelStepIso {X Y : C} (e : X ≅ Y) : kernelStep η X ≅ kernelStep η Y :=
  kernel.mapIso _ _ e (T.mapIso e) (η.naturality e.hom).symm

/-- Iterated unit kernels preserve actual isomorphisms. -/
def kernelIterateIso (n : ℕ) {X Y : C} (e : X ≅ Y) :
    kernelIterate η n X ≅ kernelIterate η n Y := by
  induction n generalizing X Y with
  | zero => exact e
  | succ n ih => exact ih (kernelStepIso η e)

/-- Addition of iteration counts composes genuine kernel iterations. -/
theorem kernelIterate_add (m n : ℕ) (X : C) :
    kernelIterate η (m + n) X = kernelIterate η m (kernelIterate η n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (kernelStep η X)

/-- A unit-kernel iteration of a zero object remains zero. -/
theorem kernelIterate_isZero (n : ℕ) (X : C) (hX : IsZero X) :
    IsZero (kernelIterate η n X) := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih _ (IsZero.of_mono (kernel.ι (η.app X)) hX)

/-- Once the actual iteration vanishes, every later stage vanishes. -/
theorem kernelIterate_isZero_of_le {m n : ℕ} (h : m ≤ n) (X : C)
    (hX : IsZero (kernelIterate η m X)) : IsZero (kernelIterate η n X) := by
  rw [← Nat.sub_add_cancel h, kernelIterate_add]
  exact kernelIterate_isZero η (n - m) _ hX

end Quillen.ReflectorDevissage

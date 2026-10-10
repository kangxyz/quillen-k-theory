/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Localization.Serre.KernelPushoutComparison
public import Quillen.Localization.Serre.OverQArrows

/-! # Existence in the kernel-comma reflection -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

instance kernelPushoutOverHom_mono {N : C} (X : Over N) {U : C}
    (i : (overKernel N).obj X ⟶ U) [Mono i] : Mono (kernelPushoutOverHom X i).left :=
  inferInstanceAs (Mono (pushout.inl (overKernelι X) i))

/-- A kernel-comma arrow to a surjective object extends across the actual
kernel pushout. Both the slice Q-triangle and the prescribed kernel triangle
are proved from the cospan comparison. -/
theorem kernelPushout_factor_exists {N : C} {X Y : Over N}
    [Epi X.hom] {U T : C}
    (i : (overKernel N).obj X ⟶ U) [Mono i] (p : T ⟶ U) [Epi p]
    (q : T ⟶ (overKernel N).obj Y) [Epi q]
    (f : Q.of (overDeflation N) (overInflation N) X ⟶ Q.of _ _ Y)
    (hf : (overKernelQ N).map f ≫ Q.surjectionArrow q =
      Q.inflationArrow i ≫ Q.surjectionArrow p) :
    ∃ g : Q.of (overDeflation N) (overInflation N) (Over.mk (kernelPushoutMap X i)) ⟶ Q.of _ _ Y,
      overInflationArrow (kernelPushoutOverHom X i) ≫ g = f ∧
      (overKernelQ N).map g ≫ Q.surjectionArrow q =
        Q.surjectionArrow (p ≫ (kernelPushoutIso X i).hom) := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  change Span (overDeflation N) (overInflation N) X Y at s
  let j := overSpanPushoutInl s
  let r := overSpanPushoutInr s
  have hj : Mono j.left := inferInstanceAs (Mono (overSpanPushoutInl s).left)
  have hr : Epi r.left := inferInstanceAs (Epi (overSpanPushoutInr s).left)
  have hZ : Epi (overSpanPushout s).hom := inferInstance
  have hc : Q.inflationArrow ((overKernel N).map j) ≫
      Q.surjectionArrow (q ≫ (overKernel N).map r) =
      Q.inflationArrow i ≫ Q.surjectionArrow p := by
    rw [← Q.surjectionArrow_comp, ← Category.assoc, overSpanPushout_kernel_cospan]
    exact hf
  obtain ⟨e, he, hp⟩ := Q.exists_cospanIso_of_eq
    ((overKernel N).map j) (q ≫ (overKernel N).map r) i p hc
  have hei : i ≫ e.inv = (overKernel N).map j := by rw [← he]; simp
  let a := kernelPushoutComparisonIso j i e.symm hei
  let t : Y ⟶ Over.mk (kernelPushoutMap X i) := r ≫ a.inv
  have ht : Epi t.left := by
    change Epi ((Over.forget N).map (r ≫ a.inv))
    rw [Functor.map_comp]
    have : Epi ((Over.forget N).map r) := hr
    infer_instance
  refine ⟨overSurjectionArrow t, ?_, ?_⟩
  · apply (overForgetQ N).map_injective
    rw [Functor.map_comp, overForgetQ_inflationArrow, overForgetQ_surjectionArrow]
    calc
      _ = Q.inflationArrow j.left ≫ Q.surjectionArrow r.left := by
        apply Q.cospan_eq_of_iso _ _ _ _ ((Over.forget N).mapIso a)
        · exact kernelPushoutComparisonIso_inl j i e.symm hei
        · change (r.left ≫ a.inv.left) ≫ a.hom.left = r.left
          simp
      _ = _ := overSpanPushout_forget_cospan s
  · rw [overKernelQ_surjectionArrow, Q.surjectionArrow_comp]
    congr 1
    have ha : (overKernel N).map a.inv = e.hom ≫ (kernelPushoutIso X i).hom := by
      apply (cancel_mono ((overKernel N).map a.hom)).1
      rw [← Functor.map_comp, a.inv_hom_id, (overKernel N).map_id]
      change 𝟙 _ = (e.hom ≫ (kernelPushoutIso X i).hom) ≫
        (overKernel N).map (kernelPushoutComparisonIso j i e.symm hei).hom
      rw [kernelPushoutComparisonIso_kernel]
      simp
    change q ≫ (overKernel N).map (r ≫ a.inv) = p ≫ (kernelPushoutIso X i).hom
    rw [Functor.map_comp, ha, ← Category.assoc, ← Category.assoc, hp]

end Quillen.SerreLocalization

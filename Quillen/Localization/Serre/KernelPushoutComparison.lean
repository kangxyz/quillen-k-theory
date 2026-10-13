/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.KernelPushout
public import Quillen.CategoryTheory.QConstruction.Abelian.Cospans

/-!
# Ordinary cospans and comparisons of kernel pushouts

The pushout of an admissible span over a fixed base has a genuine
mono-epi cospan. Its kernel square is bicartesian. A monomorphism of
extensions with the same quotient is itself the pushout of its kernel map.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- A monomorphism between epimorphisms with fixed quotient is the pushout
of its induced map on kernels. -/
theorem overKernel_mono_isPushout {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] :
    IsPushout (overKernelι X) ((overKernel N).map f) f.left (overKernelι Y) := by
  let k := (overKernel N).map f
  let d := pushout.desc f.left (overKernelι Y) (overKernel_map_isPullback f).w.symm
  have hd : d ≫ Y.hom = kernelPushoutMap X k := by
    apply pushout.hom_ext
    · simp [d, k, Over.w]
    · simp [d, k]
  let g : Over.mk (kernelPushoutMap X k) ⟶ Y := Over.homMk d hd
  have hdm : Mono d := (IsPushout.of_hasPushout (overKernelι X) k).mono_of_isPullback_of_mono
    (overKernel_map_isPullback f).flip d (by simp [d, k]) (by simp [d, k])
  have hgk : (overKernel N).map g = (kernelPushoutIso X k).inv := by
    apply (cancel_mono (overKernelι Y)).1
    rw [(overKernel_map_isPullback g).w]
    apply (cancel_epi (kernelPushoutIso X k).hom).1
    rw [← Category.assoc, kernelPushoutIso_hom_ι]
    simp [g, d, k]
  have : IsIso ((overKernel N).map g) := by rw [hgk]; infer_instance
  have : Mono g.left := hdm
  have : Epi (Over.mk (kernelPushoutMap X k)).hom := kernelPushoutMap_epi X k
  have : IsIso g := over_isIso_of_mono_of_kernel_isIso g
  have : IsIso d := inferInstanceAs (IsIso ((Over.forget N).map g))
  exact (IsPushout.of_hasPushout (overKernelι X) k).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso d)
    (by simp) (by simp [k]) (by simp [d, k]) (by simp [d, k])

/-- A prescribed identification of the target kernel transports the genuine
extension pushout square. -/
theorem overKernel_mono_isPushout_of_iso {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    IsPushout (overKernelι X) i f.left (e.hom ≫ overKernelι Y) := by
  apply (overKernel_mono_isPushout f).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
  · simp
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← h]
    simp
  · simp
  · simp

/-- The explicit kernel-pushout extension is uniquely identified with any
monomorphic extension having its prescribed kernel enlargement. -/
def kernelPushoutComparisonIso {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    Over.mk (kernelPushoutMap X i) ≅ Y := by
  let sq := overKernel_mono_isPushout_of_iso f i e h
  let a := (IsPushout.of_hasPushout (overKernelι X) i).isoIsPushout _ _ sq
  refine Over.isoMk a ?_
  apply pushout.hom_ext
  · simp [a, Over.w]
  · simp [a]

@[reassoc (attr := simp)]
theorem kernelPushoutComparisonIso_inl {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    pushout.inl (overKernelι X) i ≫ (kernelPushoutComparisonIso f i e h).hom.left =
      f.left := by
  simp [kernelPushoutComparisonIso]

@[reassoc (attr := simp)]
theorem kernelPushoutComparisonIso_inr {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    pushout.inr (overKernelι X) i ≫ (kernelPushoutComparisonIso f i e h).hom.left =
      e.hom ≫ overKernelι Y := by
  simp [kernelPushoutComparisonIso]

/-- The comparison acts on the chosen pullback kernels by exactly the
prescribed kernel identification. -/
theorem kernelPushoutComparisonIso_kernel {N : C} {X Y : Over N} (f : X ⟶ Y)
    [Epi X.hom] [Epi Y.hom] [Mono f.left] {U : C}
    (i : (overKernel N).obj X ⟶ U) (e : U ≅ (overKernel N).obj Y)
    (h : i ≫ e.hom = (overKernel N).map f) :
    (overKernel N).map (kernelPushoutComparisonIso f i e h).hom =
      (kernelPushoutIso X i).inv ≫ e.hom := by
  apply (cancel_mono (overKernelι Y)).1
  rw [(overKernel_map_isPullback (kernelPushoutComparisonIso f i e h).hom).w]
  apply (cancel_epi (kernelPushoutIso X i).hom).1
  rw [← Category.assoc, kernelPushoutIso_hom_ι]
  simp

section SpanPushout
variable {N : C} {X Y : Over N}
    (s : Span (overDeflation N) (overInflation N) X Y)

/-- The ordinary pushout of the underlying span, retaining its map to the base. -/
def overSpanPushoutMap : pushout s.l.left s.r.left ⟶ N :=
  pushout.desc X.hom Y.hom ((Over.w s.l).trans (Over.w s.r).symm)

/-- The pushout of the underlying admissible span, regarded as an object of the slice over `N`
via `overSpanPushoutMap s`. -/
abbrev overSpanPushout : Over N := Over.mk (overSpanPushoutMap s)

/-- The monomorphic leg of the ordinary pushout cospan over the fixed base. -/
def overSpanPushoutInl : X ⟶ overSpanPushout s :=
  Over.homMk (pushout.inl s.l.left s.r.left) (pushout.inl_desc _ _ _)

/-- The epimorphic leg of the ordinary pushout cospan over the fixed base. -/
def overSpanPushoutInr : Y ⟶ overSpanPushout s :=
  Over.homMk (pushout.inr s.l.left s.r.left) (pushout.inr_desc _ _ _)

instance overSpanPushout_hom_epi [Epi X.hom] : Epi (overSpanPushout s).hom :=
  epi_of_epi_fac (Over.w (overSpanPushoutInl s))

instance overSpanPushoutInl_mono : Mono (overSpanPushoutInl s).left := by
  have : Mono s.r.left := s.wr
  exact inferInstanceAs (Mono (pushout.inl s.l.left s.r.left))

instance overSpanPushoutInr_epi : Epi (overSpanPushoutInr s).left := by
  have : Epi s.l.left := s.wl
  exact inferInstanceAs (Epi (pushout.inr s.l.left s.r.left))

/-- The ordinary pushout square is also a pullback in the slice. -/
theorem overSpanPushout_isPullback :
    IsPullback s.l s.r (overSpanPushoutInl s) (overSpanPushoutInr s) := by
  have : Mono s.r.left := s.wr
  apply IsPullback.of_map_of_faithful (Over.forget N)
  change IsPullback s.l.left s.r.left (pushout.inl s.l.left s.r.left)
    (pushout.inr s.l.left s.r.left)
  exact isPullback_of_isPushout_mono (IsPushout.of_hasPushout s.l.left s.r.left)

/-- Kernel base change carries the actual span to the pullback of its
ordinary cospan on kernels. -/
theorem overSpanPushout_kernel_isPullback :
    IsPullback ((overKernel N).map s.l) ((overKernel N).map s.r)
      ((overKernel N).map (overSpanPushoutInl s))
      ((overKernel N).map (overSpanPushoutInr s)) :=
  (overSpanPushout_isPullback s).map (overKernel N)

instance overSpanPushout_kernelInl_mono :
    Mono ((overKernel N).map (overSpanPushoutInl s)) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
    (overKernel_map_isPullback (overSpanPushoutInl s)).flip inferInstance

instance overSpanPushout_kernelInr_epi :
    Epi ((overKernel N).map (overSpanPushoutInr s)) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
    (overKernel_map_isPullback (overSpanPushoutInr s)).flip inferInstance

/-- The induced square on kernels is an actual pushout square. -/
theorem overSpanPushout_kernel_isPushout :
    IsPushout ((overKernel N).map s.l) ((overKernel N).map s.r)
      ((overKernel N).map (overSpanPushoutInl s))
      ((overKernel N).map (overSpanPushoutInr s)) :=
  isPushout_of_isPullback_epi (overSpanPushout_kernel_isPullback s)

/-- The ambient monomorphic cospan leg is the pushout of its kernel map. -/
theorem overSpanPushoutInl_kernel_isPushout [Epi X.hom] :
    IsPushout (overKernelι X) ((overKernel N).map (overSpanPushoutInl s))
      (overSpanPushoutInl s).left (overKernelι (overSpanPushout s)) :=
  overKernel_mono_isPushout (overSpanPushoutInl s)

/-- The underlying ordinary cospan represents the original ambient Q-arrow. -/
theorem overSpanPushout_forget_cospan :
    Q.inflationArrow (overSpanPushoutInl s).left ≫
        Q.surjectionArrow (overSpanPushoutInr s).left =
      (overForgetQ N).map (Q.mkHom _ _ s) :=
  Q.span_cospan_factorization ((overForgetCompatible N).mapSpan s)

/-- The ordinary cospan on kernels represents the original kernel Q-arrow. -/
theorem overSpanPushout_kernel_cospan :
    Q.inflationArrow ((overKernel N).map (overSpanPushoutInl s)) ≫
        Q.surjectionArrow ((overKernel N).map (overSpanPushoutInr s)) =
      (overKernelQ N).map (Q.mkHom _ _ s) := by
  let sq := overSpanPushout_kernel_isPullback s
  rw [← Q.mkHom_cospanSpan]
  change Q.mkHom _ _ _ = Q.mkHom _ _ ((overKernelCompatible N).mapSpan s)
  symm
  apply Q.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · exact sq.isoPullback_hom_fst
  · exact sq.isoPullback_hom_snd

end SpanPushout

end Quillen.SerreLocalization

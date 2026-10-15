/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.CategoryTheory.ExactCategory.ObscureAxiom
public import Quillen.CategoryTheory.ExactCategory.SFiltering

/-!
# Special deflations and inflation denominators

The constructions here retain actual conflations. The matrix proof of the
obscure axiom supplies the exact-category short five lemma and the resulting
bicartesian diagram needed to straighten an elementary weak deflation.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- An admissible epimorphism which is also a monomorphism is invertible. -/
lemma isIso_of_deflation_of_mono {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : E.deflation f) : IsIso f := by
  obtain ⟨K, k, hk, hc⟩ := hf
  have hz : k = 0 := (cancel_mono f).1 (by simpa using hk)
  exact CokernelCofork.IsColimit.isIso_π _ (E.cokernel _ hc) hz

/-- The short five lemma with identity maps at the endpoints, proved directly
inside the exact category using the obscure axiom. -/
lemma isIso_of_conflations_fixed_ends {A X X' Y : C}
    {i : A ⟶ X} {p : X ⟶ Y} {i' : A ⟶ X'} {p' : X' ⟶ Y}
    {hip : i ≫ p = 0} {hip' : i' ≫ p' = 0}
    (hS : E.conflation (ShortComplex.mk i p hip))
    (hT : E.conflation (ShortComplex.mk i' p' hip'))
    (a : X ⟶ X') (hai : i ≫ a = i') (hap : a ≫ p' = p) : IsIso a := by
  let hk := E.kernel (ShortComplex.mk i p hip) hS
  let hk' := E.kernel (ShortComplex.mk i' p' hip') hT
  let : Mono i := Fork.IsLimit.mono hk
  let : Mono i' := Fork.IsLimit.mono hk'
  have ha : Mono a := by
    apply Preadditive.mono_of_cancel_zero
    intro W f hf
    have hfp : f ≫ p = 0 := by rw [← hap, ← Category.assoc, hf, zero_comp]
    let g := hk.lift (KernelFork.ofι f hfp)
    have hgi : g ≫ i = f := hk.fac _ WalkingParallelPair.zero
    have hgi' : g ≫ i' = 0 := by rw [← hai, ← Category.assoc, hgi, hf]
    have hg : g = 0 := (cancel_mono i').1 (by simpa using hgi')
    rw [← hgi, hg, zero_comp]
  let : Mono a := ha
  let : HasPullback p p' := E.deflation.hasPullback p' (E.deflation_of_conflation hS)
  have hz : (pullback.fst p p' ≫ a - pullback.snd p p') ≫ p' = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc, hap, pullback.condition, sub_self]
  let b : pullback p p' ⟶ A := hk'.lift (KernelFork.ofι (pullback.fst p p' ≫ a - pullback.snd p p')
    hz)
  have hbi : b ≫ i' = pullback.fst p p' ≫ a - pullback.snd p p' := hk'.fac _
    WalkingParallelPair.zero
  let c : pullback p p' ⟶ X := pullback.fst p p' - b ≫ i
  have hca : c ≫ a = pullback.snd p p' := by
    dsimp only [c]
    rw [Preadditive.sub_comp, Category.assoc, hai, hbi, sub_sub_cancel]
  have hc : E.deflation (c ≫ a) := by
    rw [hca]
    exact E.deflation.pullback_snd p p' (E.deflation_of_conflation hS)
  have hda : E.deflation a := E.deflation_of_comp_of_isKernel c a (by simp)
    (kernel.isLimitConeZeroCone a) hc
  exact E.isIso_of_deflation_of_mono a hda

/-- A morphism of conflations which is the identity on kernels gives a
pullback square of the two cokernel maps. -/
lemma isPullback_of_conflations_same_kernel {A X Y B D : C}
    {i : A ⟶ X} {p : X ⟶ Y} {j : A ⟶ B} {r : B ⟶ D}
    {hip : i ≫ p = 0} {hjr : j ≫ r = 0}
    (hS : E.conflation (ShortComplex.mk i p hip))
    (hT : E.conflation (ShortComplex.mk j r hjr))
    (q : X ⟶ B) (f : Y ⟶ D) (hiq : i ≫ q = j) (hpf : p ≫ f = q ≫ r) :
    IsPullback q p r f := by
  let : HasPullback r f := E.deflation.hasPullback f (E.deflation_of_conflation hT)
  let a := pullback.lift q p hpf.symm
  have hpb := E.pullbackConflation_mem hT f
  have hai : i ≫ a = (pullbackConflation Y f (S := ShortComplex.mk j r hjr)).f := by
    apply pullback.hom_ext <;> simp [a, hiq, hip]
  have hap : a ≫ pullback.snd r f = p := by simp [a]
  let : IsIso a := E.isIso_of_conflations_fixed_ends hS hpb a hai hap
  exact IsPullback.of_iso_pullback ⟨hpf.symm⟩ (asIso a) (by simp [a]) (by simp [a])

/-- In a pullback square, composing the kernel of the upper projection with
the other projection produces an actual kernel of the lower map. -/
def kernelForkIsLimitOfIsPullback {K X B Y D : C} {k : K ⟶ X} {q : X ⟶ B}
    {p : X ⟶ Y} {r : B ⟶ D} {f : Y ⟶ D}
    (sq : IsPullback q p r f) (hkq : k ≫ q = 0)
    (hk : IsLimit (KernelFork.ofι k hkq)) :
    IsLimit (KernelFork.ofι (k ≫ p) (show (k ≫ p) ≫ f = 0 by
      rw [Category.assoc, ← sq.w, ← Category.assoc, hkq, zero_comp])) := by
  let : Mono k := Fork.IsLimit.mono hk
  let liftX {W : C} (a : W ⟶ Y) (ha : a ≫ f = 0) : W ⟶ X :=
    sq.lift 0 a (by simpa using ha.symm)
  have liftX_q {W : C} (a : W ⟶ Y) (ha : a ≫ f = 0) : liftX a ha ≫ q = 0 := by
    simp [liftX]
  have liftX_p {W : C} (a : W ⟶ Y) (ha : a ≫ f = 0) : liftX a ha ≫ p = a := by
    simp [liftX]
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} (a : W ⟶ Y) ha => hk.lift (KernelFork.ofι (liftX (W := W) a ha) (liftX_q a ha))) ?_ ?_
  · intro W a ha
    rw [← Category.assoc]
    have hfac : hk.lift (KernelFork.ofι (liftX (W := W) a ha) (liftX_q a ha)) ≫ k =
        liftX a ha := hk.fac _ WalkingParallelPair.zero
    rw [hfac]
    exact liftX_p a ha
  · intro W a ha m hm
    apply (cancel_mono k).1
    change m ≫ k = hk.lift (KernelFork.ofι (liftX (W := W) a ha) (liftX_q a ha)) ≫ k
    have hfac : hk.lift (KernelFork.ofι (liftX (W := W) a ha) (liftX_q a ha)) ≫ k =
        liftX a ha := hk.fac _ WalkingParallelPair.zero
    rw [hfac]
    apply sq.hom_ext
    · simp [Category.assoc, hkq, liftX_q]
    · simpa only [Category.assoc, liftX_p] using hm

/-- The exact-category quotient-of-quotients diagram. Both vertical maps are
deflations, so the kernel of the middle one embeds admissibly in the quotient. -/
lemma special_deflation_conflation {A X Y B D K : C}
    {i : A ⟶ X} {p : X ⟶ Y} {q : X ⟶ B} {r : B ⟶ D} {k : K ⟶ X}
    {hip : i ≫ p = 0} {hir : (i ≫ q) ≫ r = 0} {hkq : k ≫ q = 0}
    (hS : E.conflation (ShortComplex.mk i p hip))
    (hT : E.conflation (ShortComplex.mk (i ≫ q) r hir))
    (hK : E.conflation (ShortComplex.mk k q hkq)) :
    ∃ (f : Y ⟶ D) (h : (k ≫ p) ≫ f = 0),
      p ≫ f = q ≫ r ∧ E.conflation (ShortComplex.mk (k ≫ p) f h) := by
  let hc := E.cokernel (ShortComplex.mk i p hip) hS
  let f : Y ⟶ D := hc.desc (CokernelCofork.ofπ (q ≫ r) (by simpa only [Category.assoc] using hir))
  have hpf : p ≫ f = q ≫ r := hc.fac _ WalkingParallelPair.one
  have sq := E.isPullback_of_conflations_same_kernel hS hT q f rfl hpf
  have hz : (k ≫ p) ≫ f = 0 := by
    rw [Category.assoc, hpf, ← Category.assoc, hkq, zero_comp]
  have hf : E.deflation (p ≫ f) := by
    rw [hpf]
    exact E.deflation_comp q r (E.deflation_of_conflation hK) (E.deflation_of_conflation hT)
  have hker := kernelForkIsLimitOfIsPullback sq hkq (E.kernel _ hK)
  have hdf := E.deflation_of_comp_of_isKernel p f hz hker hf
  exact ⟨f, hz, hpf, E.conflation_of_isKernel hz hker hdf⟩

/-- Elementary denominator straightening: a weak deflation can be preceded by
an inflation with cokernel in the subcategory so that its composite is another
such inflation. Only the special axiom and admissible quotient closure enter. -/
lemma RightSpecial.straighten_deflation (A : ObjectProperty C)
    (hA : E.RightSpecial A) (hquot : E.IsClosedUnderAdmissibleQuotients A)
    {X Y : C} (p : X ⟶ Y) (hp : E.deflationWithKernel A p) :
    ∃ (K : C) (j : K ⟶ X),
      E.inflationWithCokernel A j ∧ E.inflationWithCokernel A (j ≫ p) := by
  obtain ⟨A₀, i, hip, hS, hA₀⟩ := hp
  obtain ⟨B, hB, q, hq, hiq⟩ := hA i hA₀ (E.inflation_of_conflation hS)
  obtain ⟨D, r, hir, hT⟩ := hiq
  obtain ⟨K, j, hjq, hK⟩ := hq
  obtain ⟨f, h, _, hc⟩ := E.special_deflation_conflation hS hT hK
  exact ⟨K, j, ⟨B, q, hjq, hK, hB⟩,
    ⟨D, f, h, hc, hquot r (E.deflation_of_conflation hT) hB⟩⟩

end CategoryTheory.ExactCategory.ExactStructure

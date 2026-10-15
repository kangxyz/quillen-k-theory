/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.FlagMaps
public import Quillen.Waldhausen.QuillenComparison.FlagPullback

/-! # Pullback of admissible flags preserves their interval quotients

The pullback of a kernel is the kernel of the composite. With an admissible
epimorphism this composite is again a deflation, so its original cokernel
object is the actual quotient of the pulled-back inclusion.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- A pullback of an actual kernel computes the kernel of the composite. -/
def pullbackKernelComposite {P A B K Q : C} {a : K ⟶ P} {v : K ⟶ A}
    {p : P ⟶ B} {i : A ⟶ B} {q : B ⟶ Q}
    (sq : IsPullback a v p i) (w : i ≫ q = 0)
    (hi : IsLimit (KernelFork.ofι i w)) :
    IsLimit (KernelFork.ofι a (show a ≫ (p ≫ q) = 0 from by
      rw [← Category.assoc, sq.w, Category.assoc, w, comp_zero])) := by
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} f hf ↦ sq.lift f (hi.lift (KernelFork.ofι (f ≫ p) (by simpa [Category.assoc] using
      hf)))
      (by symm; exact hi.fac _ WalkingParallelPair.zero)) ?_ ?_
  · intro W f hf
    exact sq.lift_fst _ _ _
  · intro W f hf m hm
    apply sq.hom_ext
    · simpa using hm
    · apply (Fork.IsLimit.hom_ext hi)
      change (m ≫ v) ≫ i = _
      rw [Category.assoc, ← sq.w, ← Category.assoc, hm, sq.lift_snd]
      symm
      exact hi.fac _ WalkingParallelPair.zero

/-- A pullback of an admissible inclusion against a deflation has the same
actual quotient as the original inclusion. -/
theorem pullback_conflation_same_quotient {P A B K Q : C} {a : K ⟶ P} {v : K ⟶ A}
    {p : P ⟶ B} {i : A ⟶ B} {q : B ⟶ Q}
    (sq : IsPullback a v p i) (w : i ≫ q = 0)
    (hc : E.conflation (ShortComplex.mk i q w)) (hp : E.deflation p) :
    E.conflation (ShortComplex.mk a (p ≫ q) (show a ≫ (p ≫ q) = 0 from by
      rw [← Category.assoc, sq.w, Category.assoc, w, comp_zero])) :=
  E.conflation_of_isKernel _ (pullbackKernelComposite sq w (E.kernel _ hc))
    (E.deflation_comp p q hp (E.deflation_of_conflation hc))

/-- The canonical quotient transformation for a pullback flag is componentwise
an isomorphism, proved from exact-category kernel and cokernel properties. -/
theorem pullbackFlag_quotient_isIso {n : SimplexCategory} (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {P : C} (p : P ⟶ A.obj (Fin.last n.len)) (hp : E.deflation p)
    [∀ i : Fin (n.len + 1), HasPullback p (flagTopMap A i)] (ij : Interval n) :
    IsIso ((quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij) := by
  let sq := pullbackFlag_map_isPullback A p (homOfLE ij.2)
  let hc := flagQuotient_conflation E hA ij
  let hs := pullback_conflation_same_quotient E sq (flagQuotient_zero E hA ij) hc
    (pullbackFlagToOriginal_deflation E A p hp ij.1.2)
  let e := (flagQuotientIsCokernel E (pullbackFlag_inflation E A p hp hA)
    ij).coconePointUniqueUpToIso
    (E.cokernel _ hs)
  have he : (quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij = e.hom := by
    apply (cancel_epi (flagQuotient E (pullbackFlag A p) (pullbackFlag_inflation E A p hp hA) ij)).1
    rw [flagQuotient_quotientNatTrans]
    exact ((flagQuotientIsCokernel E (pullbackFlag_inflation E A p hp hA)
      ij).comp_coconePointUniqueUpToIso_hom
      (E.cokernel _ hs) WalkingParallelPair.one).symm
  rw [he]
  infer_instance

/-- The quotient rows of a flag and its admissible pullback are canonically isomorphic. -/
def pullbackFlagQuotientIso {n : SimplexCategory} (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {P : C} (p : P ⟶ A.obj (Fin.last n.len)) (hp : E.deflation p)
    [∀ i : Fin (n.len + 1), HasPullback p (flagTopMap A i)] :
    quotientDiagram E (pullbackFlag A p) (pullbackFlag_inflation E A p hp hA) ≅
      quotientDiagram E A hA := by
  letI (ij : Interval n) : IsIso ((quotientNatTrans E
      (pullbackFlag_inflation E A p hp hA) hA (pullbackFlagToOriginal A p)).app ij) :=
    pullbackFlag_quotient_isIso E A hA p hp ij
  exact NatIso.ofComponents
    (fun ij ↦ asIso ((quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij))
    (fun f ↦ (quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).naturality f)

end Quillen.Waldhausen.QuillenComparison

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.Comparison

/-! A semantic degree-zero consumer: the original coarse single map gives a
unique original term-category class over each coarse bounded-complex class.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance consumer_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

example
    (y : (boundedTermsNested P).coarse.K 0) :
    ∃! x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0,
      KMap (boundedTermsSingle_coarseExact P 0) 0 x = y := by
  have h := boundedTermsSingle_coarse_KMap_bijective P 0
  obtain ⟨x, hx⟩ := h.surjective y
  exact ⟨x, hx, fun z hz ↦ h.injective (hz.trans hx.symm)⟩
end Quillen.Waldhausen.GilletWaldhausen

namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
  (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

/-- All positive LES positions use the actual acyclic and change-of-weak KMaps. -/
example (n : ℕ) :
    ∃ δ : N.coarse.K (n + 1) →* (acyclicStructure N).K n,
      (KMap (changeWeak_exact N) (n + 1)).range = δ.ker ∧
      δ.range = (KMap (acyclicInclusion_exact N) n).ker ∧
      (KMap (acyclicInclusion_exact N) n).range = (KMap (changeWeak_exact N) n).ker := by
  let h := canonicalFiberMap_isWeakHomotopyEquivalence N he D hs
  exact ⟨changeWeakConnectingHom N h n, changeWeak_positiveLongExactSequence_of_weak N h n⟩

/-- The genuine fiber group equivalence still projects to the original inclusion. -/
example (n : ℕ) :
    ∃ e : (acyclicStructure N).K n ≃*
      HomotopyGroup.Pi (n + 1) (HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint)
        (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
          V.kBasepoint (changeWeakMap_basepoint N)),
      (piMap n (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
        (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).comp
          e.toMonoidHom = KMap (acyclicInclusion_exact N) n := by
  refine ⟨MulEquiv.ofBijective (canonicalFiberKMap N n)
    (canonicalFiberKMap_bijective_of_weak N
      (canonicalFiberMap_isWeakHomotopyEquivalence N he D hs) n), ?_⟩
  exact canonicalFiberKMap_projection N n
end Quillen.Waldhausen.Fibration

namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance forwardMap_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The produced equivalence retains the exact original single-insertion map. -/
example (n : ℕ) :
    (boundedTermsSingleCoarseKEquiv P n).toMonoidHom =
      KMap (boundedTermsSingle_coarseExact P 0) n :=
  boundedTermsSingleCoarseKEquiv_coe P n
end Quillen.Waldhausen.GilletWaldhausen

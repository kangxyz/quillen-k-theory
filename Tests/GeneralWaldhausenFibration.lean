/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.GeneralComparison

/-! Genuine mixed-universe consumers of the unchanged original maps. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
  (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

example (n : ℕ) :
    ∃ δ : N.coarse.K (n + 1) →* (acyclicStructure N).K n,
      (KMap (changeWeak_exact N) (n + 1)).range = δ.ker ∧
      δ.range = (KMap (acyclicInclusion_exact N) n).ker ∧
      (KMap (acyclicInclusion_exact N) n).range = (KMap (changeWeak_exact N) n).ker := by
  let h := canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs
  exact ⟨changeWeakConnectingHom N h n, changeWeak_positiveLongExactSequence_of_weak N h n⟩
end Quillen.Waldhausen.Fibration

namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance genericConsumer_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

example (y : (boundedTermsNested P).coarse.K 0) :
    ∃! x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0,
      KMap (boundedTermsSingle_coarseExact P 0) 0 x = y := by
  have h := boundedTermsSingle_coarse_KMap_bijective_general P 0
  obtain ⟨x, hx⟩ := h.surjective y
  exact ⟨x, hx, fun z hz ↦ h.injective (hz.trans hx.symm)⟩

example (n : ℕ) :
    (boundedTermsSingleCoarseKEquivGeneral P n).toMonoidHom =
      KMap (boundedTermsSingle_coarseExact P 0) n :=
  boundedTermsSingleCoarseKEquivGeneral_coe P n
end Quillen.Waldhausen.GilletWaldhausen

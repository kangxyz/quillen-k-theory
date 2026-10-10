/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Waldhausen.Fibration.GlobalComparison
import Quillen.Waldhausen.GilletWaldhausen.FibrationQuotient
import Quillen.Waldhausen.Fibration.ComplexExtension

/-! # Gillet-Waldhausen for bounded complexes in a small abelian category

The original identity-cone cylinder and actual global fibration identify the
original degree-zero single insertion with a K-equivalence in every degree,
including zero. The property contains zero and is closed under isomorphisms,
extensions and kernels. Smallness is explicit; this module does not infer
cross-universe or scheme comparison from a chosen small presentation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.Waldhausen.GilletWaldhausen
open Fibration
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]
local instance smallAssembly_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

omit [(abelianExactStructure A).IsKernelClosed P] in
/-- The unchanged bounded-complex cylinder supplies all structural inputs. -/
theorem boundedTerms_canonicalFiberMap_weak_of_totalComparisons
    (hN : IsWeakHomotopyEquivalence (RelativeRows.totalTailFiberComparison (boundedTermsNested P)))
    (hA : IsWeakHomotopyEquivalence (RelativeRows.totalTailFiberComparison
      (AllWeak.nested (acyclicStructure (boundedTermsNested P))))) :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedTermsNested P)) := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact AllWeak.canonicalFiberMap_weak_of_totalComparisons (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1)) hN hA

/-- Conditional comparison on the exact original coarse single KMap.
This statement is deliberately SmallCategory; it makes no scheme-universe claim. -/
theorem boundedTermsSingle_coarse_KMap_bijective_of_totalComparisons
    (hN : IsWeakHomotopyEquivalence (RelativeRows.totalTailFiberComparison (boundedTermsNested P)))
    (hA : IsWeakHomotopyEquivalence (RelativeRows.totalTailFiberComparison
      (AllWeak.nested (acyclicStructure (boundedTermsNested P))))) (n : ℕ) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_weak_of_totalComparisons P hN hA) n
end Quillen.Waldhausen.GilletWaldhausen

namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The original bounded-complex canonical fiber comparison. -/
theorem boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap (boundedTermsNested P)) :=
  boundedTerms_canonicalFiberMap_weak_of_totalComparisons P
    (Fibration.RelativeRows.totalTailFiberComparison_isWeakHomotopyEquivalence (boundedTermsNested P))
    (Fibration.RelativeRows.totalTailFiberComparison_isWeakHomotopyEquivalence
      (Fibration.AllWeak.nested (Fibration.acyclicStructure (boundedTermsNested P))))

variable [(abelianExactStructure A).IsKernelClosed P]
local instance theorem_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Gillet-Waldhausen bijectivity for the exact original degree-zero single KMap.
The smallness restriction is explicit; no cross-universe application is inferred. -/
theorem boundedTermsSingle_coarse_KMap_bijective (n : ℕ) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence P) n

/-- The equivalence has the original degree-zero single KMap as forward map. -/
def boundedTermsSingle_coarse_KEquiv (n : ℕ) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n ≃*
      (boundedTermsNested P).coarse.K n :=
  boundedTermsSingle_coarse_KEquiv_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence P) n

@[simp] theorem boundedTermsSingle_coarse_KEquiv_toMonoidHom (n : ℕ) :
    (boundedTermsSingle_coarse_KEquiv P n).toMonoidHom =
      KMap (boundedTermsSingle_coarseExact P 0) n := rfl
end Quillen.Waldhausen.GilletWaldhausen

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.Waldhausen.Fibration.GeneralComparison
import Quillen.Waldhausen.GilletWaldhausen.FibrationQuotient
import Quillen.Waldhausen.Fibration.ComplexExtension

/-! # Gillet-Waldhausen with the original object and hom universes

The genuine bounded-complex cylinder and general-universe global fibration
give a K-equivalence on the original degree-zero single-insertion map in
every degree, including zero. The term property contains zero and is closed
under isomorphisms, extensions and kernels. The precise abelian ambient
category and all actual maps remain unchanged.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.GilletWaldhausen
open Fibration
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The unchanged bounded-complex canonical fiber map is weak in the original universes. -/
theorem boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedTermsNested P)) := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1))

variable [(abelianExactStructure A).IsKernelClosed P]
local instance generalAssembly_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The exact original coarse-single KMap is bijective in every degree, including zero. -/
theorem boundedTermsSingle_coarse_KMap_bijective_general (n : ℕ) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general P) n

/-- The general-universe equivalence retains the original coarse-single forward map. -/
def boundedTermsSingle_coarse_KEquiv_general (n : ℕ) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n ≃*
      (boundedTermsNested P).coarse.K n :=
  boundedTermsSingle_coarse_KEquiv_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general P) n

@[simp] theorem boundedTermsSingle_coarse_KEquiv_general_toMonoidHom (n : ℕ) :
    (boundedTermsSingle_coarse_KEquiv_general P n).toMonoidHom =
      KMap (boundedTermsSingle_coarseExact P 0) n := rfl
end Quillen.Waldhausen.GilletWaldhausen

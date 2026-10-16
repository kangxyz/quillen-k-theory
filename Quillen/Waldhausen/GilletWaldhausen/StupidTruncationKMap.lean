/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationFixedBounds
public import Quillen.Waldhausen.Functoriality.KMap

/-! # Actual K-map endpoints of each bounded-term brutal filtration

The original restricted truncation functors have the original inclusion K-map
below the specified lower term bound and the trivial K-map above the specified
upper bound. The maps use canonical zero rebasing, via the proved natural
isomorphisms and the original public KMap API. Only isomorphism weak models
are used, and no uniform bound on the whole bounded-complex category is chosen.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The original restricted map is precisely the composite of the two original K-maps. -/
theorem fixedTermsStupidTruncGE_KMap_comp (a b n : ℤ) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b n).waldhausenExact k =
      (KMap (boundedTermsStupidTruncGEExactFunctor P n).waldhausenExact k).comp
        (KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k) :=
  (KMap_comp_KMap _ _ k).symm

/-- The genuine lower endpoint has exactly the original stratum-inclusion K-map. -/
theorem fixedTermsStupidTruncGE_KMap_inclusion (a b n : ℤ) (hn : n ≤ a) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b n).waldhausenExact k =
      KMap (fixedTermsInclusionExactFunctor P a b).waldhausenExact k :=
  KMap_eq_of_iso _ _ (fixedTermsStupidTruncGEIdentityIso P a b n hn) k

/-- The genuine upper endpoint has the trivial original normalized K-map. -/
theorem fixedTermsStupidTruncGE_KMap_zero (a b n : ℤ) (hn : b < n) (k : ℕ) :
    KMap (fixedTermsStupidTruncGEExactFunctor P a b n).waldhausenExact k = 1 := by
  have he := KMap_eq_of_iso
    (fixedTermsStupidTruncGEExactFunctor P a b n).waldhausenExact
    (zeroFunctor_isExact (ofExactCategory (fixedTermsExactStructure P a b))
      (ofExactCategory (boundedTermsExactStructure P)))
    (fixedTermsStupidTruncGEZeroIso P a b n hn) k
  exact he.trans (KMap_zeroFunctor _ _ k)

end Quillen.Waldhausen.GilletWaldhausen

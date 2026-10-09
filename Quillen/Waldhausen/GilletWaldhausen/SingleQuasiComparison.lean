import Quillen.Waldhausen.GilletWaldhausen.GlobalEulerReduction
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels

/-! # The original single-complex map and change of weak equivalences

The same original single functor is exact into the genuine quasi-isomorphism
model. Its original normalized KMap is exactly the composite of the fine
single KMap with the actual change-of-weak-equivalences KMap. This is a map
identification, not a Gillet–Waldhausen equivalence or fibration assertion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance singleQuasiComparison_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The same actual original single functor is exact into genuine quasi-isomorphisms. -/
theorem boundedTermsSingle_coarseExact (n : ℤ) :
    IsExact (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).cof
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).weq
      (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
      (boundedTermsSingleFunctor P n) where
  zero h := (boundedTermsSingleExactFunctor P n).waldhausenExact.zero h
  cofibration f h := (boundedTermsSingleExactFunctor P n).waldhausenExact.cofibration f h
  weak f h := (complexSubcategory (boundedTerms P)).weq_iso _
    ((boundedTermsSingleExactFunctor P n).waldhausenExact.weak f h)
  pushout h hp := (boundedTermsSingleExactFunctor P n).waldhausenExact.pushout h hp

/-- The actual coarse single KMap factors through the original fine single KMap
and the actual identity change-of-weak-equivalences functor. -/
theorem boundedTermsSingle_coarse_KMap (n : ℤ) (k : ℕ) :
    KMap (boundedTermsSingle_coarseExact P n) k =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k).comp
        (KMap (boundedTermsSingleExactFunctor P n).waldhausenExact k) := by
  have he := KMap_eq_of_iso
    ((boundedTermsSingleExactFunctor P n).waldhausenExact.comp
      (Fibration.changeWeak_exact (boundedTermsNested P)))
    (boundedTermsSingle_coarseExact P n) (Functor.rightUnitor (boundedTermsSingleFunctor P n)) k
  exact he.symm.trans (KMap_comp (boundedTermsSingleExactFunctor P n).waldhausenExact
    (Fibration.changeWeak_exact (boundedTermsNested P)) k)

/-- Pointwise the triangle consists of precisely the original public KMaps. -/
theorem boundedTermsSingle_coarse_KMap_apply (n : ℤ) (k : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (boundedTermsSingle_coarseExact P n) k x =
      KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k
        (KMap (boundedTermsSingleExactFunctor P n).waldhausenExact k x) :=
  DFunLike.congr_fun (boundedTermsSingle_coarse_KMap P n k) x

end Quillen.Waldhausen.GilletWaldhausen

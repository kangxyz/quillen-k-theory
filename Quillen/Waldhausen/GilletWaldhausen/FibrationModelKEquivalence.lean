import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-! # The original bounded-acyclic model identification on K-theory

This changes only two presentations of the same actual fine acyclic category.
It does not identify that category with the homotopy fiber of a change of weak
classes. The latter fibration theorem is a separate obligation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual identity-on-complexes exact equivalence, on the original K-groups. -/
def boundedAcyclicFiberKEquiv (n : ℕ) :
    (ofExactCategory (boundedAcyclicExactStructure P)).K n ≃*
      (Fibration.acyclicStructure (boundedTermsNested P)).K n :=
  KEquivOfExactEquivalence _ _ (boundedAcyclicFiberEquivalence P)
    (boundedAcyclicToFiberObjects_exact P) (fiberObjectsToBoundedAcyclic_exact P) n

/-- The forward map is exactly the original identity-on-complexes K-map. -/
@[simp] theorem boundedAcyclicFiberKEquiv_toMonoidHom (n : ℕ) :
    (boundedAcyclicFiberKEquiv P n).toMonoidHom = KMap (boundedAcyclicToFiberObjects_exact P) n := rfl

/-- The inverse is exactly the original inverse-presentation K-map. -/
@[simp] theorem boundedAcyclicFiberKEquiv_symm_toMonoidHom (n : ℕ) :
    (boundedAcyclicFiberKEquiv P n).symm.toMonoidHom = KMap (fiberObjectsToBoundedAcyclic_exact P) n := rfl

/-- After the actual fiber-object inclusion, the original bounded-acyclic
inclusion K-map is recovered exactly. -/
theorem boundedAcyclicFiberKEquiv_inclusion (n : ℕ) :
    (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n).comp
      (boundedAcyclicFiberKEquiv P n).toMonoidHom =
        KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact n := by
  rw [boundedAcyclicFiberKEquiv_toMonoidHom, ← KMap_comp]

end Quillen.Waldhausen.GilletWaldhausen

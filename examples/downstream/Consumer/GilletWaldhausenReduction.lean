/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.GlobalEulerReduction
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KernelClosure

/-! Original-map finite and global fine-model K-class reductions. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen
universe u v
namespace Consumer
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance reductionConsumerProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

theorem actual_bounded_term_stage (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k,
      KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x :=
  boundedTerms_KMap_jointlySurjective P k x

omit [(abelianExactStructure A).IsExtensionClosed P] in
theorem actual_original_single_map (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleFunctor P n).map f).hom =
      (HomologicalComplex.single A (ComplexShape.up ℤ) n).map f.hom := rfl

variable [(abelianExactStructure A).IsKernelClosed P]

theorem actual_acyclic_inclusion_injective (k : ℕ) :
    Function.Injective (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k) :=
  boundedAcyclicTermsInclusion_KMap_injective P k

theorem actual_global_unique_reduction (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃! p : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k p.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k p.2 = x :=
  boundedTerms_existsUnique_acyclic_single_zero P k x

theorem actual_global_K0_joint_kernel
    (d : (ofExactCategory (boundedAcyclicExactStructure P)).K 0)
    (c : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0)
    (h : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact 0 d *
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact 0 c = 1) : d = 1 ∧ c = 1 :=
  boundedTerms_acyclic_single_zero_eq_one P 0 d c h
end

theorem actual_scheme_global_reduction (X : AlgebraicGeometry.Scheme.{u}) (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure (SchemeSheaf.finiteLocallyFree X))).K k) :
    ∃! p : (ofExactCategory (boundedAcyclicExactStructure (SchemeSheaf.finiteLocallyFree X))).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure
          (abelianExactStructure X.Modules) (SchemeSheaf.finiteLocallyFree X))).K k,
      KMap (boundedAcyclicTermsExactInclusion (SchemeSheaf.finiteLocallyFree X)).waldhausenExact k
        p.1 *
        KMap (boundedTermsSingleExactFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X)
          0).waldhausenExact k p.2 = x :=
  boundedTerms_existsUnique_acyclic_single_zero.{u,u+1} (SchemeSheaf.finiteLocallyFree X) k x

end Consumer

import Quillen.Waldhausen.GilletWaldhausen.FineProductDecomposition
import Quillen.PerfectComplexes.SingleComparison
import Quillen.Scheme.VectorBundle.KernelClosure
import Lean.Util.CollectAxioms
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Waldhausen.GilletWaldhausen.FineProductDecomposition do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 34 do
    throwError "Expected 34 fine-product origins, found {count}"
  logInfo m!"Audited {count} fine-product origins; only standard3."

universe v u
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance fineProductAudit_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
-- The actual null composite and product map require no kernel closure.
example (k : ℕ) (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k
      (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x) = 1 :=
  boundedAcyclicTerms_changeWeak_KMap P k x
example (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    boundedTermsAcyclicSingleKMap P k x =
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k x.2 := rfl
example (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k
      (boundedTermsAcyclicSingleKMap P k x) = KMap (boundedTermsSingle_coarseExact P 0) k x.2 :=
  boundedTermsAcyclicSingleKMap_coarse P k x
variable [(abelianExactStructure A).IsKernelClosed P]
example (k : ℕ) :
    ((ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) ≃*
        (ofExactCategory (boundedTermsExactStructure P)).K k := boundedTermsAcyclicSingleKEquiv P k
example (k : ℕ) :
    (boundedTermsAcyclicSingleKEquiv P k).toMonoidHom = boundedTermsAcyclicSingleKMap P k := rfl
example (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    boundedTermsAcyclicSingleKEquiv P k x =
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k x.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k x.2 := rfl
example (k : ℕ) (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    boundedTermsAcyclicSingleKEquiv P k ((boundedTermsAcyclicSingleKEquiv P k).symm x) = x :=
  (boundedTermsAcyclicSingleKEquiv P k).apply_symm_apply x
example (k : ℕ)
    (x : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    (boundedTermsAcyclicSingleKEquiv P k).symm (boundedTermsAcyclicSingleKEquiv P k x) = x :=
  (boundedTermsAcyclicSingleKEquiv P k).symm_apply_apply x
example (x : (ofExactCategory (boundedAcyclicExactStructure P)).K 0) :
    boundedTermsAcyclicSingleKEquiv P 0 (x, 1) =
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact 0 x := by simp
example (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0) :
    boundedTermsAcyclicSingleKEquiv P 0 (1, x) =
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact 0 x := by simp
example (k : ℕ) :
    (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k).comp
      (boundedTermsAcyclicSingleKEquiv P k).toMonoidHom =
        (KMap (boundedTermsSingle_coarseExact P 0) k).comp (MonoidHom.snd _ _) :=
  boundedTermsAcyclicSingleKEquiv_coarse P k
example (k : ℕ) (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k x =
      KMap (boundedTermsSingle_coarseExact P 0) k ((boundedTermsAcyclicSingleKEquiv P k).symm x).2 := by
  have h := DFunLike.congr_fun (boundedTermsAcyclicSingleKEquiv_coarse P k)
    ((boundedTermsAcyclicSingleKEquiv P k).symm x)
  exact (congrArg (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k)
    ((boundedTermsAcyclicSingleKEquiv P k).apply_symm_apply x)).symm.trans h
end

-- Arbitrary schemes use the already proved ambient vector-bundle kernel closure.
noncomputable def strictFineProductKEquiv (X : AlgebraicGeometry.Scheme.{u}) (k : ℕ) :=
  boundedTermsAcyclicSingleKEquiv.{u,u+1} (SchemeSheaf.finiteLocallyFree X) k
#print axioms strictFineProductKEquiv

example (X : AlgebraicGeometry.Scheme.{u}) (k : ℕ)
    (d : (ofExactCategory (boundedAcyclicExactStructure (SchemeSheaf.finiteLocallyFree X))).K k)
    (c : (ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).K k) :
    KMap (Fibration.changeWeak_exact (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))) k
      (strictFineProductKEquiv X k (d, c)) = PerfectComplexes.vectorBundleSComparison X k c := by
  rw [PerfectComplexes.vectorBundleSComparison_eq_coarseSingle]
  exact boundedTermsAcyclicSingleKMap_coarse.{u,u+1} (SchemeSheaf.finiteLocallyFree X) k (d, c)

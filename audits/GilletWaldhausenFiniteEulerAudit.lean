import Quillen.Waldhausen.GilletWaldhausen.FiniteEulerReduction
import Quillen.Scheme.VectorBundle.KernelClosure
import Lean.Util.CollectAxioms
noncomputable section
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Waldhausen.GilletWaldhausen.FiniteEulerReduction do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 25 do
    throwError "Expected 25 finite Euler origins, found {count}"
  logInfo m!"Audited {count} finite Euler origins; only standard3."

universe v u
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance finiteEulerAudit_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
-- Pure bound transport and original single-coordinate maps need no kernel closure.
example (a b : ℤ) (m k : ℕ) (hb : b = a + (m : ℤ) - 1)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) (i : Fin m) :
    finiteTermKEquivWithUpper P a b m k hb x i =
      KMap (finiteTermEvaluationExact P a b (a + (i : ℤ))).waldhausenExact k x :=
  finiteTermKEquivWithUpper_apply P a b m k hb x i
example (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ)))).K k) (i : Fin (m + 1)) :
    finiteTermKEquivClosed P a m k x i =
      KMap (finiteTermEvaluationExact P a (a + (m : ℤ)) (a + (i : ℤ))).waldhausenExact k x :=
  finiteTermKEquivClosed_apply P a m k x i
example (a : ℤ) (m k : ℕ) (i : Fin (m + 1))
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    let := Additivity.KCommGroup
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
    finiteTermKEquivClosed P a m k
      (KMap (finiteTermSingleExact P a (a + (m : ℤ)) (a + (i : ℤ))
        (by omega) (by have := i.isLt; omega)).waldhausenExact k x) = Pi.mulSingle i x :=
  finiteTermKEquivClosed_single P a m k i x
variable [(abelianExactStructure A).IsKernelClosed P]
example (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k) :
    let := Additivity.KCommGroup
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)) k
    finiteTermKEquivClosed P a m k
      (KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k x) =
      FiniteAdjacentComplex.incidence
        ((ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) m
        (finiteCycleKEquiv P a m k x) := finiteTermKEquivClosed_incidence P a m k x
-- Literal original single and acyclic KMaps, with no group equivalence input.
example (a : ℤ) (m k : ℕ) (i : Fin (m + 1))
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ)))).K k) :
    ∃! p : (ofExactCategory (fixedAcyclicExactStructure P a (a + (m : ℤ)))).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (finiteAcyclicTermsExactInclusion P a (a + (m : ℤ))).waldhausenExact k p.1 *
        KMap (finiteTermSingleExact P a (a + (m : ℤ)) (a + (i : ℤ))
          (by omega) (by have := i.isLt; omega)).waldhausenExact k p.2 = x :=
  finiteTerm_existsUnique_acyclic_single P a m k i x
-- Empty disk tuple and the unique original term, explicitly in K₀.
example (a : ℤ) (x : (ofExactCategory (fixedTermsExactStructure P a (a + (0 : ℤ)))).K 0) :
    ∃! p : (ofExactCategory (fixedAcyclicExactStructure P a (a + (0 : ℤ)))).K 0 ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0,
      KMap (finiteAcyclicTermsExactInclusion P a (a + (0 : ℤ))).waldhausenExact 0 p.1 *
        KMap (finiteTermSingleExact P a (a + (0 : ℤ)) (a + ((0 : Fin 1) : ℤ))
          (by omega) (by omega)).waldhausenExact 0 p.2 = x :=
  finiteTerm_existsUnique_acyclic_single P a 0 0 0 x
end

-- Arbitrary schemes, using the proved ambient vector-bundle kernel closure.
theorem strictFiniteEulerReduction (X : AlgebraicGeometry.Scheme.{u}) (a : ℤ) (m k : ℕ)
    (i : Fin (m + 1))
    (x : (ofExactCategory (fixedTermsExactStructure (SchemeSheaf.finiteLocallyFree X)
      a (a + (m : ℤ)))).K k) :
    ∃! p : (ofExactCategory (fixedAcyclicExactStructure (SchemeSheaf.finiteLocallyFree X)
        a (a + (m : ℤ)))).K k ×
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure X.Modules)
        (SchemeSheaf.finiteLocallyFree X))).K k,
      KMap (finiteAcyclicTermsExactInclusion.{u,u+1} (SchemeSheaf.finiteLocallyFree X)
        a (a + (m : ℤ))).waldhausenExact k p.1 *
      KMap (finiteTermSingleExact (SchemeSheaf.finiteLocallyFree X) a (a + (m : ℤ))
        (a + (i : ℤ)) (by omega) (by have := i.isLt; omega)).waldhausenExact k p.2 = x :=
  finiteTerm_existsUnique_acyclic_single.{u,u+1} (SchemeSheaf.finiteLocallyFree X) a m k i x
#print axioms strictFiniteEulerReduction

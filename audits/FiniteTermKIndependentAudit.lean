import Quillen.Waldhausen.GilletWaldhausen.FiniteTermKEquivalence
-- The separately built earlier modules are deliberately imported too, to detect declaration collisions.
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsSSetColimit
import Quillen.Waldhausen.GilletWaldhausen.StupidTruncationKMap
import Quillen.Waldhausen.Cylinder.AmbientRelative
import Quillen.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic
import Quillen.PerfectComplexes.Strict
import Quillen.Waldhausen.GilletWaldhausen.CycleEvaluationSequence
import Quillen.Waldhausen.GilletWaldhausen.BoundedSSetColimit
import Quillen.Waldhausen.GilletWaldhausen.AdjacentTruncation
import Quillen.Waldhausen.GilletWaldhausen.FixedBounds
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let wanted := #[`Quillen.Waldhausen.GilletWaldhausen.FiniteTermFiltration,
    `Quillen.Waldhausen.GilletWaldhausen.FiniteTermEvaluation,
    `Quillen.Waldhausen.GilletWaldhausen.FiniteTermKFormula,
    `Quillen.Waldhausen.GilletWaldhausen.FiniteTermKEquivalence]
  let mut count : Nat := 0
  for origin in wanted do
    let mut subtotal : Nat := 0
    for (name, _) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless env.header.moduleNames[index.toNat]! == origin do continue
      count := count + 1
      subtotal := subtotal + 1
      let axioms ← collectAxioms name
      for dependency in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{origin}: {name} depends on unsupported assumption {dependency}"
      logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
    logInfo m!"ORIGIN_COUNT {origin}: {subtotal}"
  unless count == 111 do throwError "Expected 111 finite-term4 origins, got {count}"
  logInfo m!"Audited all {count} finite-term4 declaration origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.GilletWaldhausen
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
section Algebra
variable {A : Type u} [Category.{v} A] [Abelian A]
example {K : CochainComplex A ℤ} {a b : ℤ} (h : HasTermBounds K a b) (n : ℤ) :
    HasTermBounds (stupidTruncGE K n) a b := h.stupidTruncGE n
example {K : CochainComplex A ℤ} {a b : ℤ} (h : HasTermBounds K a b) (n : ℤ) :
    HasTermBounds ((stupidTruncGELayerFunctor n).obj K) a b := h.stupidLayer n
example (S : ShortComplex A) (hS : S.ShortExact) (n : ℤ) :
    (S.map (single A (ComplexShape.up ℤ) n)).ShortExact := singleTerm_shortExact S hS n
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
example (a b n : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteTermEvaluation P a b n).map f).hom = f.hom.hom.f n := rfl
example (a b n : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteTermTruncation P a b n).map f).hom.hom =
      HomologicalComplex.stupidTruncMap f.hom.hom (ComplexShape.embeddingUpIntGE n) := rfl
example (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((finiteTermSingle P a b n ha hb).map f).hom.hom =
      (single A (ComplexShape.up ℤ) n).map f.hom := rfl
example (a b n : ℤ) (hn : n ≤ a) (K : (fixedTermsBounds P a b).FullSubcategory) :
    (((finiteTermIdentityIso P a b n hn).hom.app K).hom.hom) = stupidTruncGEInclusion K.obj.obj n := rfl
example (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    finiteTermEvaluation P a b n ⋙ finiteTermSingle P a b n ha hb = finiteTermLayer P a b n :=
  finiteTermEvaluation_single P a b n ha hb
variable [(abelianExactStructure A).IsExtensionClosed P]
example (a b n : ℤ) : Additivity.IsCofibrationSequence
    (ofExactCategory (fixedTermsExactStructure P a b)) (ofExactCategory (fixedTermsExactStructure P a b))
    (finiteTermTransition P a b (by omega : n ≤ n + 1)) (finiteTermProjection P a b n) :=
  finiteTerm_isCofibrationSequence P a b n
example (a b : ℤ) (m : ℕ) (hm : b < a + (m : ℤ)) (k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
    x = ∏ i : Fin m, KMap (finiteTermLayerExact P a b (a + (i : ℤ))).waldhausenExact k x :=
  finiteTerm_KMap_layers P a b m hm k x
end Algebra

section KEquivalence
-- This is the actual compatible-universe contract, not a raw cross-universe claim.
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance finiteTermIndependentProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
example (a : ℤ) (m k : ℕ) :
    (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k ≃*
      (Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :=
  finiteTermKEquiv P a m k
example (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k) (i : Fin m) :
    finiteTermKEquiv P a m k x i = KMap (finiteTermEvaluationExact P a (a + (m : ℤ) - 1)
      (a + (i : ℤ))).waldhausenExact k x := rfl
-- Expand the inverse all the way to the literal product of original single-insertion KMaps.
example (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))) k
    (finiteTermKEquiv P a m k).symm x =
      ∏ i : Fin m, KMap (finiteTermSingleExact P a (a + (m : ℤ) - 1) (a + (i : ℤ))
        (by omega) (by have := i.isLt; omega)).waldhausenExact k (x i) := rfl
example (a : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a (a + (m : ℤ) - 1))).K k) :
    finiteTermReassemble P a m k (finiteTermEvaluationKMap P a m k x) = x :=
  finiteTermReassemble_evaluate P a m k x
example (a : ℤ) (m k : ℕ)
    (x : Fin m → (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k) :
    finiteTermEvaluationKMap P a m k (finiteTermReassemble P a m k x) = x :=
  finiteTermEvaluate_reassemble P a m k x
-- m=0: genuine empty-stratum groups are trivial in every degree, including k=0.
example (a : ℤ) (k : ℕ) (x : (ofExactCategory (fixedTermsExactStructure P a (a + (0 : ℤ) - 1))).K k) :
    x = 1 := by
  have h := finiteTerm_KMap_layers P a (a + (0 : ℤ) - 1) 0 (by omega) k x
  simpa using h
example (a : ℤ) (x : (ofExactCategory (fixedTermsExactStructure P a (a + (0 : ℤ) - 1))).K 0) :
    x = 1 := by
  have h := finiteTerm_KMap_layers P a (a + (0 : ℤ) - 1) 0 (by omega) 0 x
  simpa using h
example (a b : ℤ) {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    (ofExactCategory (fixedTermsExactStructure P a b)).weq f ↔ IsIso f := Iff.rfl
end KEquivalence

-- The geometric consumer uses actual scheme sheaves without regular/noetherian/resolution hypotheses.
noncomputable def finiteTermSchemeConsumer (X : AlgebraicGeometry.Scheme.{u}) (a : ℤ) (m k : ℕ) :=
  finiteTermKEquiv.{u, u+1} (SchemeSheaf.finiteLocallyFree X) a m k
example (X : AlgebraicGeometry.Scheme.{u}) :
    boundedTerms (SchemeSheaf.finiteLocallyFree X) = PerfectComplexes.strictPerfect X := rfl
#print axioms finiteTermSchemeConsumer

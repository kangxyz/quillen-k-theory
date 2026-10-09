import Quillen.PerfectComplexes.SingleComparison
import Quillen.PerfectComplexes.QuillenComparison
import Lean.Util.CollectAxioms
noncomputable section
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless #[`Quillen.Waldhausen.GilletWaldhausen.SingleQuasiComparison,
      `Quillen.PerfectComplexes.SingleComparison].contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 8 do
    throwError "Expected 8 actual single-triangle origins, found {count}"
  logInfo m!"Audited {count} actual single-triangle origins; only standard3."

universe v u
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance singleComparisonAudit_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P
-- No kernel closure is present in the coarse-single map contract.
example (n : ℤ) :
    IsExact (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).cof
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).weq
      (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
      (boundedTermsSingleFunctor P n) := boundedTermsSingle_coarseExact P n
example (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleFunctor P n).map f).hom =
      (HomologicalComplex.single A (ComplexShape.up ℤ) n).map f.hom := rfl
example (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) [IsIso f] :
    QuasiIso ((HomologicalComplex.single A (ComplexShape.up ℤ) n).map f.hom) :=
  (boundedTermsSingle_coarseExact P n).weak f (show IsIso f from inferInstance)
example (n : ℤ) (k : ℕ) :
    KMap (boundedTermsSingle_coarseExact P n) k =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) k).comp
        (KMap (boundedTermsSingleExactFunctor P n).waldhausenExact k) :=
  boundedTermsSingle_coarse_KMap P n k
example (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0) :
    KMap (boundedTermsSingle_coarseExact P 0) 0 x =
      KMap (Fibration.changeWeak_exact (boundedTermsNested P)) 0
        (KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact 0 x) :=
  boundedTermsSingle_coarse_KMap_apply P 0 0 x
end

open AlgebraicGeometry PerfectComplexes
example (X : Scheme.{u}) : boundedTerms (SchemeSheaf.finiteLocallyFree X) = strictPerfect X := rfl
example (X : Scheme.{u}) :
    vectorBundleInclusion X = boundedTermsSingleFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0 :=
  vectorBundleInclusion_eq_boundedTermsSingle X
example (X : Scheme.{u}) {M N : SchemeSheaf.FiniteLocallyFree X} (f : M ⟶ N) :
    ((vectorBundleInclusion X).map f).hom =
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map f.hom := rfl
example (X : Scheme.{u}) (k : ℕ) :
    vectorBundleSComparison X k =
      KMap (boundedTermsSingle_coarseExact.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0) k :=
  vectorBundleSComparison_eq_coarseSingle X k
example (X : Scheme.{u}) (k : ℕ) :
    vectorBundleSComparison X k =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))) k).comp
        (KMap (boundedTermsSingleExactFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0).waldhausenExact k) :=
  vectorBundleSComparison_eq_changeWeak_comp_fineSingle X k
-- The previously public scheme K-map retains its original Q/S conversion as well.
example (X : Scheme.{u}) (k : ℕ) (x : Quillen.Scheme.K X k) :
    vectorBundleToStrictKMap X k x =
      KMap (Fibration.changeWeak_exact (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))) k
        (KMap (boundedTermsSingleExactFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0).waldhausenExact k
          (vectorBundleQSEquiv X k x)) := by
  change vectorBundleSComparison X k (vectorBundleQSEquiv X k x) = _
  exact DFunLike.congr_fun (vectorBundleSComparison_eq_changeWeak_comp_fineSingle X k) _
#print axioms Quillen.PerfectComplexes.vectorBundleSComparison_eq_changeWeak_comp_fineSingle

-- Explicit original public K₀ homomorphism, including its actual Q/S conversion.
example (X : Scheme.{u}) :
    vectorBundleToStrictKMap X 0 =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))) 0).comp
        ((KMap (boundedTermsSingleExactFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0).waldhausenExact 0).comp
          (vectorBundleQSEquiv X 0).toMonoidHom) := by
  apply MonoidHom.ext
  intro x
  change vectorBundleSComparison X 0 (vectorBundleQSEquiv X 0 x) = _
  exact DFunLike.congr_fun (vectorBundleSComparison_eq_changeWeak_comp_fineSingle X 0) _

-- The same original map then composes with the already existing strict/local map.
example (X : Scheme.{u}) (x : Quillen.Scheme.K X 0) :
    vectorBundleToPerfectKMap X 0 x =
      strictToPerfectKMap X 0
        (KMap (Fibration.changeWeak_exact (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))) 0
          (KMap (boundedTermsSingleExactFunctor.{u,u+1} (SchemeSheaf.finiteLocallyFree X) 0).waldhausenExact 0
            (vectorBundleQSEquiv X 0 x))) := by
  change strictToPerfectKMap X 0 (vectorBundleSComparison X 0 (vectorBundleQSEquiv X 0 x)) = _
  exact congrArg (strictToPerfectKMap X 0)
    (DFunLike.congr_fun (vectorBundleSComparison_eq_changeWeak_comp_fineSingle X 0) _)

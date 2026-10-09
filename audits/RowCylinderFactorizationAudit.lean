import Quillen.Waldhausen.Fibration.Rows.ComplexFactorization
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.Rows.JointFactorization,
    `Quillen.Waldhausen.Fibration.Rows.ComplexFactorization]
  let mut counts : Array Nat := targets.map (fun _ ↦ 0)
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some target := targets.findIdx? (· == origin) | continue
    count := count + 1
    counts := counts.modify target (· + 1)
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless count == 72 && counts == #[57, 15] do
    throwError "Expected fixed 72 origins (57+15), found {count} with {counts}"
  logInfo m!"Audited all {count} original-row-cylinder declaration origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration
section Generic
open RowFactorization
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : JointData N) (n : SimplexCategory)
example : FunctorialFactorization (RowWeakEquivalences.coarseStructure N n) := factorization N D n
example (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((factorization N D n).inclusion.app f) :=
  (factorization N D n).cofibration f
example (f : Arrow (QuotientRows.Obj V n)) :
    (factorization N D n).inclusion.app f ≫ (factorization N D n).projection.app f = f.hom :=
  (factorization N D n).factorization f
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    N.coarse.weq (((factorization N D n).projection.app f).hom.app p) :=
  (factorization N D n).weak f p
example : IsExact (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).cof
    (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).weq
    (QuotientRows.waldhausenStructure V n).cof (QuotientRows.waldhausenStructure V n).weq
    (factorization N D n).middle := middle_exact N D n
example : MixedChainReplacement.PreservesFineSquares (RowWeakEquivalences.nested N n)
    (factorization N D n) := factorization_fineSquares N D n
example {m : SimplexCategory} (α : m ⟶ n) :
    (QuotientRows.reindex V α).mapArrow ⋙ middle N D m =
      middle N D n ⋙ QuotientRows.reindex V α := middle_reindex N D α
example (f : Arrow (QuotientRows.Obj V n)) :
    IsPushout ((QuotientRows.isZero V n).to_ f.left)
      ((QuotientRows.isZero V n).to_ f.right) ((first N D n).app f) ((second N D n).app f) :=
  endpoint_isPushout N D f
example [HasBinaryCoproducts (QuotientRows.Obj V n)] (f : Arrow (QuotientRows.Obj V n)) :
    f.left ⨿ f.right ≅ (source N D n).obj f := sourceCoproductIso N D f
example [HasBinaryCoproducts (QuotientRows.Obj V n)] (f : Arrow (QuotientRows.Obj V n)) :
    coprod.inl ≫ (sourceCoproductIso N D f).hom = (first N D n).app f := sourceCoproductIso_inl N D f
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).inclusion.app f).hom.app p) =
      D.inl.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).projection.app f).hom.app p) =
      D.projection.app (Arrow.mk (f.hom.hom.app p)) := rfl
example {f g : Arrow (QuotientRows.Obj V n)} (α : f ⟶ g) (p : Interval n) :
    (((factorization N D n).middle.map α).hom.app p) =
      (D.joint.map (((QuotientRows.arrowDiagram V n).map α).app p)).hom.right := rfl
example (F : ComposableArrows (QuotientRows.Obj V n) 0) :
    ((FunctorialFactorization.finiteReplacement (factorization N D n) 0).obj F).obj 0 = F.obj 0 :=
  FunctorialFactorization.finiteReplacement_obj_zero _ _ _
example [N.coarse.weq.HasTwoOutOfThreeProperty] :
    IsExact (ArrowCategory.waldhausenStructure (RowWeakEquivalences.coarseStructure N n)).cof
      (ArrowCategory.waldhausenStructure (RowWeakEquivalences.coarseStructure N n)).weq
      (RowWeakEquivalences.coarseStructure N n).cof (RowWeakEquivalences.coarseStructure N n).weq
      (middle N D n) := middle_coarse_exact N D n
example {m : SimplexCategory} (α : m ⟶ n) (f : Arrow (QuotientRows.Obj V n)) :
    (QuotientRows.reindex V α).map ((factorization N D n).inclusion.app f) =
      (factorization N D m).inclusion.app ((QuotientRows.reindex V α).mapArrow.obj f) := rfl
example {m : SimplexCategory} (α : m ⟶ n) (f : Arrow (QuotientRows.Obj V n)) :
    (QuotientRows.reindex V α).map ((factorization N D n).projection.app f) =
      (factorization N D m).projection.app ((QuotientRows.reindex V α).mapArrow.obj f) := rfl
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((factorization N D n).middle.obj f).obj.obj p) =
      (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.right := rfl
end Generic
section Complexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧)) (n : SimplexCategory)
local notation "V" => ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) P)
example : RowFactorization.JointData (complexSubcategoryNested P) := complexJointData P hcone hshift
example (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((complexRowFactorization P hcone hshift n).inclusion.app f) :=
  complexRowFactorization_cof P hcone hshift f
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((complexRowFactorization P hcone hshift n).inclusion.app f).hom.app p).hom =
      SplitFactorization.inclusion (f.hom.hom.app p).hom :=
  complexRowFactorization_inclusion_component P hcone hshift f p
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((complexRowFactorization P hcone hshift n).projection.app f).hom.app p).hom =
      SplitFactorization.projection (f.hom.hom.app p).hom := rfl
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    QuasiIso (((complexRowFactorization P hcone hshift n).projection.app f).hom.app p).hom :=
  complexRowFactorization_projection_quasi P hcone hshift f p
example : MixedChainReplacement.PreservesFineSquares (RowWeakEquivalences.nested (complexSubcategoryNested P) n)
    (complexRowFactorization P hcone hshift n) := complexRowFactorization_fineSquares P hcone hshift n
example : IsExact (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).cof
    (ArrowCategory.waldhausenStructure (QuotientRows.waldhausenStructure V n)).weq
    (QuotientRows.waldhausenStructure V n).cof (QuotientRows.waldhausenStructure V n).weq
    (complexRowFactorization P hcone hshift n).middle := complexRowFactorization_middle_exact P hcone hshift n
end Complexes
section BoundedAndScheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
example (n : SimplexCategory) : FunctorialFactorization
    (RowWeakEquivalences.coarseStructure (boundedTermsNested P) n) :=
  complexRowFactorization (boundedTerms P) (boundedTerms_mappingCone P)
    (fun _ h ↦ boundedTerms_shift P h 1) n
example (X : Scheme.{u}) (n : SimplexCategory) : FunctorialFactorization
    (RowWeakEquivalences.coarseStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)) n) :=
  complexRowFactorization (boundedTerms (SchemeSheaf.finiteLocallyFree X))
    (boundedTerms_mappingCone _) (fun _ h ↦ boundedTerms_shift _ h 1) n
end BoundedAndScheme
end Quillen.Waldhausen.Fibration

import Quillen.Waldhausen.Fibration.Rows.SecondEndpoint
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == `Quillen.Waldhausen.Fibration.Rows.SecondEndpoint do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 18 do throwError "Expected exactly 18 second-endpoint origins, found {count}"
  logInfo m!"Audited {count} original second-endpoint origins."

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Generic
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (D : RowFactorization.JointData N)
  (n : SimplexCategory)
example (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((RowFactorization.second N D n).app f) := RowFactorization.second_cof N D f
example (f : Arrow (QuotientRows.Obj V n)) :
    QuotientRows.cof V n ((RowFactorization.targetInclusion N D n).app f) :=
  RowFactorization.targetInclusion_cof N D f
example (f : Arrow (QuotientRows.Obj V n)) (p : Interval n) :
    (((RowFactorization.targetInclusion N D n).app f).hom.app p) =
      D.inr.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl
example (hs : RowFactorization.SecondEndpointSection N D) (f : Arrow (QuotientRows.Obj V n)) :
    (RowFactorization.targetInclusion N D n).app f ≫ (RowFactorization.projection N D n).app f =
      𝟙 f.right := RowFactorization.targetInclusion_projection N D hs f
example (hs : RowFactorization.SecondEndpointSection N D) [N.coarse.weq.HasTwoOutOfThreeProperty]
    (f : Arrow (QuotientRows.Obj V n)) :
    (RowWeakEquivalences.coarseStructure N n).weq ((RowFactorization.targetInclusion N D n).app f) :=
  RowFactorization.targetInclusion_weak N D hs f
example [N.coarse.weq.HasTwoOutOfThreeProperty] (f : Arrow (QuotientRows.Obj V n))
    (hf : (RowWeakEquivalences.coarseStructure N n).weq f.hom) :
    (RowWeakEquivalences.coarseStructure N n).weq ((RowFactorization.inclusion N D n).app f) :=
  RowFactorization.inclusion_weak N D f hf
example {f g : Arrow (QuotientRows.Obj V n)} (α : f ⟶ g) :
    α.right ≫ (RowFactorization.targetInclusion N D n).app g =
      (RowFactorization.targetInclusion N D n).app f ≫ (RowFactorization.middle N D n).map α :=
  (RowFactorization.targetInclusion N D n).naturality α
example (f : Arrow (QuotientRows.Obj V ⦋0⦌)) :
    QuotientRows.cof V ⦋0⦌ ((RowFactorization.targetInclusion N D ⦋0⦌).app f) :=
  RowFactorization.targetInclusion_cof N D f
end Generic
section Complexes
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
example : RowFactorization.SecondEndpointSection (complexSubcategoryNested P) (complexJointData P hcone hshift) :=
  complexJointData_secondEndpointSection P hcone hshift
example (n : SimplexCategory)
    (f : Arrow (QuotientRows.Obj (ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)) n)) :
    (complexRowTargetInclusion P hcone hshift n).app f ≫
      (complexRowFactorization P hcone hshift n).projection.app f = 𝟙 f.right :=
  complexRowTargetInclusion_projection P hcone hshift f
example (n : SimplexCategory)
    (f : Arrow (QuotientRows.Obj (ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)) n)) (p : Interval n) :
    (((complexRowTargetInclusion P hcone hshift n).app f).hom.app p).hom =
      (biprod.inr : (f.right.obj.obj p).obj ⟶ SplitFactorization.middle (f.hom.hom.app p).hom) :=
  complexRowTargetInclusion_component P hcone hshift f p
example (n : SimplexCategory)
    (f : Arrow (QuotientRows.Obj (ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)) n)) (p : Interval n) :
    QuasiIso ((((complexRowTargetInclusion P hcone hshift n).app f).hom.app p).hom) := by
  let : (complexSubcategoryNested P).coarse.weq.HasTwoOutOfThreeProperty := complexSubcategory_saturated P
  exact RowFactorization.targetInclusion_weak (complexSubcategoryNested P) (complexJointData P hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift) f p
end Complexes
section Scheme
attribute [local instance] Abelian.hasFiniteBiproducts
open GilletWaldhausen AlgebraicGeometry
example (X : Scheme.{u}) :
    RowFactorization.SecondEndpointSection
      (complexSubcategoryNested (boundedTerms (SchemeSheaf.finiteLocallyFree X)))
      (complexJointData (boundedTerms (SchemeSheaf.finiteLocallyFree X))
        (fun hK hL f ↦ boundedTerms_mappingCone _ hK hL f)
        (fun _ hK ↦ boundedTerms_shift _ hK 1)) :=
  complexJointData_secondEndpointSection _ _ _
end Scheme

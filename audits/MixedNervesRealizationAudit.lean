import Quillen.Waldhausen.Fibration.MixedNerves.RowRealization
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.Fibration.MixedNerves.Cylinder,
    `Quillen.Waldhausen.Fibration.MixedNerves.RowCylinder,
    `Quillen.Waldhausen.Fibration.MixedNerves.Realization,
    `Quillen.Waldhausen.Fibration.MixedNerves.RowRealization]
  let mut counts : Array Nat := targets.map (fun _ ↦ 0)
  let mut total : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[idx.toNat]!
    let some i := targets.findIdx? (· == origin) | continue
    counts := counts.modify i (· + 1)
    total := total + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "{origin}: {name} depends on unsupported {ax}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless total == 58 && counts == #[26, 9, 14, 9] do
    throwError "Expected fixed58 origins (26+9+14+9), found {total}: {counts}"
  logInfo m!"TOTAL_ORIGINS {total}: {counts}"
noncomputable section
open CategoryTheory CochainComplex
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.MixedNerves
section Structural
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (D : TrivialCofibrations.CylinderData V.cof N.coarse.weq)
  (hD : CylinderPreservesFineSquares N D) (k : SimplexCategory)
example : TrivialCofibrations.CylinderData (pointwiseCof V k) (pointwiseCoarse N k) :=
  chainCylinder N D hD k
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    (((chainCylinder N D hD k).middle.obj f).obj.obj i) = D.middle.obj (Arrow.mk (f.hom.hom.app i)) := rfl
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    ((chainCylinder N D hD k).inclusion.app f).hom.app i = D.inclusion.app (Arrow.mk (f.hom.hom.app i)) := rfl
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    ((chainCylinder N D hD k).target.app f).hom.app i = D.target.app (Arrow.mk (f.hom.hom.app i)) := rfl
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    ((chainCylinder N D hD k).projection.app f).hom.app i = D.projection.app (Arrow.mk (f.hom.hom.app i)) := rfl
example {f g : Arrow (FineChain V k)} (α : f ⟶ g) (i : Fin (k.len+1)) :
    ((chainCylinder N D hD k).middle.map α).hom.app i =
      D.middle.map (((chainArrowDiagram (V := V) k).map α).app i) := rfl
example {l : SimplexCategory} (α : k ⟶ l) (f : Arrow (FineChain V l)) :
    (fineReindex V α).map ((chainCylinder N D hD l).projection.app f) =
      (chainCylinder N D hD k).projection.app ((fineReindex V α).mapArrow.obj f) := rfl
example (f : Arrow (FineChain V k)) :
    (chainCylinder N D hD k).target.app f ≫ (chainCylinder N D hD k).projection.app f = 𝟙 f.right :=
  (chainCylinder N D hD k).target_projection f
example (f : Arrow (FineChain V k)) :
    (chainCylinder N D hD k).inclusion.app f ≫ (chainCylinder N D hD k).projection.app f = f.hom :=
  (chainCylinder N D hD k).factorization f
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    V.cof (((chainCylinder N D hD k).target.app f).hom.app i) :=
  (chainCylinder N D hD k).target_cof f i
example (f : Arrow (FineChain V k)) (i : Fin (k.len+1)) :
    N.coarse.weq (((chainCylinder N D hD k).projection.app f).hom.app i) :=
  (chainCylinder N D hD k).projection_weak f i
example (f : Arrow (FineChain V k)) {i j : Fin (k.len+1)} (a : i ⟶ j) :
    V.weq ((((chainCylinder N D hD k).middle.obj f).obj.map a)) :=
  ((chainCylinder N D hD k).middle.obj f).property a
example {l : SimplexCategory} (α : k ⟶ l) :
    (fineReindex V α).mapArrow ⋙ chainMiddle N D hD k = chainMiddle N D hD l ⋙ fineReindex V α :=
  chainMiddle_reindex N D hD α
example [N.coarse.weq.HasTwoOutOfThreeProperty] (f : Arrow (FineChain V k))
    (hf : pointwiseCoarse N k f.hom) :
    pointwiseCoarse N k ((chainCylinder N D hD k).inclusion.app f) :=
  (chainCylinder N D hD k).inclusion_weak f hf
example (f : Arrow (FineChain V (SimplexCategory.mk 0))) :
    ((chainCylinder N D hD (SimplexCategory.mk 0)).projection.app f).hom.app 0 =
      D.projection.app (Arrow.mk (f.hom.hom.app 0)) := rfl
end Structural
section RowData
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
  (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D)
  (n k : SimplexCategory)
example : TrivialCofibrations.CylinderData (pointwiseCof (QuotientRows.waldhausenStructure V n) k)
    (pointwiseCoarse (RowWeakEquivalences.nested N n) k) := rowChainCylinder N D hs n k
example (f : Arrow (FineChain (QuotientRows.waldhausenStructure V n) k))
    (i : Fin (k.len+1)) (p : Interval n) :
    (((rowChainCylinder N D hs n k).projection.app f).hom.app i).hom.app p =
      D.projection.app (Arrow.mk ((f.hom.hom.app i).hom.app p)) := rfl
end RowData
section Realized
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)
  (D : TrivialCofibrations.CylinderData V.cof N.coarse.weq)
  (hD : CylinderPreservesFineSquares N D) [N.coarse.weq.HasTwoOutOfThreeProperty]
example (k : SimplexCategory) :
    (horizontalClassifyingHomotopyEquiv N D hD k).toFun =
      (classifyingSpaceMap (horizontalInclusion N k)).hom := horizontalClassifyingHomotopyEquiv_toFun N D hD k
example : IsRealizationEquivalence (TheoremA.diagonalMap (chainInclusion N)) :=
  chainInclusion_isRealizationEquivalence N D hD
example : (chainInclusionRealizationHomotopyEquiv N D hD).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap (chainInclusion N))).hom := rfl
example : (horizontalRealizationHomotopyEquiv N D hD).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap (horizontalNerveInclusion N))).hom := rfl
example (J : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N J)
    (n : SimplexCategory) :
    (rowChainInclusionRealizationHomotopyEquiv N J hs n).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (chainInclusion (RowWeakEquivalences.nested N n)))).hom := rfl
end Realized
section ComplexData
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
open GilletWaldhausen
example (n k : SimplexCategory) :=
  complexRowChainCylinder (boundedTerms P) (boundedTerms_mappingCone P)
    (fun _ h ↦ boundedTerms_shift P h 1) n k
example (n k : SimplexCategory)
    (f : Arrow (FineChain (QuotientRows.waldhausenStructure
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ))
        (boundedTerms P))) n) k)) (i : Fin (k.len+1)) (p : Interval n) :
    QuasiIso ((((complexRowChainCylinder (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ h ↦ boundedTerms_shift P h 1) n k).projection.app f).hom.app i).hom.app p).hom :=
  ((complexRowChainCylinder (boundedTerms P) (boundedTerms_mappingCone P)
    (fun _ h ↦ boundedTerms_shift P h 1) n k).projection_weak f i) p
end ComplexData
section ComplexRealization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [SmallCategory A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
open GilletWaldhausen
example (n : SimplexCategory) :
    (complexRowChainInclusionRealizationHomotopyEquiv (boundedTerms P) (boundedTerms_mappingCone P)
      (fun _ h ↦ boundedTerms_shift P h 1) n).toFun =
    (SSet.toTop.map (TheoremA.diagonalMap
      (chainInclusion (RowWeakEquivalences.nested (complexSubcategoryNested (boundedTerms P)) n)))).hom := rfl
end ComplexRealization
end Quillen.Waldhausen.Fibration.MixedNerves

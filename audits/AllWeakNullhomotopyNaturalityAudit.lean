import Quillen.Waldhausen.Fibration.AllWeak.NullhomotopyNaturality
import Quillen.Waldhausen.GilletWaldhausen.FibrationModels
import Quillen.Waldhausen.Approximation.Properties
import Quillen.PerfectComplexes.SingleComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Waldhausen.SConstruction.WeakNaturalTransformationNaturality,
    `Quillen.Topology.Realization.HomotopyNaturality,
    `Quillen.Waldhausen.Fibration.AllWeak.NullhomotopyNaturality]
  let mut counts : Array Nat := #[0,0,0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some i := targets.idxOf? origin | continue
    counts := counts.modify i (· + 1)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing defining module {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  unless counts == #[4,1,2] do throwError "Unexpected origin counts {counts}"
  logInfo m!"Audited all original nullhomotopy-naturality origins: {counts}"
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open scoped Simplicial Topology
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section Cylinder
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {n m : SimplexCategory} {A B : Grid₂ n m ⥤ C}
example (η : A ⟶ B) (F : C ⥤ D) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ ⋙ F = nerveCylinderDiagram (whiskerRight η F) τ :=
  nerveCylinderDiagram_postcomp η F τ
end Cylinder
section Topology
variable {X X' Y Y' : SSet.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
  (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
  (a : X' ⟶ X) (b : Y ⟶ Y') (hs : a ▷ Δ[1] ≫ H.h ≫ b = H'.h)
example (t : unitInterval) (x : |X'|) :
    SSet.toTop.map b (realizationSimplicialHomotopy H (t,SSet.toTop.map a x)) =
      realizationSimplicialHomotopy H' (t,x) :=
  realizationSimplicialHomotopy_naturality H H' a b hs t x
end Topology
section Canonical
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
example : sSetMap (changeWeak_exact (AllWeak.nested (acyclicStructure N))) ▷ Δ[1] ≫
    weakNaturalTransformationCylinder (AllWeak.waldhausenStructure (acyclicStructure N))
      (AllWeak.waldhausenStructure (acyclicStructure N)) (zeroFunctor_isExact _ _) (IsExact.id _ _)
      (AllWeak.zeroToIdentity (acyclicStructure N)) (fun _ ↦ trivial) ≫
        sSetMap (AllWeak.acyclicInclusion_exact N) =
    weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) := AllWeak.acyclicCylinder_square N
example (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (AllWeak.contraction (acyclicStructure N)
        (t,changeWeakMap (AllWeak.nested (acyclicStructure N)) x)) = acyclicNullhomotopy N (t,x) :=
  AllWeak.contraction_acyclicNullhomotopy N t x
example (x : (acyclicStructure N).Delooping) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (AllWeak.contraction (acyclicStructure N)
        (0,changeWeakMap (AllWeak.nested (acyclicStructure N)) x)) =
      changeWeakMap N (acyclicInclusionMap N x) := by
  rw [AllWeak.contraction_acyclicNullhomotopy]
  exact (acyclicNullhomotopy N).map_zero_left x
example (x : (acyclicStructure N).Delooping) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (AllWeak.contraction (acyclicStructure N)
        (1,changeWeakMap (AllWeak.nested (acyclicStructure N)) x)) = N.coarse.kBasepoint := by
  rw [AllWeak.contraction_acyclicNullhomotopy]
  exact (acyclicNullhomotopy N).map_one_left x
example (t : unitInterval) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (AllWeak.contraction (acyclicStructure N)
        (t,changeWeakMap (AllWeak.nested (acyclicStructure N)) (acyclicStructure N).kBasepoint)) =
      N.coarse.kBasepoint := by
  rw [AllWeak.contraction_acyclicNullhomotopy]
  exact acyclicNullhomotopy_fixed_zero N t
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (canonicalFiberMap N x).1.2 t =
      deloopingMap (AllWeak.acyclicInclusion_exact N)
        (AllWeak.contraction (acyclicStructure N)
          (t,changeWeakMap (AllWeak.nested (acyclicStructure N)) x)) :=
  (AllWeak.contraction_acyclicNullhomotopy N t x).symm
end Canonical
section Scheme
open GilletWaldhausen AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
local instance nullhomotopySchemeSaturated (X : Scheme.{u}) :
    (boundedTermsNested (SchemeSheaf.finiteLocallyFree X)).coarse.weq.HasTwoOutOfThreeProperty :=
  complexSubcategory_saturated _
example (X : Scheme.{u}) (t : unitInterval)
    (x : (acyclicStructure (boundedTermsNested (SchemeSheaf.finiteLocallyFree X))).Delooping) :
    let N := boundedTermsNested (SchemeSheaf.finiteLocallyFree X)
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (AllWeak.contraction (acyclicStructure N)
        (t, changeWeakMap (AllWeak.nested (acyclicStructure N)) x)) = acyclicNullhomotopy N (t,x) := by
  let N := boundedTermsNested (SchemeSheaf.finiteLocallyFree X)
  let : N.coarse.weq.HasTwoOutOfThreeProperty := complexSubcategory_saturated _
  exact AllWeak.contraction_acyclicNullhomotopy N t x
end Scheme

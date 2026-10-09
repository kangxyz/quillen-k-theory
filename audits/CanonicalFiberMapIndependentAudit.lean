import Quillen.Waldhausen.Fibration.CanonicalFiberMap
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.Waldhausen.Fibration.CanonicalFiberMap
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless origin == target do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 24 do throwError "Expected 24 canonical fiber-map origins, got {count}"
  logInfo m!"Audited all {count} canonical fiber-map origins."

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.Waldhausen
open Quillen.Waldhausen.Fibration
universe u v
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

example (X : AcyclicCategory N) :
    (zeroToAcyclicInclusion N).app X = N.coarse.isZero.to_ X.obj := rfl
example (X : AcyclicCategory N) : N.coarse.weq ((zeroToAcyclicInclusion N).app X) := X.property
example : changeWeakMap N = (deloopingMap (changeWeak_exact N)).hom := rfl
example : acyclicInclusionMap N = (deloopingMap (acyclicInclusion_exact N)).hom := rfl
-- The nullhomotopy uses the actual reversed weak-transformation homotopy.
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    acyclicNullhomotopy N (t, x) =
      weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) (unitInterval.symm t, x) := rfl
example (t : unitInterval) :
    acyclicNullhomotopy N (t, (acyclicStructure N).kBasepoint) = N.coarse.kBasepoint :=
  acyclicNullhomotopy_fixed_zero N t
-- The actual path coordinate, endpoint conditions, and original projection.
example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (canonicalFiberMap N x).val.2 t = acyclicNullhomotopy N (t, x) := rfl
example (x : (acyclicStructure N).Delooping) :
    (canonicalFiberMap N x).val.2 0 = changeWeakMap N (acyclicInclusionMap N x) :=
  (canonicalFiberMap N x).property.1
example (x : (acyclicStructure N).Delooping) :
    (canonicalFiberMap N x).val.2 1 = N.coarse.kBasepoint := (canonicalFiberMap N x).property.2
example : (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint).comp
    (canonicalFiberMap N) = acyclicInclusionMap N := rfl
example : canonicalFiberMap N (acyclicStructure N).kBasepoint =
    HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N) := canonicalFiberMap_basepoint N
-- All n, with n=0 still the genuine fundamental-group K0 definition.
example (n : ℕ) :
    (piMap n (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).comp
      (canonicalFiberKMap N n) = KMap (acyclicInclusion_exact N) n := canonicalFiberKMap_projection N n
example :
    (piMap 0 (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).comp
      (canonicalFiberKMap N 0) = KMap (acyclicInclusion_exact N) 0 := canonicalFiberKMap_projection N 0
-- This is only the null-composite assertion on the two original K-homomorphisms.
example (n : ℕ) :
    (KMap (changeWeak_exact N) n).comp (KMap (acyclicInclusion_exact N) n) = 1 :=
  changeWeak_KMap_comp_acyclic N n
example (x : (acyclicStructure N).K 0) :
    KMap (changeWeak_exact N) 0 (KMap (acyclicInclusion_exact N) 0 x) = 1 :=
  DFunLike.congr_fun (changeWeak_KMap_comp_acyclic N 0) x

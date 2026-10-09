import Quillen.CategoryTheory.TheoremB.CompactMappingCylinderFibers
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let target := `Quillen.CategoryTheory.TheoremB.CompactMappingCylinderFibers
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[index.toNat]! == target do continue
    count := count + 1
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {name}: {axs}"
  unless count == 23 do throwError "Expected fixed23, found {count}"
  logInfo m!"FIXED23 PASSED all {count} compact mapping-cylinder fiber origins."
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open Quillen.TheoremB.CompactMappingCylinder
open scoped Topology unitInterval
universe u
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T) (t : T)
example : projection sq base = TheoremA.mappingCylinderProjection sq ≫ base := rfl
example (z : {m : M // projection sq base m = t}) :
    (collapseFiber sq base t z).val = TheoremA.mappingCylinderProjection sq z.val := rfl
example (z : {x : C // base x = t}) : (targetFiber sq base t z).val = c z.val := rfl
example (z : {a : A // (f ≫ base) a = t}) :
    (sourceFiber sq base t z).val = (TopCat.ι₀ ≫ l) z.val := rfl
example : (collapseFiberHomotopyEquiv sq base t).toFun = collapseFiber sq base t := rfl
example : (collapseFiberHomotopyEquiv sq base t).invFun = targetFiber sq base t := rfl
example : (collapseFiber sq base t).comp (sourceFiber sq base t) =
    HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t :=
  collapseFiber_sourceFiber sq base t
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CompactHomotopyExtensionLiftingProperty (sourceFiber sq base t) :=
  sourceFiber_compactHELP sq base t hf
example (hf : CompactHomotopyExtensionLiftingProperty
    (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t))
    (K D : TopCat.{u}) [CompactSpace K] [CompactSpace D]
    (i : K ⟶ D) (hi : TheoremA.homotopyExtensionProperty i)
    (a : C(K,{a : A // (f ≫ base) a = t}))
    (b : C(D,{m : M // projection sq base m = t}))
    (H : ((sourceFiber sq base t).comp a).Homotopy (b.comp i.hom)) :
    ∃ d : C(D,{a : A // (f ≫ base) a = t}),d.comp i.hom = a ∧
      ∃ V : ((sourceFiber sq base t).comp d).Homotopy b,
        ∀ s x,V (s,i x) = H (s,x) := sourceFiber_compactHELP sq base t hf K D i hi a b H

-- Exact retract and original factorization on arbitrary strict-fiber points.
example : (collapseFiber sq base t).comp (targetFiber sq base t) = ContinuousMap.id _ := by
  ext z
  exact ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_target sq) z.val
example (z : {a : A // (f ≫ base) a = t}) :
    (collapseFiber sq base t (sourceFiber sq base t z)).val = f z.val :=
  ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_start sq) z.val
example : ((targetFiber sq base t).comp (collapseFiber sq base t)).Homotopic
    (ContinuousMap.id _) := (collapseFiberHomotopyEquiv sq base t).left_inv
example (z : {m : M // projection sq base m = t}) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (collapseFiber sq base t) (x := z) rfl) :=
  (isWeakHomotopyEquivalence_of_homotopyEquiv
    (collapseFiberHomotopyEquiv sq base t)).homotopy_bijective z n
example (z : {m : M // projection sq base m = t}) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (collapseFiber sq base t) (x := z) rfl) :=
  (isWeakHomotopyEquivalence_of_homotopyEquiv
    (collapseFiberHomotopyEquiv sq base t)).homotopy_bijective z 0
example : IsEmpty {m : M // projection sq base m = t} ↔ IsEmpty {x : C // base x = t} := by
  constructor
  · intro h
    exact ⟨fun x ↦ h.false (targetFiber sq base t x)⟩
  · intro h
    exact ⟨fun x ↦ h.false (collapseFiber sq base t x)⟩

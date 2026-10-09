import Quillen.CategoryTheory.TheoremB.FiberwiseCylinderEquivalence
import Quillen.Topology.HomotopyFiber.StrictWeakTransport
import Quillen.Topology.HELP.TwoOfThree

/-! # Full compact HELP on the original mapping-cylinder strict fibers

The canonical target deformation is restricted to each actual strict fiber.
This gives an actual fiber homotopy equivalence for the collapse. Cancellation
then proves full compact HELP of the literal source inclusion on that fiber.
No interchange of a fiber with a pushout, or HLP of the cylinder, is assumed.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.TheoremB.CompactMappingCylinder
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

abbrev projection : M ⟶ T := TheoremA.mappingCylinderProjection sq ≫ base

/-- The literal collapse on the original strict fiber. -/
def collapseFiber (t : T) : C({m : M // projection sq base m = t},{x : C // base x = t}) :=
  ⟨fun z ↦ ⟨TheoremA.mappingCylinderProjection sq z.val,z.property⟩,by fun_prop⟩

/-- The literal target inclusion on the original strict fiber. -/
def targetFiber (t : T) : C({x : C // base x = t},{m : M // projection sq base m = t}) :=
  ⟨fun z ↦ ⟨c z.val,(ConcreteCategory.congr_hom
    (TheoremA.mappingCylinderProjection_target_assoc sq base) z.val).trans z.property⟩,
    by fun_prop⟩

/-- The literal source inclusion on the original strict fiber. -/
def sourceFiber (t : T) :
    C({a : A // (f ≫ base) a = t},{m : M // projection sq base m = t}) :=
  ⟨fun z ↦ ⟨(TopCat.ι₀ ≫ l) z.val,(ConcreteCategory.congr_hom
    (TheoremA.mappingCylinderProjection_start_assoc sq base) z.val).trans z.property⟩,
    by fun_prop⟩

@[simp] theorem collapseFiber_val (t : T) (z : {m : M // projection sq base m = t}) :
    (collapseFiber sq base t z).val = TheoremA.mappingCylinderProjection sq z.val := rfl
@[simp] theorem targetFiber_val (t : T) (z : {x : C // base x = t}) :
    (targetFiber sq base t z).val = c z.val := rfl
@[simp] theorem sourceFiber_val (t : T) (z : {a : A // (f ≫ base) a = t}) :
    (sourceFiber sq base t z).val = (TopCat.ι₀ ≫ l) z.val := rfl

/-- Restriction of the actual target SDR, with unchanged collapse/inclusion maps. -/
def collapseFiberHomotopyEquiv (t : T) :
    ContinuousMap.HomotopyEquiv {m : M // projection sq base m = t} {x : C // base x = t} where
  toFun := collapseFiber sq base t
  invFun := targetFiber sq base t
  left_inv := ⟨{
    toFun z := ⟨mappingCylinderTargetHomotopy sq (z.1,z.2.val),
      (mappingCylinderTargetHomotopy_over sq base z.1 z.2.val).trans z.2.property⟩
    continuous_toFun := by fun_prop
    map_zero_left z := Subtype.ext ((mappingCylinderTargetHomotopy sq).map_zero_left z.val)
    map_one_left z := Subtype.ext ((mappingCylinderTargetHomotopy sq).map_one_left z.val) }⟩
  right_inv := ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id _)).cast (by
    ext z
    exact (ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_target sq) z.val).symm) rfl⟩

@[simp] theorem collapseFiberHomotopyEquiv_toFun (t : T) :
    (collapseFiberHomotopyEquiv sq base t).toFun = collapseFiber sq base t := rfl
@[simp] theorem collapseFiberHomotopyEquiv_invFun (t : T) :
    (collapseFiberHomotopyEquiv sq base t).invFun = targetFiber sq base t := rfl

/-- Cancellation uses the actual original attaching-map strict fiber. -/
theorem collapseFiber_sourceFiber (t : T) :
    (collapseFiber sq base t).comp (sourceFiber sq base t) =
      HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t := by
  ext z
  exact ConcreteCategory.congr_hom (TheoremA.mappingCylinderProjection_start sq) z.val

/-- Full prescribed-boundary HELP for the original source inclusion at one
actual strict fiber, without any HLP assertion on the mapping cylinder. -/
theorem sourceFiber_compactHELP (t : T)
    (hf : CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (f ≫ base).hom base.hom f.hom rfl t)) :
    CompactHomotopyExtensionLiftingProperty (sourceFiber sq base t) := by
  have hcomp : CompactHomotopyExtensionLiftingProperty
      ((collapseFiber sq base t).comp (sourceFiber sq base t)) := by
    rw [collapseFiber_sourceFiber]
    exact hf
  exact hcomp.cancel_second (compactHELP_of_homotopyEquiv (collapseFiberHomotopyEquiv sq base t))

end Quillen.TheoremB.CompactMappingCylinder

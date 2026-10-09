import Quillen.CategoryTheory.TheoremB.CompactCollarFiberComparison

/-! # Original homotopy-fiber inputs for the finite collars

The two edge hypotheses are the literal maps of the original homotopy
fibers. Actual HLP of the three vertical maps transports them to the
strict edge fibers. All collar conclusions then use the proved geometric
height cases, retaining the original strict-to-homotopy-fiber maps.
-/
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.DoubleCylinder
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

def leftAttachingHomotopyFiberMap (y : A') :
    C(HomotopyFiber a.hom y,HomotopyFiber b.hom (f' y)) :=
  HomotopyFiber.map f.hom f'.hom (by
    ext x
    exact (ConcreteCategory.congr_hom wf x).symm) y

def rightAttachingHomotopyFiberMap (y : A') :
    C(HomotopyFiber a.hom y,HomotopyFiber c.hom (g' y)) :=
  HomotopyFiber.map g.hom g'.hom (by
    ext x
    exact (ConcreteCategory.congr_hom wg x).symm) y

@[simp] theorem leftAttachingHomotopyFiberMap_path (y : A') (x : HomotopyFiber a.hom y) :
    (leftAttachingHomotopyFiberMap a b wf y x).val.2 = f'.hom.comp x.val.2 := rfl
@[simp] theorem rightAttachingHomotopyFiberMap_path (y : A') (x : HomotopyFiber a.hom y) :
    (rightAttachingHomotopyFiberMap a c wg y x).val.2 = g'.hom.comp x.val.2 := rfl

theorem leftAttachingFiberMap_inclusion (y : A') :
    (HomotopyFiber.strictFiberInclusion b.hom (f' y)).comp (leftAttachingFiberMap a b wf y) =
      (leftAttachingHomotopyFiberMap a b wf y).comp (HomotopyFiber.strictFiberInclusion a.hom y) := rfl

theorem rightAttachingFiberMap_inclusion (y : A') :
    (HomotopyFiber.strictFiberInclusion c.hom (g' y)).comp (rightAttachingFiberMap a c wg y) =
      (rightAttachingHomotopyFiberMap a c wg y).comp (HomotopyFiber.strictFiberInclusion a.hom y) := rfl

theorem leftAttachingFiberMap_compactHELP (ha : HomotopyLiftingProperty a.hom)
    (hb : HomotopyLiftingProperty b.hom) (y : A')
    (hf : CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y)) :
    CompactHomotopyExtensionLiftingProperty (leftAttachingFiberMap a b wf y) := by
  have h := hf.comp (compactHELP_of_homotopyEquiv
    (HomotopyFiber.strictFiberHomotopyEquivOfLifting a.hom ha y))
  change CompactHomotopyExtensionLiftingProperty
    ((leftAttachingHomotopyFiberMap a b wf y).comp (HomotopyFiber.strictFiberInclusion a.hom y)) at h
  rw [← leftAttachingFiberMap_inclusion a b wf y] at h
  exact h.cancel_second (compactHELP_of_homotopyEquiv
    (HomotopyFiber.strictFiberHomotopyEquivOfLifting b.hom hb (f' y)))

theorem rightAttachingFiberMap_compactHELP (ha : HomotopyLiftingProperty a.hom)
    (hc : HomotopyLiftingProperty c.hom) (y : A')
    (hg : CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y)) :
    CompactHomotopyExtensionLiftingProperty (rightAttachingFiberMap a c wg y) := by
  have h := hg.comp (compactHELP_of_homotopyEquiv
    (HomotopyFiber.strictFiberHomotopyEquivOfLifting a.hom ha y))
  change CompactHomotopyExtensionLiftingProperty
    ((rightAttachingHomotopyFiberMap a c wg y).comp (HomotopyFiber.strictFiberInclusion a.hom y)) at h
  rw [← rightAttachingFiberMap_inclusion a c wg y] at h
  exact h.cancel_second (compactHELP_of_homotopyEquiv
    (HomotopyFiber.strictFiberHomotopyEquivOfLifting c.hom hc (g' y)))

/-- Full compact HELP for every original left collar strict-fiber inclusion,
from the original edge homotopy-fiber maps and genuine vertical fibrations. -/
theorem leftCollar_strictFiberInclusion_compactHELP_of_homotopyFibers
    (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hf : ∀ y : A',CompactHomotopyExtensionLiftingProperty (leftAttachingHomotopyFiberMap a b wf y))
    (cut : unitInterval) (hcut : 0 < cut) (y : LeftCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (leftCollarMap sq sq' a b c wf wg cut).hom y) :=
  leftCollar_strictFiberInclusion_compactHELP_of_edge sq sq' a b c wf wg cut hcut hb
    (fun z ↦ leftAttachingFiberMap_compactHELP a b wf ha hb z (hf z)) y

/-- The exact matching right collar statement. -/
theorem rightCollar_strictFiberInclusion_compactHELP_of_homotopyFibers
    (ha : HomotopyLiftingProperty a.hom) (hc : HomotopyLiftingProperty c.hom)
    (hg : ∀ y : A',CompactHomotopyExtensionLiftingProperty (rightAttachingHomotopyFiberMap a c wg y))
    (cut : unitInterval) (hcut : cut < 1) (y : RightCollar f' g' sq' cut) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictFiberInclusion (rightCollarMap sq sq' a b c wf wg cut).hom y) :=
  rightCollar_strictFiberInclusion_compactHELP_of_edge sq sq' a b c wf wg cut hcut hc
    (fun z ↦ rightAttachingFiberMap_compactHELP a c wg ha hc z (hg z)) y

end Quillen.DoubleCylinder

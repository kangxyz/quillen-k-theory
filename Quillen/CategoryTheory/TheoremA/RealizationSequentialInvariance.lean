import Quillen.CategoryTheory.TheoremA.SequentialHomotopyInvariance
import Quillen.CategoryTheory.TheoremA.RealizationCofibrationEquiv
import Quillen.CategoryTheory.TheoremA.RealizationColimitHomotopy
import Quillen.Topology.HomotopyFiber.SourceEquivalence

/-!
# Coherent inverse maps for sequential diagrams of cofibrations

The homotopy extension property adjusts a homotopy inverse at the next stage
so that it agrees strictly with the previous inverse on the preceding stage.
Recursion therefore gives an actual natural inverse transformation whose
components are homotopy inverses of the prescribed forward maps.

The imported sequential invariance theorem constructs the required coherent
inverse homotopies using relative mapping-cylinder latching maps and timed
strong deformation retractions. It supplies an actual equivalence of
colimits with the canonical induced map as its forward map. The direct
map-level strictification below is also useful independently.
-/

noncomputable section

open CategoryTheory Limits
open scoped Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace Quillen.TheoremA

/-- In a strictly commutative square of homotopy equivalences, HEP on the
lower successor map adjusts the upper-stage inverse to extend the preceding
inverse exactly, without changing the specified forward map. -/
theorem exists_compatible_inverse {A B C D : TopCat.{u}}
    (i : A ⟶ B) (j : C ⟶ D) (hj : homotopyExtensionProperty j)
    (e₀ : ContinuousMap.HomotopyEquiv A C) (e₁ : ContinuousMap.HomotopyEquiv B D)
    (sq : j.hom.comp e₀.toFun = e₁.toFun.comp i.hom) :
    ∃ e : ContinuousMap.HomotopyEquiv B D,
      e.toFun = e₁.toFun ∧ e.invFun.comp j.hom = i.hom.comp e₀.invFun := by
  let H₀ := (e₀.right_inv.some).symm
  let H₁ := e₁.left_inv.some
  let L : (e₁.invFun.comp j.hom).Homotopy
      (e₁.invFun.comp (j.hom.comp (e₀.toFun.comp e₀.invFun))) :=
    ((ContinuousMap.Homotopy.refl e₁.invFun).comp
      ((ContinuousMap.Homotopy.refl j.hom).comp H₀)).cast rfl rfl
  have heq : e₁.invFun.comp (j.hom.comp (e₀.toFun.comp e₀.invFun)) =
      (e₁.invFun.comp e₁.toFun).comp (i.hom.comp e₀.invFun) := by
    apply ContinuousMap.ext
    intro x
    exact congrArg e₁.invFun (ContinuousMap.congr_fun sq (e₀.invFun x))
  let K : (e₁.invFun.comp j.hom).Homotopy (i.hom.comp e₀.invFun) :=
    (L.cast rfl heq).trans
      ((H₁.comp (ContinuousMap.Homotopy.refl (i.hom.comp e₀.invFun))).cast rfl rfl)
  obtain ⟨Q, hQ₀, hQ⟩ := homotopyExtensionProperty_continuous hj B
    e₁.invFun K.toContinuousMap K.map_zero_left
  let r : C(D, B) := ⟨fun x ↦ Q (1, x), Q.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let R : e₁.invFun.Homotopy r := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  let e := (HomotopyFiber.replaceForward e₁.symm r ⟨R.symm⟩).symm
  refine ⟨e, rfl, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact (hQ 1 x).trans (K.map_one_left x)

end Quillen.TheoremA

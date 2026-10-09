import Quillen.Topology.HELP.StrictHomotopyEquiv
import Quillen.Topology.HomotopyFiber.BoundaryCorrection
import Quillen.Topology.HELP.Compact

/-! Actual homotopy equivalences satisfy HELP with the whole prescribed
boundary homotopy retained exactly. -/
noncomputable section
universe u
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
namespace Quillen.TheoremA

/-- Homotopy extension and lifting for a genuine homotopy equivalence.
No based/relative inverse data are assumed. -/
theorem homotopyEquiv_HELP {A B X Y : TopCat.{u}} {i : A ⟶ B}
    (hi : homotopyExtensionProperty i) (e : ContinuousMap.HomotopyEquiv X Y)
    (a : C(A,X)) (b : C(B,Y)) (H : (e.toFun.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧ ∃ K : (e.toFun.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x) := by
  obtain ⟨Q,hQ₀,hQA⟩ := homotopyExtensionProperty_continuous hi Y b
    H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x)
  let b' : C(B,Y) := ⟨fun x ↦ Q (1,x), by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hw : e.toFun.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c,hc,⟨K⟩⟩ := homotopyEquiv_strictHELP hi e a b' hw
  let L := K.toHomotopy.trans T.symm
  let H' : ((e.toFun.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,hc]) rfl
  have hL : ∀ t x, L (t,i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [L, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact K.prop _ (i x) ⟨x,rfl⟩
    · change Q (unitInterval.symm _, i x) = H (_, x)
      rw [hQA]
      simp
  obtain ⟨L',hL'⟩ := homotopyExtensionProperty_unpad_boundary hi L H' hL
  exact ⟨c,hc,L',hL'⟩

end Quillen.TheoremA
namespace Quillen

/-- The compact HELP property follows from an actual homotopy equivalence. -/
theorem compactHELP_of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : CompactHomotopyExtensionLiftingProperty e.toFun := by
  intro A B _ _ i hi a b H
  exact TheoremA.homotopyEquiv_HELP (X := TopCat.of X) (Y := TopCat.of Y) hi e a b H

end Quillen

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.StrictPair
public import Quillen.Topology.HELP.CubeBoundaryHomeomorph
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceProperty

/-!
# Finite based-boundary HELP from the original weak equivalence

Surjectivity on the actual cubical homotopy sets lifts every cube whose
boundary is constant. Genuine HEP then recovers any prescribed boundary
homotopy on that same constant boundary map. The zero-dimensional boundary
is empty and gives an unrestricted test. Arbitrary nonconstant boundary maps
in positive dimension require a separate sphere-filling argument.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen

/-- Strict-square HELP for one fixed boundary map recovers every prescribed
homotopy on that same map, using the actual HEP correction. -/
theorem fullHELP_at_fixed_boundary_of_strict
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A B : TopCat.{u}) (i : A ⟶ B)
    (hi : Quillen.homotopyExtensionProperty i) (a : C(A, X))
    (hf : ∀ b : C(B,Y), f.comp a = b.comp i.hom →
      ∃ c : C(B,X), c.comp i.hom = a ∧
        Nonempty ((f.comp c).HomotopyRel b (Set.range i)))
    (b : C(B,Y)) (H : (f.comp a).Homotopy (b.comp i.hom)) :
    ∃ c : C(B,X), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
      ∀ t x, K (t,i x) = H (t,x) := by
  obtain ⟨Q,hQ₀,hQA⟩ := Quillen.homotopyExtensionProperty_continuous hi
    (TopCat.of Y) b H.symm.toContinuousMap (fun x ↦ H.symm.map_zero_left x)
  let b' : C(B,Y) := ⟨fun x ↦ Q (1,x),by fun_prop⟩
  let T : b.Homotopy b' := {
    toContinuousMap := Q
    map_zero_left := hQ₀
    map_one_left := fun _ ↦ rfl }
  have hw : f.comp a = b'.comp i.hom := by
    ext x
    exact ((hQA 1 x).trans (H.symm.map_one_left x)).symm
  obtain ⟨c,hc,⟨K⟩⟩ := hf b' hw
  let L := K.toHomotopy.trans T.symm
  let H' : ((f.comp c).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by rw [ContinuousMap.comp_assoc,hc]) rfl
  have hL : ∀ t x, L (t,i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [L,ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
    split_ifs
    · exact K.prop _ (i x) ⟨x,rfl⟩
    · change Q (unitInterval.symm _,i x) = H (_,x)
      rw [hQA]
      simp
  obtain ⟨L',hL'⟩ := Quillen.homotopyExtensionProperty_unpad_boundary hi
    (Z := TopCat.of Y) L H' hL
  exact ⟨c,hc,L',hL'⟩

namespace IsWeakHomotopyEquivalence
open CubicalTests
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X, Y)} (hf : IsWeakHomotopyEquivalence f)
include hf

/-- The original weak equivalence lifts a based cube, retaining the entire
constant boundary and a homotopy relative to the actual boundary subtype. -/
theorem basedCube_strictHELP (n : ℕ) (x : X) (b : C(cube.{u} n, Y))
    (hb : ∀ z : boundary.{u} n,b z.val = f x) :
    ∃ c : C(cube.{u} n,X),
      c.comp (boundaryInclusion n).hom = ContinuousMap.const _ x ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) := by
  let up : C((Fin n → unitInterval),cube.{u} n) := ⟨ULift.up,continuous_uliftUp⟩
  let down : C(cube.{u} n,(Fin n → unitInterval)) := ⟨ULift.down,continuous_uliftDown⟩
  let p : GenLoop (Fin n) Y (f x) := ⟨b.comp up,fun z hz ↦ hb ⟨⟨z⟩,hz⟩⟩
  obtain ⟨q,hq⟩ := (hf.homotopy_bijective x n).surjective (Quotient.mk' p)
  induction q using Quotient.inductionOn with | h q =>
    change Quotient.mk' (genLoopPostcomp f rfl q) = Quotient.mk' p at hq
    obtain ⟨H⟩ := Quotient.exact hq
    let c := q.val.comp down
    refine ⟨c,?_,⟨{
      toHomotopy := {
        toFun z := H (z.1,z.2.down)
        continuous_toFun := H.continuous.comp
          (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd))
        map_zero_left z := H.toHomotopy.map_zero_left z.down
        map_one_left z := H.toHomotopy.map_one_left z.down }
      prop' := ?_ }⟩⟩
    · ext z
      exact q.property z.val.down z.property
    · rintro t z ⟨a,rfl⟩
      exact H.prop t a.val.down a.property

/-- Full prescribed-boundary HELP in every finite dimension when the
original source boundary map is constant. The boundary homotopy need not be
constant at any intermediate time. -/
theorem basedCube_fullHELP (n : ℕ) (x : X) (b : C(cube.{u} n, Y))
    (H : (f.comp (ContinuousMap.const (boundary.{u} n) x)).Homotopy
      (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n,X),
      c.comp (boundaryInclusion n).hom = ContinuousMap.const _ x ∧
      ∃ K : (f.comp c).Homotopy b, ∀ (t : unitInterval) (z : boundary.{u} n),
        K (t,z.val) = H (t,z) := by
  apply fullHELP_at_fixed_boundary_of_strict f _ _ (boundaryInclusion n)
    (boundaryInclusion_hep n) (ContinuousMap.const _ x) _ b H
  intro b' h
  exact hf.basedCube_strictHELP n x b' (fun z ↦ (ContinuousMap.congr_fun h z).symm)

/-- The genuine empty boundary gives unrestricted full HELP in dimension
zero, even when no source basepoint was initially supplied. -/
theorem zeroCube_fullHELP (a : C(boundary.{u} 0, X)) (b : C(cube.{u} 0, Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion 0).hom)) :
    ∃ c : C(cube.{u} 0,X), c.comp (boundaryInclusion 0).hom = a ∧
      ∃ K : (f.comp c).Homotopy b, ∀ (t : unitInterval) (z : boundary.{u} 0),
        K (t,z.val) = H (t,z) := by
  let : IsEmpty (boundary.{u} 0) := ⟨fun z ↦ by
    obtain ⟨i,_⟩ := z.property
    exact Fin.elim0 i⟩
  obtain ⟨x,_⟩ := hf.component_surjective (b (zero 0))
  have ha : a = ContinuousMap.const _ x := by ext z; exact isEmptyElim z
  subst a
  exact hf.basedCube_fullHELP 0 x b H

end IsWeakHomotopyEquivalence
end Quillen

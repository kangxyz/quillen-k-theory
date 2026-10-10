/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.DoubleMappingCylinder.WeakCartesian

/-! The original endpoint comparisons of weakly cartesian double cylinders
retain their actual source points and constant paths, including degree zero. -/
@[expose] public section


noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Topology unitInterval
universe u

namespace DoubleCylinderWeakTests
open DoubleCylinder
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TheoremA.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TheoremA.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (hgraph : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
    (d : C(K,D')), IsClosed (Set.ofPred (fun z : K × D' ↦ d z.1 = z.2)))
  (hL : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg TopCat.Hom.hom wf)))
  (hR : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg TopCat.Hom.hom wg)))

include hgraph hL hR in
example (x : B) : Function.Bijective (homotopyGroupMap (N := Fin 0)
    (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
      (FiniteNormalization.left_square sq sq' a b c wf wg)) (x := x) rfl) :=
  (Cartesian.leftComparison_isWeakHomotopyEquivalence sq sq' a b c wf wg hgraph hL
    hR).homotopy_bijective x 0

include hgraph hL hR in
example (x : C) (n : ℕ) : Function.Bijective (homotopyGroupMap (N := Fin n)
    (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
      (FiniteNormalization.right_square sq sq' a b c wf wg)) (x := x) rfl) :=
  (Cartesian.rightComparison_isWeakHomotopyEquivalence sq sq' a b c wf wg hgraph hL
    hR).homotopy_bijective x n

include hgraph hL hR in
example [IsEmpty B] :
    IsEmpty (HomotopyPullback (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom) :=
  (Cartesian.leftComparison_isWeakHomotopyEquivalence sq sq' a b c wf wg hgraph hL
    hR).isEmpty_target

example (x : B) :
    let z := HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
      (FiniteNormalization.left_square sq sq' a b c wf wg) x
    z.val.1 = b x ∧ z.val.2.1 = Subdivision.leftEnd (e := e) x ∧
      ∀ t, z.val.2.2 t = Subdivision.leftEnd (e := e') (b x) :=
  ⟨rfl,rfl,fun _ ↦ rfl⟩

end DoubleCylinderWeakTests

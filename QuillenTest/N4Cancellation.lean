/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.PiOneLegs
public import Quillen.Topology.PlusConstruction.DisplayedComparisonRealizations

/-! # Fresh nonabelian, based-path and low-degree cancellation regressions -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.N4Cancellation

open Quillen

/-- No commutative-group assumption enters the generic quotient comparison. -/
theorem nonabelianQuotientComparison {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K] (f : G →* H) (g : G →* K) (h : H →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) (hcomm : h.comp f = g) : Function.Bijective h :=
  MonoidHom.bijective_of_surjective_equal_kernels f g h hf hg hker hcomm

/-- The concrete permutation group test does not install a commutative instance. -/
theorem permutationGroupComparison :
    Function.Bijective (MonoidHom.id (Equiv.Perm (Fin 3))) :=
  nonabelianQuotientComparison (MonoidHom.id _) (MonoidHom.id _) (MonoidHom.id _)
    Function.surjective_id Function.surjective_id rfl rfl

section Based
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Arbitrary supplied target-basepoint paths change no element of the raw kernel. -/
theorem originalKernel (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y) :
    (basedPiOneMap f γ).ker = (piMap 0 f (x := x) rfl).ker := basedPiOneMap_ker f γ

/-- The actual homotopy track, not an arbitrary comparison path, makes the square commute. -/
theorem coherentBasedSquare (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z))
    (H : (k.comp f).Homotopy g) {x : X} {y : Y} {z : Z}
    (γ : Path (f x) y) (δ : Path (g x) z) :
    (basedPiOneMap k (displayedComparisonPath f g k H γ δ)).comp (basedPiOneMap f γ) =
      basedPiOneMap g δ := basedPiOneMap_displayedComparison f g k H γ δ

/-- The unit-removal correction has both original projection tracks literally constant. -/
theorem bothFiberCorrectionTracks (f : C(X, Z)) (g : C(Y, Z))
    (z : HomotopyPullback f g) :
    (HomotopyPullback.transportedFiberUnitPath f g z).map
      (HomotopyPullback.sourceProjection f g).continuous =
        Path.refl (HomotopyPullback.sourceProjection f g z) ∧
    (HomotopyPullback.transportedFiberUnitPath f g z).map
      (HomotopyPullback.baseProjection f g).continuous =
        Path.refl (HomotopyPullback.baseProjection f g z) :=
  ⟨HomotopyPullback.transportedFiberUnitPath_source f g z,
    HomotopyPullback.transportedFiberUnitPath_base f g z⟩
end Based

section Cylinder
open DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints A) (endMap f g) l e)

/-- The degree-one gap range is surjectivity and degree-zero bijectivity;
equal kernels are not required for this pair of conclusions. -/
theorem genuineGapRange (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N M : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ M) :
    Function.Surjective (piMap 0 (gap f g sq) (x := a) rfl) ∧
      Function.Bijective (homotopyGroupMap (N := Fin 0) (gap f g sq) (x := a) rfl) :=
  ⟨plus_gap_piOne_surjective f g sq a b c γ δ N M hf hg,
    plus_gap_piZero_bijective f g sq a b c γ δ N M hf hg⟩

include sq in
/-- The actual legs need only connected bases and raw surjections with equal kernels. -/
theorem rawKernelBothLegs [PathConnectedSpace A] [PathConnectedSpace B] [PathConnectedSpace C]
    (a : A) (hf : Function.Surjective (piMap 0 f.hom (x := a) rfl))
    (hg : Function.Surjective (piMap 0 g.hom (x := a) rfl))
    (hker : (piMap 0 f.hom (x := a) rfl).ker = (piMap 0 g.hom (x := a) rfl).ker) :
    Function.Bijective (piMap 0 (gapLeftEndpoint e) (x := f a) rfl) ∧
      Function.Bijective (piMap 0 (gapRightEndpoint e) (x := g a) rfl) :=
  ⟨leftEnd_piOne_bijective_of_equal_kernel f g sq a hf hg hker,
    rightEnd_piOne_bijective_of_equal_kernel f g sq a hf hg hker⟩
end Cylinder
section Realizations
open scoped Simplicial
open IsPlusConstruction
variable {X : Type u} [TopologicalSpace X] {Y Z : SSet.{u}}

/-- With supplied covers and a displayed comparison, the recognized forward map is exact. -/
theorem exactDisplayedForward
    (f : C(X, |Y|)) (g : C(X, |Z|)) (k : C(|Y|, |Z|)) (H : (k.comp f).Homotopy g)
    {x : X} {y : |Y|} {z : |Z|} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → |Y|} {q : F → |Z|} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, F)) (hlift : ∀ e, q (lift e) = k (p e)) (e₀ : E) :
    (displayedComparisonHomotopyEquivSuppliedCovers
      f g k H γ δ N hf hg hp hq lift hlift e₀).toFun = k := rfl
end Realizations
end QuillenTest.N4Cancellation

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent
public import Quillen.Topology.PlusConstruction.DoubleCylinderWeakEquivalence
public import Quillen.Topology.Realization.Domination

/-!
# Restricted ordinary homotopy uniqueness of plus comparisons

The target of the original plus map is an actual realization. Its actual self-
double-cylinder has explicit realization domination and a supplied covering
lift of its left leg between supplied simply connected covers. These geometric
inputs construct homotopy cancellation. The conclusion is ordinary homotopy
of maps: supplied under-source tracks are not asserted fixed or coherently
identified, and no contractible comparison-space claim is made.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.IsPlusConstruction
open DoubleCylinder
variable {A D : TopCat.{u}} {B : SSet.{u}}

/-- The original self-cylinder ends are homotopic because the actual fold is a
left inverse of the genuinely recognized left leg. -/
def selfCylinderEndHomotopyOfDomination
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E) :
    (gapLeftEndpoint e).Homotopy (gapRightEndpoint e) := by
  let legEquiv := Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination (gapLeftEndpoint e)
    (doubleCylinder_leftLeg_isWeakHomotopyEquivalence_suppliedCovers
      f f sq a b b γ γ N hf hf hp hd ki hi e₀) T r s Hdom
  let q := selfFold f sq
  have hstart : q.comp (legEquiv.toFun.comp legEquiv.invFun) = legEquiv.invFun := by
    ext x
    exact ContinuousMap.congr_fun (selfFold_left f sq) (legEquiv.invFun x)
  let L : legEquiv.invFun.Homotopy q :=
    ((ContinuousMap.Homotopy.refl q).comp legEquiv.right_inv.some).cast hstart rfl
  let K : ((gapLeftEndpoint e).comp q).Homotopy (ContinuousMap.id D) :=
    ((ContinuousMap.Homotopy.refl (gapLeftEndpoint e)).comp L.symm).trans legEquiv.right_inv.some
  have hleft : ((gapLeftEndpoint e).comp q).comp (gapRightEndpoint e) =
      gapLeftEndpoint e := by
    ext x
    exact congrArg (gapLeftEndpoint e) (ContinuousMap.congr_fun (selfFold_right f sq) x)
  exact (K.compContinuousMap (gapRightEndpoint e)).cast hleft rfl

/-- The actual self-cylinder construction cancels precomposition with the
original plus map at the level of ordinary homotopies. -/
def homotopyCancelOfDominatedSelfCylinder
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(|B|, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ := by
  let v := homotopyDesc f f sq h₀ h₁ H
  let L := selfCylinderEndHomotopyOfDomination
    f sq a b γ N hf T r s Hdom hp hd ki hi e₀
  exact ((ContinuousMap.Homotopy.refl v).comp L).cast
    (homotopyDesc_left f f sq h₀ h₁ H) (homotopyDesc_right f f sq h₀ h₁ H)

/-- Two comparisons with supplied under-source homotopies are ordinarily
homotopic. No relative-under-source coherence of those supplied tracks is claimed. -/
def comparisonHomotopyOfDominatedSelfCylinder
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(|B|, Y))
    (H₀ : (h₀.comp f.hom).Homotopy g) (H₁ : (h₁.comp f.hom).Homotopy g) :
    h₀.Homotopy h₁ :=
  homotopyCancelOfDominatedSelfCylinder
    f sq a b γ N hf T r s Hdom hp hd ki hi e₀ h₀ h₁ (H₀.trans H₁.symm)

/-- Restricted ordinary homotopy uniqueness, with geometric self-cylinder data
and no assumed cancellation or uniqueness certificate. -/
theorem homotopic_comparisons_of_dominatedSelfCylinder
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(|B|, Y))
    (H₀ : (h₀.comp f.hom).Homotopy g) (H₁ : (h₁.comp f.hom).Homotopy g) :
    h₀.Homotopic h₁ :=
  ⟨comparisonHomotopyOfDominatedSelfCylinder
    f sq a b γ N hf T r s Hdom hp hd ki hi e₀ g h₀ h₁ H₀ H₁⟩

end Quillen.IsPlusConstruction

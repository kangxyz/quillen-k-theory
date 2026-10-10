/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.RealizationRows

/-!
# Homotopy extension for subfamilies of replacement-row summands

An arbitrary subfamily of a topological disjoint union has the homotopy
extension property, with an explicit extension. This supplies the elementary
cofibration step for unions of degeneracy summands in a simplicial replacement.
It does not prove the skeletal gluing theorem for total realizations.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremA

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The inclusion of an arbitrary subfamily of a topological disjoint union. -/
def sigmaSubfamilyInclusion (S : Set ι) : C((Σ i : S, X i.1), Σ i, X i) :=
  ContinuousMap.sigma fun i ↦ ContinuousMap.sigmaMk i.1

/-- Extend a prescribed homotopy on the selected components, keeping every
other component constant in time. -/
def sigmaSubfamilyHomotopyExtension {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y)) :
    C(unitInterval × (Σ i, X i), Y) := by
  classical
  let component : ∀ i, C(X i × unitInterval, Y) := fun i ↦
    if hi : i ∈ S then
      h.comp (ContinuousMap.prodMk ContinuousMap.snd
        ((ContinuousMap.sigmaMk (⟨i, hi⟩ : S)).comp ContinuousMap.fst))
    else
      f.comp ((ContinuousMap.sigmaMk i).comp ContinuousMap.fst)
  let e : (unitInterval × Σ i, X i) ≃ₜ Σ i, X i × unitInterval :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  exact (ContinuousMap.sigma component).comp e

/-- The extension agrees with the supplied homotopy on its whole prescribed domain. -/
theorem sigmaSubfamilyHomotopyExtension_restrict {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (t : unitInterval) (x : Σ i : S, X i.1) :
    sigmaSubfamilyHomotopyExtension S f h (t, sigmaSubfamilyInclusion S x) = h (t, x) := by
  rcases x with ⟨⟨i, hi⟩, x⟩
  simp [sigmaSubfamilyHomotopyExtension, sigmaSubfamilyInclusion, hi]

/-- Compatibility at time zero suffices for the explicit extension to start
at the original map everywhere. -/
theorem sigmaSubfamilyHomotopyExtension_zero {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (hzero : ∀ x, h (0, x) = f (sigmaSubfamilyInclusion S x))
    (x : Σ i, X i) :
    sigmaSubfamilyHomotopyExtension S f h (0, x) = f x := by
  classical
  rcases x with ⟨i, x⟩
  by_cases hi : i ∈ S
  · simpa [sigmaSubfamilyHomotopyExtension, sigmaSubfamilyInclusion, hi] using
      hzero ⟨⟨i, hi⟩, x⟩
  · simp [sigmaSubfamilyHomotopyExtension, hi]

/-- The subfamily inclusion has the genuine homotopy extension property
against every target space; no extension is assumed as input. -/
theorem sigmaSubfamily_homotopyExtension {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (hzero : ∀ x, h (0, x) = f (sigmaSubfamilyInclusion S x)) :
    ∃ k : C(unitInterval × (Σ i, X i), Y),
      (∀ x, k (0, x) = f x) ∧
      ∀ t x, k (t, sigmaSubfamilyInclusion S x) = h (t, x) :=
  ⟨sigmaSubfamilyHomotopyExtension S f h,
    sigmaSubfamilyHomotopyExtension_zero S f h hzero,
    sigmaSubfamilyHomotopyExtension_restrict S f h⟩

/-- The simplicial inclusion of a chosen subfamily of summands. -/
def simplicialSubfamilyInclusion (Z : ι → SSet.{u}) (S : Set ι) :
    simplicialSigma (fun i : S ↦ Z i.1) ⟶ simplicialSigma Z where
  app _ := ↾fun x ↦ ⟨x.1.1, x.2⟩
  naturality _ _ _ := rfl

@[reassoc (attr := simp)]
theorem simplicialSubfamilyInclusion_ι (Z : ι → SSet.{u}) (S : Set ι) (i : S) :
    simplicialSigmaι (fun i : S ↦ Z i.1) i ≫ simplicialSubfamilyInclusion Z S =
      simplicialSigmaι Z i.1 := rfl

/-- The realization isomorphisms identify the realized inclusion exactly with
the topological subfamily inclusion. -/
theorem realizationSubfamilyInclusion_naturality (Z : ι → SSet.{u}) (S : Set ι) :
    SSet.toTop.map (simplicialSubfamilyInclusion Z S) ≫ (realizationSigmaIso Z).hom =
      (realizationSigmaIso (fun i : S ↦ Z i.1)).hom ≫
        TopCat.ofHom (sigmaSubfamilyInclusion (X := fun i ↦ |Z i|) S) := by
  apply (realizedSigmaIsColimit (fun i : S ↦ Z i.1)).hom_ext
  intro ⟨i⟩
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, simplicialSubfamilyInclusion_ι,
    realizationSigmaIso_ι, ← Category.assoc, realizationSigmaIso_ι]
  rfl

/-- Pointwise form of the comparison, convenient for transporting extensions. -/
theorem realizationSubfamilyInclusion_apply (Z : ι → SSet.{u}) (S : Set ι)
    (x : |simplicialSigma (fun i : S ↦ Z i.1)|) :
    (realizationSigmaIso Z).hom (SSet.toTop.map (simplicialSubfamilyInclusion Z S) x) =
      sigmaSubfamilyInclusion S ((realizationSigmaIso (fun i : S ↦ Z i.1)).hom x) :=
  ConcreteCategory.congr_hom (realizationSubfamilyInclusion_naturality Z S) x

/-- The inverse comparison commutes with the canonical subfamily inclusion. -/
theorem realizationSubfamilyInclusion_inv_apply (Z : ι → SSet.{u}) (S : Set ι)
    (x : Σ i : S, |Z i.1|) :
    SSet.toTop.map (simplicialSubfamilyInclusion Z S)
        ((realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) =
      (realizationSigmaIso Z).inv (sigmaSubfamilyInclusion S x) := by
  have h := realizationSubfamilyInclusion_apply Z S
    ((realizationSigmaIso (fun i : S ↦ Z i.1)).inv x)
  have hs : (realizationSigmaIso (fun i : S ↦ Z i.1)).hom
      ((realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) = x :=
    ConcreteCategory.congr_hom (realizationSigmaIso (fun i : S ↦ Z i.1)).inv_hom_id x
  rw [hs] at h
  calc
    _ = (realizationSigmaIso Z).inv ((realizationSigmaIso Z).hom
        (SSet.toTop.map (simplicialSubfamilyInclusion Z S)
          ((realizationSigmaIso (fun i : S ↦ Z i.1)).inv x))) :=
      (ConcreteCategory.congr_hom (realizationSigmaIso Z).hom_inv_id _).symm
    _ = _ := congrArg (realizationSigmaIso Z).inv h

/-- The canonical realization of a simplicial subfamily inclusion has the
homotopy extension property. This transports the explicit construction through
proved realization homeomorphisms and works with every target topology. -/
theorem realizationSubfamily_homotopyExtension
    (Z : ι → SSet.{u}) (S : Set ι) {Y : Type v} [TopologicalSpace Y]
    (f : C(|simplicialSigma Z|, Y))
    (h : C(unitInterval × |simplicialSigma (fun i : S ↦ Z i.1)|, Y))
    (hzero : ∀ x, h (0, x) = f (SSet.toTop.map (simplicialSubfamilyInclusion Z S) x)) :
    ∃ k : C(unitInterval × |simplicialSigma Z|, Y),
      (∀ x, k (0, x) = f x) ∧
      ∀ t x, k (t, SSet.toTop.map (simplicialSubfamilyInclusion Z S) x) = h (t, x) := by
  let f' : C((Σ i, |Z i|), Y) := f.comp (realizationSigmaIso Z).inv.hom
  let h' : C(unitInterval × (Σ i : S, |Z i.1|), Y) :=
    h.comp ((ContinuousMap.id unitInterval).prodMap
      (realizationSigmaIso (fun i : S ↦ Z i.1)).inv.hom)
  have hzero' : ∀ x, h' (0, x) = f' (sigmaSubfamilyInclusion S x) := by
    intro x
    change h (0, (realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) =
      f ((realizationSigmaIso Z).inv (sigmaSubfamilyInclusion S x))
    rw [← realizationSubfamilyInclusion_inv_apply]
    exact hzero _
  refine ⟨(sigmaSubfamilyHomotopyExtension S f' h').comp
    ((ContinuousMap.id unitInterval).prodMap (realizationSigmaIso Z).hom.hom), ?_, ?_⟩
  · intro x
    change sigmaSubfamilyHomotopyExtension S f' h'
      (0, (realizationSigmaIso Z).hom x) = f x
    rw [sigmaSubfamilyHomotopyExtension_zero S f' h' hzero']
    exact congrArg f (ConcreteCategory.congr_hom (realizationSigmaIso Z).hom_inv_id x)
  · intro t x
    change sigmaSubfamilyHomotopyExtension S f' h'
      (t, (realizationSigmaIso Z).hom
        (SSet.toTop.map (simplicialSubfamilyInclusion Z S) x)) = h (t, x)
    rw [realizationSubfamilyInclusion_apply,
      sigmaSubfamilyHomotopyExtension_restrict]
    exact congrArg (fun z ↦ h (t, z))
      (ConcreteCategory.congr_hom (realizationSigmaIso (fun i : S ↦ Z i.1)).hom_inv_id x)

end Quillen.TheoremA

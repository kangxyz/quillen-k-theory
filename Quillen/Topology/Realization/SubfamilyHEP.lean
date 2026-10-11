/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.Coproduct
public import Quillen.Topology.HELP.Coproduct
public import Quillen.Topology.HELP.Basic

/-!
# Homotopy extension for realized simplicial subfamilies
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The simplicial inclusion of a chosen subfamily of summands. -/
def Realization.simplicialSubfamilyInclusion (Z : ι → SSet.{u}) (S : Set ι) :
    Quillen.Realization.simplicialSigma (fun i : S ↦ Z i.1) ⟶ Quillen.Realization.simplicialSigma Z
      where
  app _ := ↾fun x ↦ ⟨x.1.1, x.2⟩
  naturality _ _ _ := rfl

@[reassoc (attr := simp)]
theorem Realization.simplicialSubfamilyInclusion_ι (Z : ι → SSet.{u}) (S : Set ι) (i : S) :
    Quillen.Realization.simplicialSigmaι (fun i : S ↦ Z i.1) i ≫
      Quillen.Realization.simplicialSubfamilyInclusion Z S =
      Quillen.Realization.simplicialSigmaι Z i.1 := rfl

/-- The realization isomorphisms identify the realized inclusion exactly with
the topological subfamily inclusion. -/
theorem Realization.realizationSubfamilyInclusion_naturality (Z : ι → SSet.{u}) (S : Set ι) :
    SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z S) ≫
      (Quillen.Realization.realizationSigmaIso Z).hom =
      (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).hom ≫
        TopCat.ofHom (Quillen.sigmaSubfamilyInclusion (X := fun i ↦ |Z i|) S) := by
  apply (Quillen.Realization.realizedSigmaIsColimit (fun i : S ↦ Z i.1)).hom_ext
  intro ⟨i⟩
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, Quillen.Realization.simplicialSubfamilyInclusion_ι,
    Quillen.Realization.realizationSigmaIso_ι, ← Category.assoc,
      Quillen.Realization.realizationSigmaIso_ι]
  rfl

/-- Pointwise form of the comparison, convenient for transporting extensions. -/
theorem Realization.realizationSubfamilyInclusion_apply (Z : ι → SSet.{u}) (S : Set ι)
    (x : |Quillen.Realization.simplicialSigma (fun i : S ↦ Z i.1)|) :
    (Quillen.Realization.realizationSigmaIso Z).hom (SSet.toTop.map
      (Quillen.Realization.simplicialSubfamilyInclusion Z S) x) =
      Quillen.sigmaSubfamilyInclusion S ((Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z
        i.1)).hom x) :=
  ConcreteCategory.congr_hom (Quillen.Realization.realizationSubfamilyInclusion_naturality Z S) x

/-- The inverse comparison commutes with the canonical subfamily inclusion. -/
theorem Realization.realizationSubfamilyInclusion_inv_apply (Z : ι → SSet.{u}) (S : Set ι)
    (x : Σ i : S, |Z i.1|) :
    SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z S)
        ((Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) =
      (Quillen.Realization.realizationSigmaIso Z).inv (Quillen.sigmaSubfamilyInclusion S x) := by
  have h := Quillen.Realization.realizationSubfamilyInclusion_apply Z S
    ((Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv x)
  have hs : (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).hom
      ((Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) = x :=
    ConcreteCategory.congr_hom (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z
      i.1)).inv_hom_id x
  rw [hs] at h
  calc
    _ = (Quillen.Realization.realizationSigmaIso Z).inv ((Quillen.Realization.realizationSigmaIso
      Z).hom
        (SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z S)
          ((Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv x))) :=
      (ConcreteCategory.congr_hom (Quillen.Realization.realizationSigmaIso Z).hom_inv_id _).symm
    _ = _ := congrArg (Quillen.Realization.realizationSigmaIso Z).inv h

/-- The canonical realization of a simplicial subfamily inclusion has the
homotopy extension property. This transports the explicit construction through
proved realization homeomorphisms and works with every target topology. -/
theorem Realization.realizationSubfamily_homotopyExtension
    (Z : ι → SSet.{u}) (S : Set ι) {Y : Type v} [TopologicalSpace Y]
    (f : C(|Quillen.Realization.simplicialSigma Z|, Y))
    (h : C(unitInterval × |Quillen.Realization.simplicialSigma (fun i : S ↦ Z i.1)|, Y))
    (hzero : ∀ x, h (0, x) = f (SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z
      S) x)) :
    ∃ k : C(unitInterval × |Quillen.Realization.simplicialSigma Z|, Y),
      (∀ x, k (0, x) = f x) ∧
      ∀ t x, k (t, SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z S) x) = h (t,
        x) := by
  let f' : C((Σ i, |Z i|), Y) := f.comp (Quillen.Realization.realizationSigmaIso Z).inv.hom
  let h' : C(unitInterval × (Σ i : S, |Z i.1|), Y) :=
    h.comp ((ContinuousMap.id unitInterval).prodMap
      (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv.hom)
  have hzero' : ∀ x, h' (0, x) = f' (Quillen.sigmaSubfamilyInclusion S x) := by
    intro x
    change h (0, (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z i.1)).inv x) =
      f ((Quillen.Realization.realizationSigmaIso Z).inv (Quillen.sigmaSubfamilyInclusion S x))
    rw [← Quillen.Realization.realizationSubfamilyInclusion_inv_apply]
    exact hzero _
  refine ⟨(Quillen.sigmaSubfamilyHomotopyExtension S f' h').comp
    ((ContinuousMap.id unitInterval).prodMap (Quillen.Realization.realizationSigmaIso Z).hom.hom),
      ?_, ?_⟩
  · intro x
    change Quillen.sigmaSubfamilyHomotopyExtension S f' h'
      (0, (Quillen.Realization.realizationSigmaIso Z).hom x) = f x
    rw [Quillen.sigmaSubfamilyHomotopyExtension_zero S f' h' hzero']
    exact congrArg f (ConcreteCategory.congr_hom (Quillen.Realization.realizationSigmaIso
      Z).hom_inv_id x)
  · intro t x
    change Quillen.sigmaSubfamilyHomotopyExtension S f' h'
      (t, (Quillen.Realization.realizationSigmaIso Z).hom
        (SSet.toTop.map (Quillen.Realization.simplicialSubfamilyInclusion Z S) x)) = h (t, x)
    rw [Quillen.Realization.realizationSubfamilyInclusion_apply,
      Quillen.sigmaSubfamilyHomotopyExtension_restrict]
    exact congrArg (fun z ↦ h (t, z))
      (ConcreteCategory.congr_hom (Quillen.Realization.realizationSigmaIso (fun i : S ↦ Z
        i.1)).hom_inv_id x)

/-- Inclusions of arbitrary subfamilies of realized simplicial summands have
the categorical homotopy extension property. -/
theorem Realization.homotopyExtensionProperty_realizationSubfamily {ι : Type u}
    (Z : ι → SSet.{u}) (S : Set ι) :
    Quillen.homotopyExtensionProperty (SSet.toTop.map
      (Quillen.Realization.simplicialSubfamilyInclusion Z S)) :=
  Quillen.homotopyExtensionProperty_of_continuous _ fun _ f H hzero ↦
    Quillen.Realization.realizationSubfamily_homotopyExtension Z S f H hzero


end Quillen

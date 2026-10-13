/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HELP.RelativeCylinder
public import Quillen.Topology.Pushout.CompactHausdorff

/-! # The compact endpoint-relative cylinder boundary

The domain is the actual topological pushout of the side cylinder and the
 two endpoint copies. It makes sense for every HEP map, without assuming an
embedding. The relative square-extension theorem proves its HEP.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Quillen

variable {A B : TopCat.{u}} (i : A ⟶ B)

/-- Include two copies of `A` at times zero and one in the cylinder `A × I`. -/
def CylinderBoundary.cylinderBoundaryEnds (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ TopCat.of (A ×
  unitInterval) :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ (a, 0)) (fun a ↦ (a, 1)),
    Continuous.sumElim (by fun_prop) (by fun_prop)⟩

/-- Apply the attaching map `i : A ⟶ B` separately to the two endpoint copies of `A`. -/
def CylinderBoundary.cylinderBoundarySumMap : TopCat.of (A ⊕ A) ⟶ TopCat.of (B ⊕ B) :=
  TopCat.ofHom ⟨Sum.map i i, i.hom.continuous.sumMap i.hom.continuous⟩

/-- The pushout joining the side cylinder `A × I` to the two caps `B ⊕ B` along their endpoint
copies of `A`; no embedding hypothesis on `i` is needed. -/
def CylinderBoundary : TopCat.{u} := pushout (Quillen.CylinderBoundary.cylinderBoundaryEnds A)
  (Quillen.CylinderBoundary.cylinderBoundarySumMap i)

/-- The side-cylinder leg of the pushout defining `Quillen.CylinderBoundary i`. -/
def CylinderBoundary.cylinderBoundarySide : TopCat.of (A × unitInterval) ⟶ Quillen.CylinderBoundary
  i :=
  pushout.inl _ _

/-- The two-cap leg of the pushout defining `Quillen.CylinderBoundary i`. -/
def CylinderBoundary.cylinderBoundaryCaps : TopCat.of (B ⊕ B) ⟶ Quillen.CylinderBoundary i :=
  pushout.inr _ _

/-- The map `A × I ⟶ B × I` applying `i` to the space coordinate and retaining time. -/
def CylinderBoundary.cylinderBoundarySideMap : TopCat.of (A × unitInterval) ⟶ TopCat.of (B ×
  unitInterval) :=
  TopCat.ofHom ⟨fun z ↦ (i z.1, z.2), by fun_prop⟩

/-- The map from the endpoint-relative cylinder boundary to `B × I`, induced by `i` on the side
cylinder and the endpoint inclusions on the caps. -/
def CylinderBoundary.cylinderBoundaryMap : Quillen.CylinderBoundary i ⟶ TopCat.of (B × unitInterval)
  :=
  pushout.desc (Quillen.CylinderBoundary.cylinderBoundarySideMap i)
    (Quillen.CylinderBoundary.cylinderBoundaryEnds B) (by
    ext x : 1
    cases x <;> rfl)

@[simp] theorem CylinderBoundary.cylinderBoundarySide_map :
    Quillen.CylinderBoundary.cylinderBoundarySide i ≫ Quillen.CylinderBoundary.cylinderBoundaryMap i
      = Quillen.CylinderBoundary.cylinderBoundarySideMap i :=
  pushout.inl_desc _ _ _

@[simp] theorem CylinderBoundary.cylinderBoundaryCaps_map :
    Quillen.CylinderBoundary.cylinderBoundaryCaps i ≫ Quillen.CylinderBoundary.cylinderBoundaryMap i
      = Quillen.CylinderBoundary.cylinderBoundaryEnds B :=
  pushout.inr_desc _ _ _

theorem CylinderBoundary.cylinderBoundary_isPushout : IsPushout
  (Quillen.CylinderBoundary.cylinderBoundaryEnds A)
    (Quillen.CylinderBoundary.cylinderBoundarySumMap i)
      (Quillen.CylinderBoundary.cylinderBoundarySide i)
      (Quillen.CylinderBoundary.cylinderBoundaryCaps i) :=
  IsPushout.of_hasPushout _ _

instance CylinderBoundary.cylinderBoundary_compactSpace [CompactSpace A] [CompactSpace B] :
    CompactSpace (Quillen.CylinderBoundary i) := compactSpace_pushout
      (Quillen.CylinderBoundary.cylinderBoundary_isPushout i)

/-- The whole boundary of the relative cylinder has HEP, including both
endpoint copies. The proof uses the actual pushout topology. -/
theorem CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap
    (hi : Quillen.homotopyExtensionProperty i) : Quillen.homotopyExtensionProperty
      (Quillen.CylinderBoundary.cylinderBoundaryMap i) := by
  apply Quillen.homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let S : C((A × unitInterval) × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, Quillen.CylinderBoundary.cylinderBoundarySide i z.1), by fun_prop⟩
  let H₀ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl z.1)), by fun_prop⟩
  let H₁ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr z.1)), by fun_prop⟩
  have hside (a : A) (t : unitInterval) :
      Quillen.CylinderBoundary.cylinderBoundaryMap i (Quillen.CylinderBoundary.cylinderBoundarySide
        i (a, t)) = (i a, t) :=
    ConcreteCategory.congr_hom (Quillen.CylinderBoundary.cylinderBoundarySide_map i) (a, t)
  have hcap₀ (b : B) :
      Quillen.CylinderBoundary.cylinderBoundaryMap i (Quillen.CylinderBoundary.cylinderBoundaryCaps
        i (Sum.inl b)) = (b, 0) :=
    ConcreteCategory.congr_hom (Quillen.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inl b)
  have hcap₁ (b : B) :
      Quillen.CylinderBoundary.cylinderBoundaryMap i (Quillen.CylinderBoundary.cylinderBoundaryCaps
        i (Sum.inr b)) = (b, 1) :=
    ConcreteCategory.congr_hom (Quillen.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inr b)
  have hcomm₀ (a : A) : Quillen.CylinderBoundary.cylinderBoundarySide i (a, 0) =
      Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl (i a)) :=
    ConcreteCategory.congr_hom (Quillen.CylinderBoundary.cylinderBoundary_isPushout i).w (Sum.inl a)
  have hcomm₁ (a : A) : Quillen.CylinderBoundary.cylinderBoundarySide i (a, 1) =
      Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr (i a)) :=
    ConcreteCategory.congr_hom (Quillen.CylinderBoundary.cylinderBoundary_isPushout i).w (Sum.inr a)
  obtain ⟨K, hK₀, hKS, hK₀', hK₁'⟩ := Quillen.homotopyExtensionProperty_interval_square_extension
    hi f S H₀ H₁
    (fun a t ↦ (hzero _).trans (congrArg f (hside a t)))
    (fun b ↦ (hzero _).trans (congrArg f (hcap₀ b)))
    (fun b ↦ (hzero _).trans (congrArg f (hcap₁ b)))
    (fun a t ↦ congrArg (fun x ↦ H (t, x)) (hcomm₀ a))
    (fun a t ↦ congrArg (fun x ↦ H (t, x)) (hcomm₁ a))
  refine ⟨⟨fun z ↦ K (z.2, z.1), by fun_prop⟩, ?_, ?_⟩
  · rintro ⟨b, t⟩
    exact hK₀ b t
  · intro t x
    obtain ⟨x, rfl⟩ := pushout_sum_surjective (Quillen.CylinderBoundary.cylinderBoundary_isPushout
      i) x
    rcases x with ⟨a, s⟩ | (b | b)
    · change K (Quillen.CylinderBoundary.cylinderBoundaryMap i
        (Quillen.CylinderBoundary.cylinderBoundarySide i (a, s)), t) = _
      rw [hside]
      exact hKS a s t
    · change K (Quillen.CylinderBoundary.cylinderBoundaryMap i
        (Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl b)), t) = _
      rw [hcap₀]
      exact hK₀' b t
    · change K (Quillen.CylinderBoundary.cylinderBoundaryMap i
        (Quillen.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr b)), t) = _
      rw [hcap₁]
      exact hK₁' b t

end Quillen

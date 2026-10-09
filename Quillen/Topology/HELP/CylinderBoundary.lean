import Quillen.CategoryTheory.TheoremA.RealizationPushoutProduct
import Quillen.Topology.Pushout.CompactHausdorff

/-! # The compact endpoint-relative cylinder boundary

The domain is the actual topological pushout of the side cylinder and the
 two endpoint copies. It makes sense for every HEP map, without assuming an
embedding. The relative square-extension theorem proves its HEP.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Quillen.TheoremA

variable {A B : TopCat.{u}} (i : A ⟶ B)

def cylinderBoundaryEnds (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ TopCat.of (A × unitInterval) :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ (a, 0)) (fun a ↦ (a, 1)),
    Continuous.sumElim (by fun_prop) (by fun_prop)⟩

def cylinderBoundarySumMap : TopCat.of (A ⊕ A) ⟶ TopCat.of (B ⊕ B) :=
  TopCat.ofHom ⟨Sum.map i i, i.hom.continuous.sumMap i.hom.continuous⟩

def CylinderBoundary : TopCat.{u} := pushout (cylinderBoundaryEnds A) (cylinderBoundarySumMap i)

def cylinderBoundarySide : TopCat.of (A × unitInterval) ⟶ CylinderBoundary i :=
  pushout.inl _ _

def cylinderBoundaryCaps : TopCat.of (B ⊕ B) ⟶ CylinderBoundary i :=
  pushout.inr _ _

def cylinderBoundarySideMap : TopCat.of (A × unitInterval) ⟶ TopCat.of (B × unitInterval) :=
  TopCat.ofHom ⟨fun z ↦ (i z.1, z.2), by fun_prop⟩

def cylinderBoundaryMap : CylinderBoundary i ⟶ TopCat.of (B × unitInterval) :=
  pushout.desc (cylinderBoundarySideMap i) (cylinderBoundaryEnds B) (by
    ext x : 1
    cases x <;> rfl)

@[simp] theorem cylinderBoundarySide_map :
    cylinderBoundarySide i ≫ cylinderBoundaryMap i = cylinderBoundarySideMap i :=
  pushout.inl_desc _ _ _

@[simp] theorem cylinderBoundaryCaps_map :
    cylinderBoundaryCaps i ≫ cylinderBoundaryMap i = cylinderBoundaryEnds B :=
  pushout.inr_desc _ _ _

theorem cylinderBoundary_isPushout : IsPushout (cylinderBoundaryEnds A)
    (cylinderBoundarySumMap i) (cylinderBoundarySide i) (cylinderBoundaryCaps i) :=
  IsPushout.of_hasPushout _ _

instance cylinderBoundary_compactSpace [CompactSpace A] [CompactSpace B] :
    CompactSpace (CylinderBoundary i) := compactSpace_pushout (cylinderBoundary_isPushout i)

/-- The whole boundary of the relative cylinder has HEP, including both
endpoint copies. The proof uses the actual pushout topology. -/
theorem homotopyExtensionProperty_cylinderBoundaryMap
    (hi : homotopyExtensionProperty i) : homotopyExtensionProperty (cylinderBoundaryMap i) := by
  apply homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let S : C((A × unitInterval) × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, cylinderBoundarySide i z.1), by fun_prop⟩
  let H₀ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, cylinderBoundaryCaps i (Sum.inl z.1)), by fun_prop⟩
  let H₁ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, cylinderBoundaryCaps i (Sum.inr z.1)), by fun_prop⟩
  have hside (a : A) (t : unitInterval) :
      cylinderBoundaryMap i (cylinderBoundarySide i (a, t)) = (i a, t) :=
    ConcreteCategory.congr_hom (cylinderBoundarySide_map i) (a, t)
  have hcap₀ (b : B) :
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)) = (b, 0) :=
    ConcreteCategory.congr_hom (cylinderBoundaryCaps_map i) (Sum.inl b)
  have hcap₁ (b : B) :
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)) = (b, 1) :=
    ConcreteCategory.congr_hom (cylinderBoundaryCaps_map i) (Sum.inr b)
  have hcomm₀ (a : A) : cylinderBoundarySide i (a, 0) =
      cylinderBoundaryCaps i (Sum.inl (i a)) :=
    ConcreteCategory.congr_hom (cylinderBoundary_isPushout i).w (Sum.inl a)
  have hcomm₁ (a : A) : cylinderBoundarySide i (a, 1) =
      cylinderBoundaryCaps i (Sum.inr (i a)) :=
    ConcreteCategory.congr_hom (cylinderBoundary_isPushout i).w (Sum.inr a)
  obtain ⟨K, hK₀, hKS, hK₀', hK₁'⟩ := homotopyExtensionProperty_interval_square_extension
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
    obtain ⟨x, rfl⟩ := pushout_sum_surjective (cylinderBoundary_isPushout i) x
    rcases x with ⟨a, s⟩ | (b | b)
    · change K (cylinderBoundaryMap i (cylinderBoundarySide i (a, s)), t) = _
      rw [hside]
      exact hKS a s t
    · change K (cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)), t) = _
      rw [hcap₀]
      exact hK₀' b t
    · change K (cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)), t) = _
      rw [hcap₁]
      exact hK₁' b t

end Quillen.TheoremA

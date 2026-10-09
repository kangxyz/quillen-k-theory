import Quillen.Topology.HELP.CubeBoundary

/-! # The canonical presentation is the actual cube boundary

Injectivity is proved using the original side/cap pushout relations. Compactness
then upgrades the resulting continuous bijection to a homeomorphism with the
literal boundary subtype. In particular its actual inclusion has HEP.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u

namespace Quillen.TheoremA

/-- The actual relative-cylinder boundary map is injective when the original
map is injective. Only the displayed pushout relations are used. -/
theorem cylinderBoundaryMap_injective {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : Function.Injective i) : Function.Injective (cylinderBoundaryMap i) := by
  have hs (a : A) (t : unitInterval) :
      cylinderBoundaryMap i (cylinderBoundarySide i (a,t)) = (i a,t) :=
    ConcreteCategory.congr_hom (cylinderBoundarySide_map i) (a,t)
  have h₀ (b : B) : cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)) = (b,0) :=
    ConcreteCategory.congr_hom (cylinderBoundaryCaps_map i) (Sum.inl b)
  have h₁ (b : B) : cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)) = (b,1) :=
    ConcreteCategory.congr_hom (cylinderBoundaryCaps_map i) (Sum.inr b)
  have hc₀ (a : A) : cylinderBoundarySide i (a,0) =
      cylinderBoundaryCaps i (Sum.inl (i a)) :=
    ConcreteCategory.congr_hom (cylinderBoundary_isPushout i).w (Sum.inl a)
  have hc₁ (a : A) : cylinderBoundarySide i (a,1) =
      cylinderBoundaryCaps i (Sum.inr (i a)) :=
    ConcreteCategory.congr_hom (cylinderBoundary_isPushout i).w (Sum.inr a)
  intro x y h
  obtain ⟨x,rfl⟩ := pushout_sum_surjective (cylinderBoundary_isPushout i) x
  obtain ⟨y,rfl⟩ := pushout_sum_surjective (cylinderBoundary_isPushout i) y
  rcases x with ⟨a,t⟩ | (b | b) <;> rcases y with ⟨a',t'⟩ | (b' | b')
  · change cylinderBoundaryMap i (cylinderBoundarySide i (a,t)) =
      cylinderBoundaryMap i (cylinderBoundarySide i (a',t')) at h
    rw [hs,hs] at h
    exact congrArg (cylinderBoundarySide i)
      (Prod.ext (hi (congrArg Prod.fst h))
        (congrArg (fun z : B × unitInterval ↦ z.2) h))
  · change cylinderBoundaryMap i (cylinderBoundarySide i (a,t)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b')) at h
    rw [hs,h₀] at h
    obtain ⟨hb,ht⟩ := Prod.mk.inj h
    subst b'; subst t
    exact hc₀ a
  · change cylinderBoundaryMap i (cylinderBoundarySide i (a,t)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b')) at h
    rw [hs,h₁] at h
    obtain ⟨hb,ht⟩ := Prod.mk.inj h
    subst b'; subst t
    exact hc₁ a
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)) =
      cylinderBoundaryMap i (cylinderBoundarySide i (a',t')) at h
    rw [h₀,hs] at h
    obtain ⟨hb,ht⟩ := Prod.mk.inj h
    subst b; subst t'
    exact (hc₀ a').symm
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b')) at h
    rw [h₀,h₀] at h
    exact congrArg (fun z ↦ cylinderBoundaryCaps i (Sum.inl z)) (congrArg Prod.fst h)
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b')) at h
    rw [h₀,h₁] at h
    exact False.elim (zero_ne_one (congrArg Prod.snd h))
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)) =
      cylinderBoundaryMap i (cylinderBoundarySide i (a',t')) at h
    rw [h₁,hs] at h
    obtain ⟨hb,ht⟩ := Prod.mk.inj h
    subst b; subst t'
    exact (hc₁ a').symm
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inl b')) at h
    rw [h₁,h₀] at h
    exact False.elim (zero_ne_one (congrArg Prod.snd h).symm)
  · change cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b)) =
      cylinderBoundaryMap i (cylinderBoundaryCaps i (Sum.inr b')) at h
    rw [h₁,h₁] at h
    exact congrArg (fun z ↦ cylinderBoundaryCaps i (Sum.inr z)) (congrArg Prod.fst h)

end Quillen.TheoremA
namespace Quillen.CubicalTests
open TheoremA

/-- The existing canonical presentation map has no identifications beyond
those of the actual cube boundary. -/
theorem boundaryPresentation_injective (n : ℕ) :
    Function.Injective (boundaryPresentation.{u} n).map := by
  induction n with
  | zero => intro x; exact PEmpty.elim x
  | succ n ih =>
    exact (stepHomeomorph n).injective.comp
      (cylinderBoundaryMap_injective (boundaryPresentation n).map ih)

/-- The literal boundary subtype of the actual universe-lifted cube. -/
abbrev boundary (n : ℕ) := {z : cube.{u} n // z.down ∈ Cube.boundary (Fin n)}

/-- The original subtype inclusion, with its inherited topology. -/
def boundaryInclusion (n : ℕ) : TopCat.of (boundary.{u} n) ⟶ cube.{u} n :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

/-- The canonical iterated pushout presentation is homeomorphic to the actual
boundary, with forward function given by its original presentation map. -/
def boundaryPresentationHomeomorph (n : ℕ) :
    (boundaryPresentation.{u} n).space ≃ₜ boundary.{u} n := by
  let P := boundaryPresentation.{u} n
  let : CompactSpace P.space := P.compact
  let e : P.space ≃ boundary.{u} n := Equiv.ofBijective
    (fun a ↦ ⟨P.map a,P.lands a⟩) ⟨fun _ _ h ↦ boundaryPresentation_injective n
      (congrArg Subtype.val h), fun z ↦ by
        obtain ⟨a,ha⟩ := P.covers z.val z.property
        exact ⟨a,Subtype.ext ha⟩⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (P.map.hom.continuous.subtype_mk _)

@[simp] theorem boundaryPresentationHomeomorph_apply (n : ℕ)
    (a : (boundaryPresentation.{u} n).space) :
    (boundaryPresentationHomeomorph n a).val = (boundaryPresentation n).map a := rfl

@[simp] theorem boundaryPresentationHomeomorph_symm_map (n : ℕ) (z : boundary.{u} n) :
    (boundaryPresentation n).map ((boundaryPresentationHomeomorph n).symm z) = z.val :=
  congrArg Subtype.val ((boundaryPresentationHomeomorph n).apply_symm_apply z)

/-- Exact original map factorization through the boundary homeomorphism. -/
theorem boundaryPresentationHomeomorph_comp (n : ℕ) :
    (TopCat.isoOfHomeo (boundaryPresentationHomeomorph.{u} n)).hom ≫ boundaryInclusion n =
      (boundaryPresentation n).map := rfl

theorem boundaryPresentationHomeomorph_inv_comp (n : ℕ) :
    (TopCat.isoOfHomeo (boundaryPresentationHomeomorph.{u} n)).inv ≫
      (boundaryPresentation n).map = boundaryInclusion n := by
  ext z : 1
  exact boundaryPresentationHomeomorph_symm_map n z

/-- The actual boundary inclusion has HEP, obtained from the canonical
pushout presentation rather than assumed for an arbitrary closed subset. -/
theorem boundaryInclusion_hep (n : ℕ) :
    homotopyExtensionProperty (boundaryInclusion.{u} n) := by
  rw [← boundaryPresentationHomeomorph_inv_comp]
  exact homotopyExtensionProperty_comp (homotopyExtensionProperty_of_isIso _)
    (boundaryPresentation n).hep

/-- The original presentation map is itself a closed embedding. -/
theorem boundaryPresentation_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (boundaryPresentation.{u} n).map := by
  let : CompactSpace (boundaryPresentation.{u} n).space := (boundaryPresentation n).compact
  exact (boundaryPresentation n).map.hom.continuous.isClosedEmbedding
    (boundaryPresentation_injective n)

/-- Remove only the universe lift; all boundary coordinates are unchanged. -/
def boundaryULiftHomeomorph (n : ℕ) : boundary.{u} n ≃ₜ
    {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)} where
  toFun z := ⟨z.val.down,z.property⟩
  invFun z := ⟨⟨z.val⟩,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The canonical presentation of the literal, unlifted finite-cube boundary. -/
def boundaryPresentationUnliftedHomeomorph (n : ℕ) :
    (boundaryPresentation.{u} n).space ≃ₜ
      {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)} :=
  (boundaryPresentationHomeomorph n).trans (boundaryULiftHomeomorph n)

@[simp] theorem boundaryPresentationUnliftedHomeomorph_apply (n : ℕ)
    (a : (boundaryPresentation.{u} n).space) :
    (boundaryPresentationUnliftedHomeomorph n a).val = ((boundaryPresentation n).map a).down := rfl

/-- The literal subtype inclusion into the unlifted finite cube. -/
def unliftedBoundaryInclusion (n : ℕ) :
    TopCat.of {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)} ⟶
      TopCat.of (Fin n → unitInterval) := TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

theorem unliftedBoundaryInclusion_hep (n : ℕ) :
    homotopyExtensionProperty (unliftedBoundaryInclusion n) := by
  let e : TopCat.of (boundary.{0} n) ≅
      TopCat.of {z : Fin n → unitInterval // z ∈ Cube.boundary (Fin n)} :=
    TopCat.isoOfHomeo (boundaryULiftHomeomorph.{0} n)
  let d : cube.{0} n ≅ TopCat.of (Fin n → unitInterval) :=
    TopCat.isoOfHomeo (Homeomorph.ulift.{0,0} (X := Fin n → unitInterval))
  have he : e.inv ≫ boundaryInclusion n ≫ d.hom = unliftedBoundaryInclusion n := by
    ext z : 1
    rfl
  rw [← he]
  exact homotopyExtensionProperty_comp (homotopyExtensionProperty_of_isIso _)
    (homotopyExtensionProperty_comp (boundaryInclusion_hep n)
      (homotopyExtensionProperty_of_isIso _))

end Quillen.CubicalTests

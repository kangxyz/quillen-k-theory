import Quillen.Resolution.LengthOne
import Quillen.CategoryTheory.ExactCategory.Equivalence
import Quillen.KTheory.Equivalence
import Quillen.CategoryTheory.SmallModel.Abelian

/-!
# Canonical comparisons for nested inherited exact subcategories

Flattening a nested full subcategory is a genuine exact equivalence, and the
factorization through it retains the original inclusion maps. This supplies
the categorical bookkeeping for adjacent resolution-length strata.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P Q : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]

instance inclusionOfLE_additive (h : P ≤ Q) : (ObjectProperty.ιOfLE h).Additive where
  map_add := by intros; rfl

/-- The canonical exact inclusion for an inequality of inherited properties. -/
def exactInclusionOfLE (h : P ≤ Q) :
    ExactFunctor (ExactSubcategory.exactStructure E P) (ExactSubcategory.exactStructure E Q) where
  toFunctor := ObjectProperty.ιOfLE h
  map_conflation _ hS := hS

@[simp] theorem exactInclusionOfLE_comp (h : P ≤ Q) :
    (exactInclusionOfLE E P Q h).comp (exactInclusion E Q) = exactInclusion E P := rfl

/-- The smaller property, evaluated on objects of the larger full subcategory. -/
def restrictedProperty (P Q : ObjectProperty C) (E : ExactStructure C) :
    ObjectProperty Q.FullSubcategory := fun X => P X.obj

instance restrictedProperty_isoClosed : (restrictedProperty P Q E).IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso (Q.ι.mapIso e) hX

instance restrictedProperty_containsZero : (restrictedProperty P Q E).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, P.prop_of_isZero (Q.ι.map_isZero (isZero_zero _))⟩

instance restrictedProperty_extensionClosed :
    (ExactSubcategory.exactStructure E Q).IsExtensionClosed (restrictedProperty P Q E) where
  prop_middle hS h₁ h₃ := ExactStructure.IsExtensionClosed.prop_middle (E := E) hS h₁ h₃

instance restrictedProperty_finiteProducts : (restrictedProperty P Q E).IsClosedUnderFiniteProducts :=
  (ExactSubcategory.exactStructure E Q).extensionClosed_finiteProducts (restrictedProperty P Q E)

instance restrictedProperty_kernelClosed [E.IsKernelClosed P] :
    (ExactSubcategory.exactStructure E Q).IsKernelClosed (restrictedProperty P Q E) where
  prop_kernel hS h₂ h₃ := ExactStructure.IsKernelClosed.prop_kernel (E := E) hS h₂ h₃

/-- The original smaller category, lifted into the nested full subcategory. -/
def nestedLift (h : P ≤ Q) : P.FullSubcategory ⥤ (restrictedProperty P Q E).FullSubcategory :=
  (restrictedProperty P Q E).lift (ObjectProperty.ιOfLE h) (fun X => X.property)

instance nestedLift_full (h : P ≤ Q) : (nestedLift E P Q h).Full := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_faithful (h : P ≤ Q) : (nestedLift E P Q h).Faithful := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_additive (h : P ≤ Q) : (nestedLift E P Q h).Additive := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_essSurj (h : P ≤ Q) : (nestedLift E P Q h).EssSurj where
  mem_essImage Z := ⟨⟨Z.obj.obj, Z.property⟩, ⟨Iso.refl _⟩⟩

instance nestedLift_isEquivalence (h : P ≤ Q) : (nestedLift E P Q h).IsEquivalence := {}

/-- The nested lift is exact for the genuinely inherited structures. -/
def nestedLiftExact (h : P ≤ Q) :
    ExactFunctor (ExactSubcategory.exactStructure E P)
      (ExactSubcategory.exactStructure (ExactSubcategory.exactStructure E Q)
        (restrictedProperty P Q E)) where
  toFunctor := nestedLift E P Q h
  map_conflation _ hS := hS

instance nestedLift_asEquivalence_additive (h : P ≤ Q) :
    (nestedLift E P Q h).asEquivalence.functor.Additive :=
  inferInstanceAs (nestedLift E P Q h).Additive

instance nestedLiftExact_isEquivalence (h : P ≤ Q) :
    (nestedLiftExact E P Q h).toFunctor.IsEquivalence :=
  inferInstanceAs (nestedLift E P Q h).IsEquivalence

/-- Flattening reflects conflations, not only the underlying category. -/
theorem nestedLift_ofEquivalence (h : P ≤ Q) :
    (ExactSubcategory.exactStructure (ExactSubcategory.exactStructure E Q)
      (restrictedProperty P Q E)).ofEquivalence (nestedLift E P Q h).asEquivalence =
      ExactSubcategory.exactStructure E P := by
  apply ExactStructure.ext_conflation
  funext S
  rfl

instance nestedLiftExact_mapQ_isEquivalence (h : P ≤ Q) :
    (nestedLiftExact E P Q h).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    rw [← nestedLift_ofEquivalence E P Q h]
    exact (ExactStructure.ofEquivalence_inflation_iff _ _ i).mpr hi
  · intro X Y p hp
    rw [← nestedLift_ofEquivalence E P Q h]
    exact (ExactStructure.ofEquivalence_deflation_iff _ _ p).mpr hp

@[simp] theorem nestedLift_factor (h : P ≤ Q) :
    (nestedLiftExact E P Q h).comp
      (exactInclusion (ExactSubcategory.exactStructure E Q) (restrictedProperty P Q E)) =
        exactInclusionOfLE E P Q h := rfl

/-- Length-one resolution applied to a nested inherited exact inclusion,
with the original un-nested inclusion K-map as its conclusion. -/
theorem inclusionOfLEKMap_bijective_of_length_one [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (restrictedProperty P Q E) 1 X) (n : ℕ) :
    Function.Bijective ((exactInclusionOfLE E P Q hPQ).KMap n) := by
  have h₁ := (nestedLiftExact E P Q hPQ).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := inclusionKMap_bijective_of_length_one
    (ExactSubcategory.exactStructure E Q) (restrictedProperty P Q E) h n
  rw [← nestedLift_factor E P Q hPQ, ExactFunctor.KMap_comp]
  exact h₂.comp h₁

/-- The corresponding genuine classifying-space equivalence, with the
un-nested exact inclusion as its forward map. -/
def inclusionOfLEClassifyingHomotopyEquivOfLengthOne [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (restrictedProperty P Q E) 1 X) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace
      (ExactSubcategory.exactStructure E Q).KSpace :=
  (classifyingHomotopyEquivOfIsEquivalence (nestedLiftExact E P Q hPQ).mapQ).trans
    (classifyingHomotopyEquivOfLengthOne (ExactSubcategory.exactStructure E Q)
      (restrictedProperty P Q E) h)

@[simp] theorem inclusionOfLEClassifyingHomotopyEquivOfLengthOne_toFun [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (restrictedProperty P Q E) 1 X) :
    (inclusionOfLEClassifyingHomotopyEquivOfLengthOne E P Q hPQ h).toFun =
      (classifyingSpaceMap (exactInclusionOfLE E P Q hPQ).mapQ).hom := by
  change (classifyingHomotopyEquivOfLengthOne (ExactSubcategory.exactStructure E Q)
    (restrictedProperty P Q E) h).toFun.comp
      (classifyingSpaceMap (nestedLiftExact E P Q hPQ).mapQ).hom = _
  rw [classifyingHomotopyEquivOfLengthOne_toFun, ← TopCat.hom_comp,
    ← classifyingSpaceMap_comp, ← ExactFunctor.mapQ_comp, nestedLift_factor]

/-- Equal object classes give an actual equivalence for their inherited
inclusion; this is a categorical equivalence, not a resolution assumption. -/
theorem inclusionOfLE_mapQ_isEquivalence_of_reverse (hPQ : P ≤ Q) (hQP : Q ≤ P) :
    (exactInclusionOfLE E P Q hPQ).mapQ.IsEquivalence := by
  let F := exactInclusionOfLE E P Q hPQ
  letI : F.toFunctor.Full := inferInstanceAs (ObjectProperty.ιOfLE hPQ).Full
  letI : F.toFunctor.Faithful := inferInstanceAs (ObjectProperty.ιOfLE hPQ).Faithful
  letI : F.toFunctor.EssSurj :=
    ⟨fun Y => ⟨⟨Y.obj, hQP _ Y.property⟩, ⟨Iso.refl _⟩⟩⟩
  letI : F.toFunctor.IsEquivalence := {}
  change F.mapQ.IsEquivalence
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff E Q _).1 hi
    exact (ExactSubcategory.inflation_iff E P _).2 ⟨Z, hQP _ hZ, p, hp, hS⟩
  · intro X Y p hp
    obtain ⟨Z, hZ, i, hi, hS⟩ := (ExactSubcategory.deflation_iff E Q _).1 hp
    exact (ExactSubcategory.deflation_iff E P _).2 ⟨Z, hQP _ hZ, i, hi, hS⟩

/-- The equivalent inherited inclusions give the same canonical all-degree
K-map equivalence. -/
theorem inclusionOfLEKMap_bijective_of_reverse (hPQ : P ≤ Q) (hQP : Q ≤ P) (n : ℕ) :
    Function.Bijective ((exactInclusionOfLE E P Q hPQ).KMap n) := by
  letI := inclusionOfLE_mapQ_isEquivalence_of_reverse E P Q hPQ hQP
  exact (exactInclusionOfLE E P Q hPQ).KMap_bijective_of_mapQ_isEquivalence n

/-- If every ambient object satisfies the predicate, the inherited exact
inclusion is an actual equivalence and its canonical K-map is bijective. -/
theorem inclusionKMap_bijective_of_all (hP : ∀ X, P X) (n : ℕ) :
    Function.Bijective (inclusionKMap E P n) := by
  let F := exactInclusion E P
  letI : F.toFunctor.Full := inferInstanceAs P.ι.Full
  letI : F.toFunctor.Faithful := inferInstanceAs P.ι.Faithful
  letI : F.toFunctor.EssSurj := ⟨fun Y => ⟨⟨Y, hP Y⟩, ⟨Iso.refl _⟩⟩⟩
  letI : F.toFunctor.IsEquivalence := {}
  letI : F.mapQ.IsEquivalence := by
    apply ExactFunctor.mapQ_isEquivalence_of_equivalence
    · intro X Y i hi
      obtain ⟨Z, p, hp, hS⟩ := hi
      exact (ExactSubcategory.inflation_iff E P _).2 ⟨Z, hP Z, p, hp, hS⟩
    · intro X Y p hp
      obtain ⟨Z, i, hi, hS⟩ := hp
      exact (ExactSubcategory.deflation_iff E P _).2 ⟨Z, hP Z, i, hi, hS⟩
  exact F.KMap_bijective_of_mapQ_isEquivalence n

end Quillen.Resolution

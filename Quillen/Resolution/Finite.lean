import Quillen.CategoryTheory.ExactCategory.Subcategory
import Quillen.Devissage.Filtration

/-!
# Finite admissible resolutions

The input in Quillen's resolution theorem is a finite sequence of actual
conflations, not merely a relation between object classes.  The recursive
presentation here retains every intermediate syzygy and every admissible
kernel–cokernel pair.  A resolution of length zero is an object already in the
resolving subcategory.  No common bound on the lengths is imposed.

Reference: Weibel, *The K-book*, V.3.1, pp. 20–21 of chapter V,
https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf.
-/

noncomputable section
universe v u v' u' w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A finite admissible resolution by objects satisfying `P`. In a successor
step, the middle term is a resolving object and the kernel is resolved by the
previous tower. The terminal object, rather than the middle object, is resolved. -/
inductive FiniteResolution (P : C → Prop) : C → Type (max u v)
  | of_mem {X : C} (hX : P X) : FiniteResolution P X
  | step (S : ShortComplex C) (hS : E.conflation S)
      (middle_mem : P S.X₂) (syzygy : FiniteResolution P S.X₁) :
      FiniteResolution P S.X₃

/-- The purely algebraic finite-resolution hypothesis. It has no homotopy,
comma-category, K-group, or uniform-length assumption. -/
def ResolutionHypothesis (P : C → Prop) : Prop :=
  ∀ X, Nonempty (E.FiniteResolution P X)

namespace FiniteResolution
variable {E} {P : C → Prop}

/-- The number of nonterminal conflations in the resolution. -/
def length {X : C} : E.FiniteResolution P X → ℕ
  | .of_mem _ => 0
  | .step _ _ _ R => R.length + 1

/-- Resolution terms, ordered from the augmentation toward the last syzygy. -/
def terms {X : C} : E.FiniteResolution P X → List C
  | .of_mem (X := X) _ => [X]
  | .step S _ _ R => S.X₂ :: R.terms

@[simp] lemma length_of_mem {X : C} (hX : P X) :
    (FiniteResolution.of_mem (E := E) hX).length = 0 := rfl

@[simp] lemma length_step (S : ShortComplex C) (hS : E.conflation S)
    (hP : P S.X₂) (R : E.FiniteResolution P S.X₁) :
    (FiniteResolution.step S hS hP R).length = R.length + 1 := rfl

@[simp] lemma terms_length {X : C} (R : E.FiniteResolution P X) :
    R.terms.length = R.length + 1 := by
  induction R with
  | of_mem hX => rfl
  | step S hS hP R ih => simp [terms, length, ih]

/-- Every term, including the last syzygy, belongs to the chosen class. -/
lemma mem_terms {X : C} (R : E.FiniteResolution P X) {Y : C}
    (hY : Y ∈ R.terms) : P Y := by
  induction R with
  | of_mem hX =>
    simp only [terms, List.mem_singleton] at hY
    exact hY ▸ hX
  | step S hS hP R ih =>
    simp only [terms, List.mem_cons] at hY
    rcases hY with rfl | hY
    · exact hP
    · exact ih hY

/-- A length-zero resolution says that the resolved object itself is in `P`. -/
lemma mem_of_length_eq_zero {X : C} (R : E.FiniteResolution P X)
    (h : R.length = 0) : P X := by
  cases R with
  | of_mem hX => exact hX
  | step S hS hP R => simp at h

/-- Forgetting restrictions on the resolving objects does not change a tower. -/
def mono {P' : C → Prop} (h : ∀ X, P X → P' X) {X : C} :
    E.FiniteResolution P X → E.FiniteResolution P' X
  | .of_mem hX => .of_mem (h X hX)
  | .step S hS hP R => .step S hS (h S.X₂ hP) (R.mono h)

@[simp] lemma length_mono {P' : C → Prop} (h : ∀ X, P X → P' X)
    {X : C} (R : E.FiniteResolution P X) : (R.mono h).length = R.length := by
  induction R with
  | of_mem hX => rfl
  | step S hS hP R ih => simp [mono, ih]

/-- The signed Euler expression attached to the actual resolution. -/
def euler {A : Type w} [AddGroup A] (f : C → A) {X : C} :
    E.FiniteResolution P X → A
  | .of_mem (X := X) _ => f X
  | .step S _ _ R => f S.X₂ - R.euler f

/-- Admissible exactness proves the Euler expression for every additive
invariant. This is an algebraic identity, not a K-equivalence assumption. -/
theorem additiveInvariant_eq_euler {A : Type w} [AddCommGroup A] (f : C → A)
    (hf : E.IsAdditiveInvariant f) {X : C} (R : E.FiniteResolution P X) :
    f X = R.euler f := by
  induction R with
  | of_mem hX => rfl
  | step S hS hP R ih =>
    change f S.X₃ = f S.X₂ - R.euler f
    rw [← ih]
    have h := hf S hS
    rw [h]
    abel

/-- Resolving an object puts its class in every subgroup containing the classes
of resolving objects. -/
theorem class_mem {X : C} (R : E.FiniteResolution P X)
    (H : AddSubgroup E.GrothendieckGroup)
    (hH : ∀ Y, P Y → E.grothendieckClass Y ∈ H) :
    E.grothendieckClass X ∈ H := by
  induction R with
  | of_mem hX => exact hH _ hX
  | step S hS hP R ih =>
    have h := E.grothendieckClass_additive hS
    have he : E.grothendieckClass S.X₃ =
        E.grothendieckClass S.X₂ - E.grothendieckClass S.X₁ := by rw [h]; abel
    rw [he]
    exact H.sub_mem (hH _ hP) ih

/-- Every finite resolution begins with an actual admissible epimorphism from
a resolving object. The length-zero case uses its identity. -/
def presentation {X : C} (R : E.FiniteResolution P X) :
    Σ Y : C, {p : Y ⟶ X // P Y ∧ E.deflation p} := by
  cases R with
  | of_mem hX => exact ⟨X, 𝟙 X, hX, E.deflation_id X⟩
  | step S hS hP R => exact ⟨S.X₂, S.g, hP, E.deflation_of_conflation hS⟩

end FiniteResolution

/-- Objects of resolution length at most `n`. This filtration is defined by
actual finite conflation towers. -/
def ResolutionLength (P : C → Prop) (n : ℕ) : ObjectProperty C :=
  fun X => ∃ R : E.FiniteResolution P X, R.length ≤ n

lemma resolutionLength_zero_iff (P : C → Prop) (X : C) :
    E.ResolutionLength P 0 X ↔ P X := by
  constructor
  · rintro ⟨R, hR⟩
    exact R.mem_of_length_eq_zero (Nat.eq_zero_of_le_zero hR)
  · intro hX
    exact ⟨.of_mem hX, Nat.le_refl 0⟩

lemma resolutionLength_mono (P : C → Prop) {m n : ℕ} (h : m ≤ n) :
    E.ResolutionLength P m ≤ E.ResolutionLength P n := by
  rintro X ⟨R, hR⟩
  exact ⟨R, hR.trans h⟩

lemma resolutionHypothesis_iff_union (P : C → Prop) :
    E.ResolutionHypothesis P ↔ ∀ X, ∃ n, E.ResolutionLength P n X := by
  constructor
  · intro h X
    obtain ⟨R⟩ := h X
    exact ⟨R.length, R, le_rfl⟩
  · intro h X
    obtain ⟨n, R, _⟩ := h X
    exact ⟨R⟩

/-- Kernel closure required in Quillen's resolution theorem. Both the middle
and quotient are required to be resolving objects. This is weaker than closure
under arbitrary admissible subobjects in the ambient exact category. -/
class IsKernelClosed (P : ObjectProperty C) : Prop where
  prop_kernel : ∀ {S : ShortComplex C}, E.conflation S → P S.X₂ → P S.X₃ → P S.X₁

end Quillen.ExactStructure

namespace Quillen.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Exact functors carry actual finite admissible resolutions to resolutions. -/
def mapFiniteResolution (F : ExactFunctor EC ED) {P : C → Prop} {P' : D → Prop}
    (h : ∀ X, P X → P' (F.toFunctor.obj X)) {X : C} :
    EC.FiniteResolution P X → ED.FiniteResolution P' (F.toFunctor.obj X)
  | .of_mem hX => .of_mem (h X hX)
  | .step S hS hP R =>
    .step (S.map F.toFunctor) (F.map_conflation S hS) (h S.X₂ hP)
      (F.mapFiniteResolution h R)

@[simp] lemma length_mapFiniteResolution (F : ExactFunctor EC ED)
    {P : C → Prop} {P' : D → Prop} (h : ∀ X, P X → P' (F.toFunctor.obj X))
    {X : C} (R : EC.FiniteResolution P X) :
    (F.mapFiniteResolution h R).length = R.length := by
  induction R with
  | of_mem hX => rfl
  | step S hS hP R ih => simp [mapFiniteResolution, ih]

end Quillen.ExactFunctor

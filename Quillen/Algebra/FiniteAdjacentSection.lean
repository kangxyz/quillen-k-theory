import Quillen.Algebra.FiniteAdjacentComplex
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Nat.Even

/-!
# A canonical representative at any finite term coordinate

Euler on the literal single-coordinate inclusion is identity or inversion,
according to the coordinate parity. Its actual inverse gives a section at
any specified coordinate. Every term tuple has a unique decomposition into
an original adjacent-incidence image times that single-coordinate term.
-/

noncomputable section
universe u
namespace Quillen.FiniteAdjacentComplex
variable (G : Type u) [CommGroup G]

/-- The original single-coordinate inclusion into a finite tuple. -/
def singleCoordinate {n : ℕ} (i : Fin n) : G →* (Fin n → G) :=
  MonoidHom.mulSingle (fun _ : Fin n => G) i

@[simp] theorem singleCoordinate_apply {n : ℕ} (i : Fin n) (x : G) :
    singleCoordinate G i x = Pi.mulSingle i x := rfl

@[simp] theorem singleCoordinate_zero (n : ℕ) (x : G) :
    singleCoordinate G (0 : Fin (n + 1)) x = Fin.cons x 1 := by
  ext j
  cases j using Fin.cases <;> simp [singleCoordinate]

@[simp] theorem singleCoordinate_succ {n : ℕ} (i : Fin n) (x : G) :
    singleCoordinate G i.succ x = Fin.cons 1 (singleCoordinate G i x) := by
  ext j
  cases j using Fin.cases <;> simp [singleCoordinate, Pi.mulSingle_apply]

/-- The sign at a coordinate, as an actual automorphism of the original group. -/
def coordinateSign (k : ℕ) : G ≃* G :=
  if Even k then MulEquiv.refl G else MulEquiv.inv G

@[simp] theorem coordinateSign_apply (k : ℕ) (x : G) :
    coordinateSign G k x = if Even k then x else x⁻¹ := by
  by_cases h : Even k <;> simp [coordinateSign, h]

@[simp] theorem coordinateSign_symm (k : ℕ) :
    (coordinateSign G k).symm = coordinateSign G k := by
  by_cases h : Even k <;> simp [coordinateSign, h]

@[simp] theorem coordinateSign_succ_apply (k : ℕ) (x : G) :
    coordinateSign G (k + 1) x = (coordinateSign G k x)⁻¹ := by
  by_cases h : Even k <;> simp [coordinateSign_apply, Nat.even_add_one, h]

/-- Euler restricted to the actual single coordinate is the alternating sign
automorphism. No surjectivity or K-theory statement is assumed. -/
theorem euler_singleCoordinate {n : ℕ} (i : Fin n) (x : G) :
    euler G n (singleCoordinate G i x) = coordinateSign G i.val x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [singleCoordinate_zero, euler_cons, map_one, div_one]
      simp [coordinateSign_apply]
    | succ i => simp only [singleCoordinate_succ, euler_cons, one_div, ih,
        Fin.val_succ, coordinateSign_succ_apply]

/-- In every position, Euler on the original single-coordinate inclusion is
bijective, including the unique coordinate of a length-one tuple. -/
theorem euler_singleCoordinate_bijective {n : ℕ} (i : Fin n) :
    Function.Bijective ((euler G n).comp (singleCoordinate G i)) := by
  have h : (euler G n).comp (singleCoordinate G i) = (coordinateSign G i.val).toMonoidHom := by
    ext x
    exact euler_singleCoordinate G i x
  rw [h]
  exact (coordinateSign G i.val).bijective

/-- The canonical coefficient of the representative in the specified coordinate. -/
def coordinateValue (n : ℕ) (i : Fin (n + 1)) : (Fin (n + 1) → G) →* G :=
  (coordinateSign G i.val).symm.toMonoidHom.comp (euler G (n + 1))

@[simp] theorem coordinateValue_apply (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    coordinateValue G n i y =
      if Even i.val then euler G (n + 1) y else (euler G (n + 1) y)⁻¹ := by
  change (coordinateSign G i.val).symm (euler G (n + 1) y) = _
  rw [coordinateSign_symm, coordinateSign_apply]

/-- An actual section of Euler supported at the specified coordinate. -/
def coordinateSection (n : ℕ) (i : Fin (n + 1)) : G →* (Fin (n + 1) → G) :=
  (singleCoordinate G i).comp (coordinateSign G i.val).symm.toMonoidHom

@[simp] theorem euler_coordinateSection (n : ℕ) (i : Fin (n + 1)) (x : G) :
    euler G (n + 1) (coordinateSection G n i x) = x := by
  change euler G (n + 1) (singleCoordinate G i ((coordinateSign G i.val).symm x)) = x
  rw [euler_singleCoordinate, MulEquiv.apply_symm_apply]

/-- The canonical representative of the original incidence coset. -/
def coordinateRepresentative (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → G) →* (Fin (n + 1) → G) :=
  (coordinateSection G n i).comp (euler G (n + 1))

@[simp] theorem coordinateRepresentative_apply (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    coordinateRepresentative G n i y = Pi.mulSingle i (coordinateValue G n i y) := rfl

/-- The representative has the same original Euler product. -/
@[simp] theorem euler_coordinateRepresentative (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    euler G (n + 1) (coordinateRepresentative G n i y) = euler G (n + 1) y :=
  euler_coordinateSection G n i _

/-- There is a unique original adjacent-disk tuple taking the canonical
single-coordinate representative to the given term tuple. -/
theorem existsUnique_incidence_representative (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! d : Fin n → G, incidence G n d * coordinateRepresentative G n i y = y := by
  have h : euler G (n + 1) (y / coordinateRepresentative G n i y) = 1 := by
    rw [map_div, euler_coordinateRepresentative, div_self']
  obtain ⟨d, hd⟩ := (euler_eq_one_iff G n _).mp h
  refine ⟨d, ?_, ?_⟩
  · change incidence G n d * coordinateRepresentative G n i y = y
    rw [hd, div_mul_cancel]
  · intro d' hd'
    apply incidence_injective G n
    apply mul_right_cancel (b := coordinateRepresentative G n i y)
    exact hd'.trans (by rw [hd, div_mul_cancel])

/-- The single-coordinate coefficient is uniquely determined modulo the
image of the original incidence homomorphism. -/
theorem existsUnique_coordinateValue (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! c : G, ∃ d : Fin n → G, incidence G n d * singleCoordinate G i c = y := by
  obtain ⟨d, hd, _⟩ := existsUnique_incidence_representative G n i y
  refine ⟨coordinateValue G n i y, ⟨d, hd⟩, ?_⟩
  rintro c ⟨d', hd'⟩
  apply (coordinateSign G i.val).injective
  have h := congrArg (euler G (n + 1)) hd'
  rw [map_mul, euler_incidence, one_mul, euler_singleCoordinate] at h
  exact h.trans (by
    change euler G (n + 1) y = coordinateSign G i.val
      ((coordinateSign G i.val).symm (euler G (n + 1) y))
    rw [MulEquiv.apply_symm_apply])

/-- Full uniqueness of the original incidence term and its single-coordinate
representative; this includes the empty disk tuple `n = 0`. -/
theorem existsUnique_incidence_coordinate (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! p : (Fin n → G) × G, incidence G n p.1 * singleCoordinate G i p.2 = y := by
  obtain ⟨d, hd, hu⟩ := existsUnique_incidence_representative G n i y
  refine ⟨(d, coordinateValue G n i y), hd, ?_⟩
  rintro ⟨d', c⟩ hc
  have he : c = coordinateValue G n i y :=
    (existsUnique_coordinateValue G n i y).unique ⟨d', hc⟩ ⟨d, hd⟩
  subst c
  exact Prod.ext (hu d' hc) rfl

end Quillen.FiniteAdjacentComplex

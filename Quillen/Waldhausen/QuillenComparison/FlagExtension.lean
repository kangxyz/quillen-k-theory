import Quillen.Waldhausen.QuillenComparison.FlagPullback

/-! # Extending admissible flags by a zero and an ambient target -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows ZeroObject
universe u v

namespace Quillen.Waldhausen.QuillenComparison
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {n : ℕ} (A : ComposableArrows C n)

/-- Admissibility of neighboring arrows suffices for a whole finite flag. -/
theorem flag_inflation_of_successors
    (hA : ∀ (i : ℕ) (hi : i < n), E.inflation (A.map' i (i + 1)))
    {i j : Fin (n + 1)} (f : i ⟶ j) : E.inflation (A.map f) := by
  suffices ∀ (k i j : ℕ) (hj : i + k = j) (hj' : j ≤ n),
      E.inflation (A.map' i j) by
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have hij : i ≤ j := leOfHom f
    obtain ⟨k, hk⟩ := Nat.le.dest hij
    exact this k i j hk (by omega)
  intro k
  induction k with
  | zero =>
    intro i j hj hj'
    simp only [Nat.add_zero] at hj
    subst j
    rw [A.map'_self i hj']
    exact E.inflation_id _
  | succ k ih =>
    intro i j hj hj'
    rw [← Nat.add_assoc] at hj
    subst j
    rw [A.map'_comp i (i + k) (i + k + 1)]
    exact E.inflation_comp _ _ (ih i (i + k) rfl (by omega)) (hA (i + k) (by omega))

/-- Prefix an actual zero object to a flag. -/
def zeroPrefixFlag : ComposableArrows C (n + 1) :=
  A.precomp (0 : (0 : C) ⟶ A.obj 0)

@[simp]
theorem zeroPrefixFlag_obj_zero : (zeroPrefixFlag A).obj 0 = (0 : C) := rfl

@[simp]
theorem zeroPrefixFlag_obj_succ (i : Fin (n + 1)) :
    (zeroPrefixFlag A).obj i.succ = A.obj i := rfl

@[simp]
theorem zeroPrefixFlag_map_succ {i j : Fin (n + 1)} (f : i ⟶ j) :
    (zeroPrefixFlag A).map ((Fin.succFunctor (n + 1)).map f) = A.map f := rfl

/-- Prefixing zero preserves admissibility without a condition on the old first term. -/
theorem zeroPrefixFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {i j : Fin (n + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((zeroPrefixFlag A).map f) := by
  apply flag_inflation_of_successors E
  intro i hi
  cases i with
  | zero => exact E.inflation_zero _
  | succ i => exact hA _

variable {Y : C} (q : A.obj (Fin.last n) ⟶ Y)

/-- The object sequence obtained by adjoining a last target. -/
def appendFlagObj : Fin (n + 1 + 1) → C := Fin.lastCases Y A.obj

@[simp]
theorem appendFlagObj_castSucc (i : Fin (n + 1)) :
    appendFlagObj A (Y := Y) i.castSucc = A.obj i := Fin.lastCases_castSucc i

@[simp]
theorem appendFlagObj_last : appendFlagObj A (Y := Y) (Fin.last (n + 1)) = Y :=
  Fin.lastCases_last

@[simp]
theorem appendFlagObj_succ_castSucc (i : Fin n) :
    appendFlagObj A (Y := Y) i.castSucc.succ = A.obj i.succ := by
  rw [← Fin.castSucc_succ, appendFlagObj_castSucc]

/-- The old neighboring maps followed by the prescribed last map. -/
def appendFlagSucc (i : Fin (n + 1)) :
    appendFlagObj A (Y := Y) i.castSucc ⟶ appendFlagObj A (Y := Y) i.succ :=
  Fin.lastCases
    (eqToHom (appendFlagObj_castSucc A (Fin.last n)) ≫ q ≫
      eqToHom (by simp only [Fin.succ_last, appendFlagObj_last]))
    (fun j ↦ eqToHom (appendFlagObj_castSucc A j.castSucc) ≫
      A.map (homOfLE (Fin.castSucc_le_succ j)) ≫
      eqToHom (appendFlagObj_succ_castSucc A j).symm) i

/-- Append a target using the actual adjacent flag maps. -/
def appendFlag : ComposableArrows C (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc (appendFlagObj A (Y := Y)) (appendFlagSucc A q)

@[simp]
theorem appendFlag_obj_castSucc (i : Fin (n + 1)) :
    (appendFlag A q).obj i.castSucc = A.obj i := appendFlagObj_castSucc A i

@[simp]
theorem appendFlag_obj_last : (appendFlag A q).obj (Fin.last (n + 1)) = Y :=
  appendFlagObj_last A

/-- Appending an inflation to an admissible flag is admissible. -/
theorem appendFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) (hq : E.inflation q)
    {i j : Fin (n + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((appendFlag A q).map f) := by
  apply flag_inflation_of_successors E
  intro i hi
  change E.inflation ((ComposableArrows.mkOfObjOfMapSucc _ _).map' i (i + 1))
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
  suffices ∀ (i : Fin (n + 1)), E.inflation (appendFlagSucc A q i) from this ⟨i, hi⟩
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [appendFlagSucc, Fin.lastCases_last]
    exact E.inflation_comp _ _
      (E.inflation_of_iso (eqToIso (appendFlagObj_castSucc A (Fin.last n))))
      (E.inflation_comp _ _ hq
        (E.inflation_of_iso (eqToIso (appendFlagObj_last A).symm)))
  | cast i =>
    simp only [appendFlagSucc, Fin.lastCases_castSucc]
    exact E.inflation_comp _ _
      (E.inflation_of_iso (eqToIso (appendFlagObj_castSucc A i.castSucc)))
      (E.inflation_comp _ _ (hA _)
        (E.inflation_of_iso (eqToIso (appendFlagObj_succ_castSucc A i).symm)))

/-- Restricting the appended flag to its original indices canonically recovers it. -/
def appendFlagRestrictionIso :
    Fin.castSuccFunctor (n + 1) ⋙ appendFlag A q ≅ A :=
  ComposableArrows.isoMk (fun i ↦ eqToIso (appendFlag_obj_castSucc A q i)) (by
    intro i hi
    change (appendFlag A q).map' i (i + 1) ≫ _ = _ ≫ A.map' i (i + 1)
    rw [show (appendFlag A q).map' i (i + 1) = appendFlagSucc A q ⟨i, by omega⟩ from
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i (by omega)]
    change appendFlagSucc A q (Fin.castSucc ⟨i, hi⟩) ≫ _ = _
    simp only [appendFlagSucc, Fin.lastCases_castSucc, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id, eqToIso.hom])

/-- The appended adjacent arrow is the prescribed target map, under the object identifications. -/
theorem appendFlag_last_step :
    (appendFlag A q).map (homOfLE (Fin.le_last (Fin.last n).castSucc)) ≫
        eqToHom (appendFlag_obj_last A q) =
      eqToHom (appendFlag_obj_castSucc A q (Fin.last n)) ≫ q := by
  change (appendFlag A q).map' n (n + 1) ≫ _ = _
  rw [show (appendFlag A q).map' n (n + 1) = appendFlagSucc A q (Fin.last n) from
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ n (by omega)]
  simp [appendFlagSucc]

/-- The maps to the appended target are the old top maps followed by the prescribed map. -/
theorem appendFlag_to_last (i : Fin (n + 1)) :
    (appendFlag A q).map (homOfLE (Fin.le_last i.castSucc)) ≫
        eqToHom (appendFlag_obj_last A q) =
      eqToHom (appendFlag_obj_castSucc A q i) ≫ flagTopMap A i ≫ q := by
  let f : i ⟶ Fin.last n := homOfLE (Fin.le_last i)
  have h := (appendFlagRestrictionIso A q).hom.naturality f
  change (appendFlag A q).map ((Fin.castSuccFunctor (n + 1)).map f) ≫
      eqToHom (appendFlag_obj_castSucc A q (Fin.last n)) =
    eqToHom (appendFlag_obj_castSucc A q i) ≫ flagTopMap A i at h
  rw [show homOfLE (Fin.le_last i.castSucc) =
    (Fin.castSuccFunctor (n + 1)).map f ≫
      homOfLE (Fin.le_last (Fin.last n).castSucc) from Subsingleton.elim _ _,
    Functor.map_comp, Category.assoc, appendFlag_last_step, ← Category.assoc, h,
    Category.assoc]

section PullbackExtension
variable {P : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
  {Z : C} (r : P ⟶ Z)

/-- Pull back the old flag, prefix a genuine zero, and append the new target.
All required pullbacks are supplied by the exact-category axioms. -/
def extendedPullbackFlag : ComposableArrows C (n + 1 + 1) := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact zeroPrefixFlag (appendFlag (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r))

/-- The extended flag is admissible from ordinary inflation/deflation data. -/
theorem extendedPullbackFlag_inflation
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f)) (hr : E.inflation r)
    {i j : Fin (n + 1 + 1 + 1)} (f : i ⟶ j) :
    E.inflation ((extendedPullbackFlag E A p hp r).map f) := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact zeroPrefixFlag_inflation E _
    (appendFlag_inflation E _ _ (pullbackFlag_inflation E A p hp hA)
      (E.inflation_comp _ _ (E.inflation_of_iso (pullbackFlagTopIso A p)) hr)) f

@[simp]
theorem extendedPullbackFlag_obj_zero :
    (extendedPullbackFlag E A p hp r).obj 0 = (0 : C) := rfl

@[simp]
theorem extendedPullbackFlag_obj_last :
    (extendedPullbackFlag E A p hp r).obj (Fin.last (n + 1 + 1)) = Z := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact appendFlag_obj_last (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)

variable [∀ i : Fin (n + 1), HasPullback p (flagTopMap A i)]

@[simp]
theorem extendedPullbackFlag_obj_middle (i : Fin (n + 1)) :
    (extendedPullbackFlag E A p hp r).obj i.castSucc.succ = (pullbackFlag A p).obj i :=
  appendFlag_obj_castSucc (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r) i

/-- The actual middle terms and arrows of the extension recover the pullback flag. -/
def extendedPullbackFlagMiddleIso :
    (Fin.castSuccFunctor (n + 1) ⋙ Fin.succFunctor (n + 1 + 1)) ⋙
      extendedPullbackFlag E A p hp r ≅ pullbackFlag A p :=
  appendFlagRestrictionIso (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)

/-- The actual inclusion of every middle term into the final target is its
pullback projection followed by the prescribed inflation. -/
theorem extendedPullbackFlag_middle_to_last (i : Fin (n + 1)) :
    (extendedPullbackFlag E A p hp r).map (homOfLE (Fin.le_last i.castSucc.succ)) ≫
        eqToHom (extendedPullbackFlag_obj_last E A p hp r) =
      eqToHom (extendedPullbackFlag_obj_middle E A p hp r i) ≫
        pullback.fst p (flagTopMap A i) ≫ r := by
  change (appendFlag (pullbackFlag A p) ((pullbackFlagTopIso A p).hom ≫ r)).map
    (homOfLE (Fin.le_last i.castSucc)) ≫ _ = _
  rw [appendFlag_to_last]
  simp only [pullbackFlagTopIso_hom, Category.assoc]
  exact congrArg (fun t ↦ eqToHom (extendedPullbackFlag_obj_middle E A p hp r i) ≫ t)
    (pullbackFlag_map_fst_assoc A p (homOfLE (Fin.le_last i)) r)

end PullbackExtension

end Quillen.Waldhausen.QuillenComparison

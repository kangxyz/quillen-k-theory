import Quillen.Topology.ClassifyingSpace.Basic

/-!
# Maps on genuine homotopy groups

A basepoint-preserving continuous map acts on generalized loops by
postcomposition. Postcomposition takes homotopies relative to the boundary
to homotopies relative to the boundary, and commutes with concatenation.
It therefore descends to group homomorphisms on mathlib's actual homotopy
groups. Applying this to the realization of the nerve of a functor gives
maps on the shifted homotopy groups of based classifying spaces.
-/

noncomputable section

open scoped Topology unitInterval
open CategoryTheory

universe w v u

namespace Quillen

section ContinuousMaps

variable {N : Type w} {X : Type u} {Y : Type v} {Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- Postcomposition of a generalized loop by a pointed continuous map. -/
def genLoopPostcomp (f : C(X, Y)) (h : f x = y) (p : GenLoop N X x) :
    GenLoop N Y y :=
  ⟨f.comp p.val, fun t ht => (congrArg f (p.property t ht)).trans h⟩

@[simp]
theorem genLoopPostcomp_apply (f : C(X, Y)) (h : f x = y)
    (p : GenLoop N X x) (t : N → unitInterval) :
    genLoopPostcomp f h p t = f (p t) := rfl

/-- Postcomposition respects homotopies fixed on the cube boundary. -/
theorem genLoopPostcomp_homotopic (f : C(X, Y)) (h : f x = y)
    {p q : GenLoop N X x} (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopPostcomp f h p) (genLoopPostcomp f h q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap H f

@[simp]
theorem genLoopPostcomp_const (f : C(X, Y)) (h : f x = y) :
    genLoopPostcomp (N := N) f h GenLoop.const = GenLoop.const := by
  ext t
  exact h

/-- Postcomposition commutes with concatenation in every cube direction. -/
@[simp]
theorem genLoopPostcomp_transAt [DecidableEq N] (f : C(X, Y)) (h : f x = y)
    (i : N) (p q : GenLoop N X x) :
    genLoopPostcomp f h (GenLoop.transAt i p q) =
      GenLoop.transAt i (genLoopPostcomp f h p) (genLoopPostcomp f h q) := by
  ext t
  simp only [genLoopPostcomp_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- The map on the homotopy quotient induced by a pointed continuous map.
This also makes sense for the zeroth homotopy set. -/
def homotopyGroupMap (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (genLoopPostcomp f h) (fun _ _ H => genLoopPostcomp_homotopic f h H)

@[simp]
theorem homotopyGroupMap_mk (f : C(X, Y)) (h : f x = y) (p : GenLoop N X x) :
    homotopyGroupMap f h (Quotient.mk' p) = Quotient.mk' (genLoopPostcomp f h p) := rfl

/-- On positive-dimensional homotopy groups, the induced map is a group
homomorphism. Multiplication is the existing mathlib group multiplication. -/
def homotopyGroupMapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := homotopyGroupMap f h
  map_one' := by
    change Quotient.mk' (genLoopPostcomp f h GenLoop.const) = Quotient.mk' GenLoop.const
    rw [genLoopPostcomp_const]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b (fun p q => ?_)
    simp only [HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    exact (congrArg Quotient.mk' (genLoopPostcomp_transAt f h _ q p)).trans
      (HomotopyGroup.mul_spec (i := Classical.arbitrary N)).symm

@[simp]
theorem homotopyGroupMap_id (a : HomotopyGroup N X x) :
    homotopyGroupMap (ContinuousMap.id X) rfl a = a := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply congrArg Quotient.mk'
  ext t
  rfl

@[simp]
theorem homotopyGroupMap_comp (f : C(X, Y)) (hf : f x = y)
    (g : C(Y, Z)) (hg : g y = z) (a : HomotopyGroup N X x) :
    homotopyGroupMap (g.comp f) ((congrArg g hf).trans hg) a =
      homotopyGroupMap g hg (homotopyGroupMap f hf a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  rfl

@[simp]
theorem homotopyGroupMapHom_apply [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (h : f x = y) (a : HomotopyGroup N X x) :
    homotopyGroupMapHom f h a = homotopyGroupMap f h a := rfl

@[simp]
theorem homotopyGroupMapHom_id [DecidableEq N] [Nonempty N] :
    homotopyGroupMapHom (N := N) (x := x) (ContinuousMap.id X) rfl =
      MonoidHom.id (HomotopyGroup N X x) := by
  ext a
  exact homotopyGroupMap_id a

@[simp]
theorem homotopyGroupMapHom_comp [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) (g : C(Y, Z)) (hg : g y = z) :
    homotopyGroupMapHom (N := N) (g.comp f) ((congrArg g hf).trans hg) =
      (homotopyGroupMapHom g hg).comp (homotopyGroupMapHom f hf) := by
  ext a
  exact homotopyGroupMap_comp f hf g hg a

/-- The induced homomorphism on the actual `(n + 1)`st homotopy group. -/
abbrev piMap (n : ℕ) (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  homotopyGroupMapHom f h

/-- A based homotopy of maps gives a homotopy of their postcomposed
loops relative to the entire cube boundary. -/
def genLoopPostcompHomotopy {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) (p : GenLoop N X x) :
    (genLoopPostcomp f hf p).val.HomotopyRel (genLoopPostcomp g hg p).val
      (Cube.boundary N) where
  toHomotopy := H.compContinuousMap p.val
  prop' t z hz := by
    change H (t, p z) = f (p z)
    rw [GenLoop.boundary p z hz, hH t, hf]

/-- Based homotopic continuous maps induce equal maps on the homotopy set. -/
theorem homotopyGroupMap_eq_of_based_homotopy {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    homotopyGroupMap (N := N) f hf = homotopyGroupMap g hg := by
  funext a
  refine Quotient.inductionOn a (fun p => ?_)
  exact Quotient.sound ⟨genLoopPostcompHomotopy hf hg H hH p⟩

/-- Based homotopic continuous maps induce equal homotopy-group homomorphisms. -/
theorem homotopyGroupMapHom_eq_of_based_homotopy [DecidableEq N] [Nonempty N]
    {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    homotopyGroupMapHom (N := N) f hf = homotopyGroupMapHom g hg := by
  ext a
  exact congrFun (homotopyGroupMap_eq_of_based_homotopy hf hg H hH) a

/-- Based homotopic continuous maps induce equal maps on `π_(n+1)`. -/
theorem piMap_eq_of_based_homotopy (n : ℕ) {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    piMap n f hf = piMap n g hg :=
  homotopyGroupMapHom_eq_of_based_homotopy hf hg H hH

/-- A constant map sends every generalized loop to the constant loop. -/
@[simp]
theorem genLoopPostcomp_constant (p : GenLoop N X x) :
    genLoopPostcomp (ContinuousMap.const X y) rfl p = GenLoop.const := by
  ext t
  rfl

/-- The homomorphism induced by a constant map is trivial. -/
@[simp]
theorem homotopyGroupMapHom_const [DecidableEq N] [Nonempty N] :
    homotopyGroupMapHom (N := N) (x := x) (ContinuousMap.const X y) rfl = 1 := by
  ext a
  refine Quotient.inductionOn a (fun p => ?_)
  change Quotient.mk' (genLoopPostcomp (ContinuousMap.const X y) rfl p) =
    Quotient.mk' GenLoop.const
  rw [genLoopPostcomp_constant]

/-- The induced map on `π_(n+1)` of a constant map is trivial. -/
@[simp]
theorem piMap_const (n : ℕ) :
    piMap n (x := x) (ContinuousMap.const X y) rfl = 1 :=
  homotopyGroupMapHom_const

/-- A nullhomotopy that stays fixed at the basepoint makes the induced
homomorphism trivial. -/
theorem piMap_eq_one_of_based_nullhomotopy (n : ℕ) {f : C(X, Y)}
    (hf : f x = y) (H : f.Homotopy (ContinuousMap.const X y))
    (hH : ∀ t, H (t, x) = y) : piMap n f hf = 1 := by
  exact (piMap_eq_of_based_homotopy n hf rfl H hH).trans (piMap_const n)


end ContinuousMaps

section ClassifyingSpaces

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]

/-- A functor induces a homomorphism on the shifted homotopy groups of
classifying spaces, based at an object and its image. -/
def shiftedHomotopyGroupMap (F : C ⥤ D) (c : C) (n : ℕ) :
    ShiftedHomotopyGroup C c n →* ShiftedHomotopyGroup D (F.obj c) n :=
  piMap n (classifyingSpaceMap F).hom (classifyingSpaceMap_point F c)

/-- Realization of the nerve preserves identity functors. -/
@[simp]
theorem classifyingSpaceMap_id :
    classifyingSpaceMap (𝟭 C) = 𝟙 (ClassifyingSpace C) := by
  unfold classifyingSpaceMap
  change SSet.toTop.map (𝟙 (CategoryTheory.nerve C)) = _
  exact SSet.toTop.map_id _

/-- Realization of the nerve preserves composition of functors. -/
@[simp]
theorem classifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  unfold classifyingSpaceMap
  change SSet.toTop.map (CategoryTheory.nerveMap F ≫ CategoryTheory.nerveMap G) = _
  exact SSet.toTop.map_comp _ _

@[simp]
theorem shiftedHomotopyGroupMap_id (c : C) (n : ℕ) :
    shiftedHomotopyGroupMap (𝟭 C) c n = MonoidHom.id (ShiftedHomotopyGroup C c n) := by
  unfold shiftedHomotopyGroupMap piMap
  simp only [classifyingSpaceMap_id, TopCat.hom_id]
  exact homotopyGroupMapHom_id

@[simp]
theorem shiftedHomotopyGroupMap_comp {E : Type u} [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) (c : C) (n : ℕ) :
    shiftedHomotopyGroupMap (F ⋙ G) c n =
      (shiftedHomotopyGroupMap G (F.obj c) n).comp (shiftedHomotopyGroupMap F c n) := by
  unfold shiftedHomotopyGroupMap piMap
  simp only [classifyingSpaceMap_comp, TopCat.hom_comp]
  exact homotopyGroupMapHom_comp _ _ _ _

end ClassifyingSpaces

end Quillen

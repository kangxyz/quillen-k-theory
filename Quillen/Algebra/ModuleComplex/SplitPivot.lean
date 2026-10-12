/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.Module.FiniteParametrix
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Split-pivot replacement of a whole cochain complex

Given a cochain complex `C`, a degree `k`, and an actual splitting
`d s + r t = id` of the enlarged differential `[d,r]`, replace degrees `k` and
`k + 1` by `ker[d,r]` and `G`. The middle differential is minus the second
projection. The incoming differential is `(d,0)` and the outgoing one is `d r`.

The explicit forward and backward chain maps come with homotopies in every
degree, giving `homotopyEquiv` for the whole complex. No finiteness or
projectivity assumption is needed for this equivalence. If `C.X k` and `G` are
projective, the kernel is projective; finite-projectivity of `G` is retained in
degree `k + 1`. An original lower zero bound at or below `k` is preserved.

This is a single replacement step over an arbitrary commutative ring. It does
not assert the finite-domination induction or impose noetherian hypotheses.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.Module
universe u v
namespace Quillen.ModuleComplex.SplitPivot
variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℤ)
  (k : ℤ) (G : ModuleCat.{v} R)
  (s : C.X (k + 1) →ₗ[R] C.X k) (r : G →ₗ[R] C.X (k + 1))
  (t : C.X (k + 1) →ₗ[R] G)
  (hs : (C.d k (k + 1)).hom.comp s + r.comp t = LinearMap.id)

/-- The actual kernel of the enlarged pivot differential `[d,r]`. -/
abbrev kernelModule := LinearMap.ker (parametrixTotal (C.d k (k + 1)).hom r)

/-- The original incoming differential, with zero in the added summand. -/
def incoming : C.X (k - 1) →ₗ[R] kernelModule C k G r :=
  ((C.d (k - 1) k).hom.prod 0).codRestrict _ (by
    intro x
    change C.d k (k + 1) (C.d (k - 1) k x) + r 0 = 0
    rw [map_zero, add_zero]
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
      (C.d_comp_d (k - 1) k (k + 1))) x)

/-- Replace only the two pivot objects; all other degrees retain the original objects. -/
def objects (i : ℤ) : ModuleCat.{v} R :=
  if i = k then ModuleCat.of R (kernelModule C k G r) else if i = k + 1 then G else C.X i

/-- The lower pivot object is the actual split-surjection kernel. -/
def lowerIso : objects C k G r k ≅ ModuleCat.of R (kernelModule C k G r) :=
  eqToIso (by simp [objects])
/-- The upper pivot object is the specified added module. -/
def upperIso : objects C k G r (k + 1) ≅ G :=
  eqToIso (by simp [objects, show k + 1 ≠ k by omega])
/-- Away from the pivot, the replacement object is the original object. -/
def otherIso (i : ℤ) (h : i ≠ k) (h' : i ≠ k + 1) : objects C k G r i ≅ C.X i :=
  eqToIso (by simp [objects, h, h'])

/-- The adjacent replacement differentials are `(d,0)`, `−snd`, and `d r`. -/
def differential (i : ℤ) : objects C k G r i ⟶ objects C k G r (i + 1) :=
  if h : i = k - 1 then
    eqToHom (congrArg (objects C k G r) h) ≫
      (otherIso C k G r (k - 1) (by omega) (by omega)).hom ≫
      ModuleCat.ofHom (incoming C k G r) ≫ (lowerIso C k G r).inv ≫
      eqToHom (congrArg (objects C k G r) (by omega : k = i + 1))
  else if h' : i = k then
    eqToHom (congrArg (objects C k G r) h') ≫ (lowerIso C k G r).hom ≫
      ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) ≫
      (upperIso C k G r).inv ≫ eqToHom (by rw [h'])
  else if h'' : i = k + 1 then
    eqToHom (congrArg (objects C k G r) h'') ≫ (upperIso C k G r).hom ≫
      ModuleCat.ofHom r ≫ C.d (k + 1) (k + 1 + 1) ≫
      (otherIso C k G r _ (by omega) (by omega)).inv ≫ eqToHom (by rw [h''])
  else (otherIso C k G r _ h' h'').hom ≫ C.d i (i + 1) ≫
    (otherIso C k G r _ (by omega) (by omega)).inv

/-- The incoming map lands in the kernel of the middle differential. -/
@[reassoc]
theorem incoming_middle :
    ModuleCat.ofHom (incoming C k G r) ≫
      ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change -(0 : G) = 0
  exact neg_zero

/-- The kernel relation and original square-zero identity kill the outgoing composite. -/
@[reassoc]
theorem middle_outgoing :
    ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) ≫
      ModuleCat.ofHom r ≫ C.d (k + 1) (k + 1 + 1) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change C.d (k + 1) (k + 1 + 1) (r (-x.val.2)) = 0
  have hx : C.d k (k + 1) x.val.1 + r x.val.2 = 0 := x.property
  rw [map_neg, ← eq_neg_of_add_eq_zero_left hx]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
    (C.d_comp_d k (k + 1) (k + 1 + 1))) x.val.1

/-- The original preceding differential is killed by the new incoming map. -/
@[reassoc]
theorem preceding_incoming (i : ℤ) :
    C.d i (k - 1) ≫ ModuleCat.ofHom (incoming C k G r) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change C.d (k - 1) k (C.d i (k - 1) x) = 0
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
      (C.d_comp_d i (k - 1) k)) x
  · rfl

/-- The specified replacement differentials square to zero in every degree. -/
theorem differential_sq (i : ℤ) :
    differential C k G r i ≫ differential C k G r (i + 1) = 0 := by
  unfold differential
  split_ifs <;> try omega
  all_goals try subst i
  all_goals simp_all [otherIso, lowerIso, upperIso, Category.assoc,
    incoming_middle_assoc, middle_outgoing_assoc, preceding_incoming_assoc]

/-- The actual cochain complex obtained by the split-pivot replacement. -/
def replacement : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.of (objects C k G r) (differential C k G r) (differential_sq C k G r)

/-- The forward components are the split-kernel projection, `t`, and identity transports. -/
def forwardComponent (i : ℤ) : C.X i ⟶ (replacement C k G r).X i :=
  if h : i = k then
    eqToHom (congrArg C.X h) ≫
      ModuleCat.ofHom (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) ≫
      (lowerIso C k G r).inv ≫ eqToHom (congrArg (objects C k G r) h.symm)
  else if h' : i = k + 1 then
    eqToHom (congrArg C.X h') ≫ ModuleCat.ofHom t ≫ (upperIso C k G r).inv ≫
      eqToHom (congrArg (objects C k G r) h'.symm)
  else (otherIso C k G r i h h').inv

/-- The backward components are the first projection, `r`, and identity transports. -/
def backwardComponent (i : ℤ) : (replacement C k G r).X i ⟶ C.X i :=
  if h : i = k then
    eqToHom (congrArg (objects C k G r) h) ≫ (lowerIso C k G r).hom ≫
      ModuleCat.ofHom (parametrixBackwardSource (C.d k (k + 1)).hom r) ≫
      eqToHom (congrArg C.X h.symm)
  else if h' : i = k + 1 then
    eqToHom (congrArg (objects C k G r) h') ≫ (upperIso C k G r).hom ≫
      ModuleCat.ofHom r ≫ eqToHom (congrArg C.X h'.symm)
  else (otherIso C k G r i h h').hom

/-- The signed middle differential commutes with the actual forward components. -/
@[reassoc]
theorem forward_middle :
    ModuleCat.ofHom (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) ≫
      ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) =
      C.d k (k + 1) ≫ ModuleCat.ofHom t := by
  apply ModuleCat.hom_ext
  change (-parametrixReplacementDifferential (C.d k (k + 1)).hom r).comp
    (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) = _
  rw [LinearMap.neg_comp, parametrixForward_chain, LinearMap.neg_comp, neg_neg]
  rfl

/-- The signed middle differential commutes with the actual backward components. -/
@[reassoc]
theorem backward_middle :
    ModuleCat.ofHom (parametrixBackwardSource (C.d k (k + 1)).hom r) ≫ C.d k (k + 1) =
      ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) ≫
        ModuleCat.ofHom r := by
  apply ModuleCat.hom_ext
  change (C.d k (k + 1)).hom.comp
    (parametrixBackwardSource (C.d k (k + 1)).hom r) =
      r.comp (-parametrixReplacementDifferential (C.d k (k + 1)).hom r)
  rw [parametrixBackward_chain, LinearMap.neg_comp, LinearMap.comp_neg]

/-- The forward lower component agrees with the original incoming differential. -/
theorem forward_preceding :
    ModuleCat.ofHom (incoming C k G r) = C.d (k - 1) k ≫
      ModuleCat.ofHom (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (LinearMap.congr_fun
    (parametrixKernelRetraction_subtype (C.d k (k + 1)).hom s r t hs)
      (incoming C k G r x)).symm

/-- The first projection recovers the original incoming differential. -/
@[reassoc]
theorem backward_preceding :
    ModuleCat.ofHom (incoming C k G r) ≫
      ModuleCat.ofHom (parametrixBackwardSource (C.d k (k + 1)).hom r) =
        C.d (k - 1) k := rfl

include hs in
/-- The splitting identity makes the forward map commute at the upper pivot. -/
@[reassoc]
theorem forward_following :
    ModuleCat.ofHom t ≫ ModuleCat.ofHom r ≫ C.d (k + 1) (k + 1 + 1) =
      C.d (k + 1) (k + 1 + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hz := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp
    (C.d_comp_d k (k + 1) (k + 1 + 1))) (s x)
  change C.d (k + 1) (k + 1 + 1) (C.d k (k + 1) (s x)) = 0 at hz
  have hx := congrArg (fun y => C.d (k + 1) (k + 1 + 1) y) (LinearMap.congr_fun hs x)
  change C.d (k + 1) (k + 1 + 1) (C.d k (k + 1) (s x) + r (t x)) =
    C.d (k + 1) (k + 1 + 1) x at hx
  rw [map_add, hz, zero_add] at hx
  exact hx

/-- The forward components commute with all adjacent differentials. -/
theorem forward_comm (i : ℤ) :
    forwardComponent C k G s r t hs i ≫ (replacement C k G r).d i (i + 1) =
      C.d i (i + 1) ≫ forwardComponent C k G s r t hs (i + 1) := by
  simp only [replacement, CochainComplex.of_d]
  unfold forwardComponent differential
  split_ifs <;> try omega
  all_goals try subst i
  all_goals simp_all [otherIso, lowerIso, upperIso, Category.assoc,
    forward_middle_assoc, forward_following_assoc C k G s r t hs,
    forward_preceding C k G s r t hs]

/-- The backward components commute with all adjacent differentials. -/
theorem backward_comm (i : ℤ) :
    backwardComponent C k G r i ≫ C.d i (i + 1) =
      (replacement C k G r).d i (i + 1) ≫ backwardComponent C k G r (i + 1) := by
  simp only [replacement, CochainComplex.of_d]
  unfold backwardComponent differential
  split_ifs <;> try omega
  all_goals try subst i
  all_goals simp_all [otherIso, lowerIso, upperIso, Category.assoc,
    backward_middle, backward_preceding_assoc]

/-- The actual forward chain map from the original complex to its replacement. -/
def forward : C ⟶ replacement C k G r :=
  CochainComplex.ofHom (forwardComponent C k G s r t hs) (forward_comm C k G s r t hs)

/-- The actual backward chain map from the replacement to the original complex. -/
def backward : replacement C k G r ⟶ C :=
  CochainComplex.ofHom (backwardComponent C k G r) (backward_comm C k G r)

/-- The original homotopy is `s` from degree `k + 1` to `k`, and zero elsewhere. -/
def originalHomotopyComponent (i j : ℤ) : C.X i ⟶ C.X j :=
  if h : i = k + 1 ∧ j = k then
    eqToHom (congrArg C.X h.1) ≫ ModuleCat.ofHom s ≫ eqToHom (congrArg C.X h.2.symm)
  else 0

/-- The replacement homotopy is `(s r, t r − id)` at the pivot, and zero elsewhere. -/
def replacementHomotopyComponent (i j : ℤ) :
    (replacement C k G r).X i ⟶ (replacement C k G r).X j :=
  if h : i = k + 1 ∧ j = k then
    eqToHom (congrArg (objects C k G r) h.1) ≫ (upperIso C k G r).hom ≫
      ModuleCat.ofHom (-parametrixReplacementHomotopy (C.d k (k + 1)).hom s r t hs) ≫
      (lowerIso C k G r).inv ≫ eqToHom (congrArg (objects C k G r) h.2.symm)
  else 0

/-- The lower original homotopy identity uses the specified parametrix. -/
theorem original_lower_identity :
    𝟙 (C.X k) = C.d k (k + 1) ≫ ModuleCat.ofHom s +
      ModuleCat.ofHom (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) ≫
        ModuleCat.ofHom (parametrixBackwardSource (C.d k (k + 1)).hom r) := by
  apply ModuleCat.hom_ext
  change LinearMap.id = s.comp (C.d k (k + 1)).hom +
    (parametrixBackwardSource (C.d k (k + 1)).hom r).comp
      (parametrixForwardSource (C.d k (k + 1)).hom s r t hs)
  rw [parametrixBackward_forward_zero]
  abel

include hs in
/-- The upper original homotopy identity is the given splitting identity. -/
theorem original_upper_identity :
    𝟙 (C.X (k + 1)) = ModuleCat.ofHom s ≫ C.d k (k + 1) +
      ModuleCat.ofHom t ≫ ModuleCat.ofHom r :=
  ModuleCat.hom_ext hs.symm

/-- The lower replacement homotopy identity holds on the actual kernel. -/
theorem replacement_lower_identity :
    𝟙 (ModuleCat.of R (kernelModule C k G r)) =
      ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) ≫
        ModuleCat.ofHom (-parametrixReplacementHomotopy (C.d k (k + 1)).hom s r t hs) +
      ModuleCat.ofHom (parametrixBackwardSource (C.d k (k + 1)).hom r) ≫
        ModuleCat.ofHom (parametrixForwardSource (C.d k (k + 1)).hom s r t hs) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x =
    -(parametrixReplacementHomotopy (C.d k (k + 1)).hom s r t hs
      (-parametrixReplacementDifferential (C.d k (k + 1)).hom r x)) +
    parametrixForwardSource (C.d k (k + 1)).hom s r t hs
      (parametrixBackwardSource (C.d k (k + 1)).hom r x)
  rw [map_neg, neg_neg]
  exact (LinearMap.congr_fun
    (parametrixForward_backward_zero_add (C.d k (k + 1)).hom s r t hs) x).symm.trans
      (add_comm _ _)

/-- The upper replacement homotopy identity holds on the specified added module. -/
theorem replacement_upper_identity :
    𝟙 G =
      ModuleCat.ofHom (-parametrixReplacementHomotopy (C.d k (k + 1)).hom s r t hs) ≫
        ModuleCat.ofHom (-parametrixReplacementDifferential (C.d k (k + 1)).hom r) +
      ModuleCat.ofHom r ≫ ModuleCat.ofHom t := by
  apply ModuleCat.hom_ext
  change LinearMap.id =
    (-parametrixReplacementDifferential (C.d k (k + 1)).hom r).comp
      (-parametrixReplacementHomotopy (C.d k (k + 1)).hom s r t hs) + t.comp r
  have h := parametrixForward_backward_one_add (C.d k (k + 1)).hom s r t hs
  simpa only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, add_comm] using h.symm

/-- The identity of the original whole complex is homotopic to the forward-backward composite. -/
def originalHomotopy : Homotopy (𝟙 C)
    (forward C k G s r t hs ≫ backward C k G r) where
  hom := originalHomotopyComponent C k s
  zero i j hij := by
    unfold originalHomotopyComponent
    split_ifs with h
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by dsimp; omega)]
    change 𝟙 (C.X i) = C.d i (i + 1) ≫ originalHomotopyComponent C k s (i + 1) i +
      originalHomotopyComponent C k s i (i - 1) ≫ C.d (i - 1) i +
      forwardComponent C k G s r t hs i ≫ backwardComponent C k G r i
    unfold originalHomotopyComponent forwardComponent backwardComponent
    split_ifs <;> try omega
    all_goals try subst i
    all_goals first
      | solve | simp_all [otherIso, lowerIso, upperIso, Category.assoc]
      | solve | simpa [otherIso, lowerIso, upperIso, Category.assoc] using
          original_lower_identity C k G s r t hs
      | solve | simpa [otherIso, lowerIso, upperIso, Category.assoc] using
          original_upper_identity C k G s r t hs

/-- The identity of the replacement whole complex is homotopic to the backward-forward composite. -/
def replacementHomotopy : Homotopy (𝟙 (replacement C k G r))
    (backward C k G r ≫ forward C k G s r t hs) where
  hom := replacementHomotopyComponent C k G s r t hs
  zero i j hij := by
    unfold replacementHomotopyComponent
    split_ifs with h
    · exfalso
      apply hij
      change j + 1 = i
      omega
    · rfl
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by dsimp; omega)]
    change 𝟙 ((replacement C k G r).X i) =
      (replacement C k G r).d i (i + 1) ≫
        replacementHomotopyComponent C k G s r t hs (i + 1) i +
      replacementHomotopyComponent C k G s r t hs i (i - 1) ≫
        (replacement C k G r).d (i - 1) i +
      backwardComponent C k G r i ≫ forwardComponent C k G s r t hs i
    simp only [replacement, CochainComplex.of.d,
      sub_add_cancel, dite_eq_left, eqToHom_refl, Category.comp_id]
    unfold replacementHomotopyComponent backwardComponent forwardComponent differential
    split_ifs <;> try omega
    all_goals try subst i
    all_goals first
      | solve | simp_all [otherIso, lowerIso, upperIso, Category.assoc]
      | solve
        | have h := congrArg (fun f => (lowerIso C k G r).hom ≫ f ≫
            (lowerIso C k G r).inv) (replacement_lower_identity C k G s r t hs)
          simpa [otherIso, lowerIso, upperIso, Category.assoc,
            Preadditive.comp_add, Preadditive.add_comp] using h
      | solve
        | have h := congrArg (fun f => (upperIso C k G r).hom ≫ f ≫
            (upperIso C k G r).inv) (replacement_upper_identity C k G s r t hs)
          simpa [otherIso, lowerIso, upperIso, Category.assoc,
            Preadditive.comp_add, Preadditive.add_comp] using h

/-- The specified chain maps and both whole-complex homotopies form a homotopy equivalence. -/
def homotopyEquiv : HomotopyEquiv C (replacement C k G r) where
  hom := forward C k G s r t hs
  inv := backward C k G r
  homotopyHomInvId := (originalHomotopy C k G s r t hs).symm
  homotopyInvHomId := (replacementHomotopy C k G s r t hs).symm

include hs in
/-- The kernel is projective when the original lower object and added module are projective. -/
theorem projective_kernel [Module.Projective R (C.X k)] [Module.Projective R G] :
    Module.Projective R (kernelModule C k G r) :=
  Module.Projective.of_split (LinearMap.ker (parametrixTotal (C.d k (k + 1)).hom r)).subtype
    (parametrixKernelRetraction (C.d k (k + 1)).hom s r t hs)
    (parametrixKernelRetraction_subtype (C.d k (k + 1)).hom s r t hs)

/-- A finite added module gives a finite upper replacement term. -/
theorem finite_replacement_upper [Module.Finite R G] :
    Module.Finite R ((replacement C k G r).X (k + 1)) :=
  Module.Finite.equiv (upperIso C k G r).toLinearEquiv.symm

/-- A projective added module gives a projective upper replacement term. -/
theorem projective_replacement_upper [Module.Projective R G] :
    Module.Projective R ((replacement C k G r).X (k + 1)) :=
  Module.Projective.of_equiv (upperIso C k G r).toLinearEquiv.symm

/-- Every original lower zero bound at or below the pivot is preserved. -/
theorem replacement_preserves_lower_bound (a : ℤ) (ha : a ≤ k)
    (hC : ∀ i, i < a → IsZero (C.X i)) (i : ℤ) (hi : i < a) :
    IsZero ((replacement C k G r).X i) :=
  (hC i hi).of_iso (otherIso C k G r i (by omega) (by omega))

end Quillen.ModuleComplex.SplitPivot

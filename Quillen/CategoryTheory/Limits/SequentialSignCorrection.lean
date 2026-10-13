/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
Alternating actual stage inversions turn proved anti-commuting successor squares into a natural
isomorphism.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Preadditive
universe u v
namespace Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Successive stages carry successive genuine additive sign inversions. -/
def alternatingIso {X Y : C} (n : ℕ) (e : X ≅ Y) : X ≅ Y :=
  Nat.rec e (fun _ e ↦ -e) n

@[simp] lemma alternatingIso_zero {X Y : C} (e : X ≅ Y) : alternatingIso 0 e = e := rfl
@[simp] lemma alternatingIso_succ {X Y : C} (n : ℕ) (e : X ≅ Y) :
    alternatingIso (n + 1) e = -alternatingIso n e := rfl

lemma alternatingIso_hom {X Y : C} (n : ℕ) (e : X ≅ Y) :
    (alternatingIso n e).hom = (-1 : ℤ)^n • e.hom := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ]

/-- An actual anti-commuting successor square becomes a commuting square after
alternating original stage inversions. -/
lemma alternatingIso_naturality {X Y X' Y' : C} (n : ℕ)
    (f : X ⟶ X') (g : Y ⟶ Y') (e : X ≅ Y) (e' : X' ≅ Y')
    (h : f ≫ e'.hom = -(e.hom ≫ g)) :
    f ≫ (alternatingIso (n + 1) e').hom = (alternatingIso n e).hom ≫ g := by
  rw [alternatingIso_hom, alternatingIso_hom, comp_zsmul, zsmul_comp, h]
  simp [pow_succ]

/-- Original level isomorphisms with actual anti-commuting transition squares
induce a natural isomorphism after the displayed sign correction. -/
def sequentialSignCorrectionIso {F G : ℕ ⥤ C} (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) : F ≅ G := by
  let η : F ⟶ G := NatTrans.ofSequence (fun n ↦ (alternatingIso n (e n)).hom)
    (fun n ↦ alternatingIso_naturality n _ _ _ _ (h n))
  exact NatIso.ofComponents (fun n ↦ alternatingIso n (e n)) (fun {_ _} f ↦ η.naturality f)

@[simp] lemma sequentialSignCorrectionIso_hom_app {F G : ℕ ⥤ C}
    (e : ∀ n, F.obj n ≅ G.obj n)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (e (n + 1)).hom =
      -((e n).hom ≫ G.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    (sequentialSignCorrectionIso e h).hom.app n = (-1 : ℤ)^n • (e n).hom :=
  alternatingIso_hom n (e n)

end Quillen

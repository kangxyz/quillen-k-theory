/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SquareCone
public import Quillen.Topology.Prespectrum.Telescope
public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum

/-! # Original-map consumers of concrete prespectrum cones and telescopes -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
open Quillen Quillen.LoopPrespectrum
universe u v
namespace QuillenTest.PrespectrumCofibers

open Quillen
variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The cone nullhomotopy commutes at independent original cylinder and loop parameters. -/
theorem full_cone_cylinder (n : ℕ) (s t : unitInterval) (x : E.space n) :
    (mappingConeHomotopy f).level (n+1) (s,E.structureMap n x t) =
      (mappingCone f).structureMap n ((mappingConeHomotopy f).level n (s,x)) t ∧
    (mappingConeHomotopy f).at 0 = f ≫ mappingConeInclusion f ∧
    (mappingConeHomotopy f).at 1 = zeroHom E (mappingCone f) :=
  ⟨(mappingConeHomotopy f).comm n s x t,
    (mappingConeHomotopy f).at_zero_eq, (mappingConeHomotopy f).at_one_eq⟩

/-- The unchanged inclusion composite induces the trivial map on every positive level group. -/
theorem original_cone_homotopy_map (n k : ℕ) :
    piMap k ((f ≫ mappingConeInclusion f).map n) ((f ≫ mappingConeInclusion f).map_point n) = 1 :=
  piMap_eq_one_of_based_nullhomotopy k _
    ((mappingConeHomotopy f).levelHomotopy n).toHomotopy ((mappingConeHomotopy f).at_point n)

/-- The specified original nullhomotopy, not just its existence, determines a unique cone map. -/
theorem unique_cone_descent (g : F ⟶ G) (H : Homotopy (f ≫ g) (zeroHom E G)) :
    ∃! d : mappingCone f ⟶ G, mappingConeInclusion f ≫ d = g ∧
      ∀ n s x, d.map n (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s,x)) =
        H.level n (s,x) := by
  refine ⟨mappingConeDesc f g H, ⟨mappingConeInclusion_desc f g H, fun _ _ _ ↦ rfl⟩, ?_⟩
  intro d hd
  apply mappingCone_hom_ext f
  · exact hd.1.trans (mappingConeInclusion_desc f g H).symm
  · intro n s x
    exact hd.2 n s x

/-- The cone functor retains the whole original strict square at both time-independent pieces. -/
theorem cone_square_components {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) (n : ℕ)
    (y : A.right.space n) (s : unitInterval) (x : A.left.space n) :
    (mappingConeMap sq).map n (ReducedMappingCone.inr (A.left.point n) (A.right.point n) (A.hom.map
      n) y) =
      ReducedMappingCone.inr (B.left.point n) (B.right.point n) (B.hom.map n) (sq.right.map n y) ∧
    (mappingConeMap sq).map n (ReducedMappingCone.cylinder (A.left.point n) (A.right.point n)
      (A.hom.map n) (s,x)) =
      ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n) (s,sq.left.map n
        x) := ⟨rfl,rfl⟩

/-- Looping is an actual functor, and stabilization retains the original structure map. -/
theorem original_looping (g : F ⟶ G) (n : ℕ) :
    loopingFunctor.map (f ≫ g) = loopingFunctor.map f ≫ loopingFunctor.map g ∧
    (stabilizationMap E).map n = E.structureMap n := ⟨loopingFunctor.map_comp f g,rfl⟩

variable (T : ℕ → LoopPrespectrum.{u}) (a : ∀ i, T i ⟶ T (i+1))

/-- Descending the genuine telescope cylinders recovers the identity on the whole telescope. -/
theorem telescope_actual_cylinders_identity :
    Telescope.desc T a (Telescope.inclusion T a) (Telescope.inclusionHomotopy T a) = 𝟙
      (Telescope.prespectrum T a) := by
  apply Telescope.hom_ext
  intro n i s x
  rfl

/-- An arbitrary specified coherent stage homotopy is retained at each interior cylinder point. -/
theorem telescope_specified_descent (g : ∀ i, T i ⟶ G) (H : ∀ i, Homotopy (g i) (a i ≫ g (i+1)))
    (n i : ℕ) (s t : unitInterval) (x : (T i).space n) :
    (Telescope.desc T a g H).map n (Telescope.cylinder T a n i (s,x)) = (H i).level n (s,x) ∧
    (H i).level (n+1) (s,(T i).structureMap n x t) = G.structureMap n ((H i).level n (s,x)) t :=
  ⟨rfl,(H i).comm n s x t⟩

/-- The original stage inclusions remain strictly natural under a map of sequential diagrams. -/
theorem telescope_original_map (T' : ℕ → LoopPrespectrum.{u}) (a' : ∀ i, T' i ⟶ T' (i+1))
    (b : ∀ i, T i ⟶ T' i) (hb : ∀ i, b i ≫ a' i = a i ≫ b (i+1)) (i : ℕ) :
    Telescope.inclusion T a i ≫ Telescope.map T a T' a' b hb = b i ≫ Telescope.inclusion T' a' i :=
  Telescope.inclusion_map T a T' a' b hb i

variable {A B C D : LoopPrespectrum.{u}} (p : A ⟶ B) (q : A ⟶ C)

/-- Both literal cylinder endpoints and both original basepoint identifications hold. -/
theorem double_cylinder_endpoints (n : ℕ) (x : A.space n) (s : unitInterval) :
    HomotopyPushout.cylinder p q n (0,x) = HomotopyPushout.left p q n (p.map n x) ∧
    HomotopyPushout.cylinder p q n (1,x) = HomotopyPushout.right p q n (q.map n x) ∧
    HomotopyPushout.cylinder p q n (s,A.point n) = HomotopyPushout.point p q n ∧
    HomotopyPushout.right p q n (C.point n) = HomotopyPushout.point p q n :=
  ⟨HomotopyPushout.cylinder_zero p q n x, HomotopyPushout.cylinder_one p q n x,
    HomotopyPushout.cylinder_point p q n s, HomotopyPushout.right_point p q n⟩

/-- Descending the original two inclusions and whole overlap homotopy recovers the identity. -/
theorem double_cylinder_identity :
    HomotopyPushout.desc p q (HomotopyPushout.inl p q) (HomotopyPushout.inr p q)
      (HomotopyPushout.glue p q) =
      𝟙 (HomotopyPushout.prespectrum p q) := by
  apply HomotopyPushout.hom_ext
  · simp only [HomotopyPushout.inl_desc, Category.comp_id]
  · simp only [HomotopyPushout.inr_desc, Category.comp_id]
  · intro n s x; rfl

/-- The displayed Bass-type transition retains every point of the supplied actual degree-raising
  arrow. -/
theorem original_square_cone_transition (b : B ⟶ D) (c : C ⟶ D) (H : Homotopy (p ≫ b) (q ≫ c))
    (u : A ⟶ looping D) (n : ℕ) (x : A.space n) (t : unitInterval) :
    Path.toContinuousMap ((squareConeTransition p q b c H u).map n x) t =
      ReducedMappingCone.inr ((HomotopyPushout.prespectrum p q).point n) (D.point n)
        ((HomotopyPushout.desc p q b c H).map n) (Path.toContinuousMap (u.map n x) t) := rfl

/-- The actual original Waldhausen spectrum map has this concrete coherent quotient-cone
  nullhomotopy. -/
theorem original_Waldhausen_cone {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Waldhausen.Structure C) (V : Waldhausen.Structure D) {F : C ⥤ D}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F) (h₀ : F.obj W.zero = V.zero) :
    Nonempty (Homotopy
      (Waldhausen.IteratedS.originalPrespectrumMap W V hF h₀ ≫
        mappingConeInclusion (Waldhausen.IteratedS.originalPrespectrumMap W V hF h₀))
      (zeroHom (Waldhausen.IteratedS.originalPrespectrum W)
        (mappingCone (Waldhausen.IteratedS.originalPrespectrumMap W V hF h₀)))) :=
  ⟨mappingConeHomotopy _⟩

end QuillenTest.PrespectrumCofibers

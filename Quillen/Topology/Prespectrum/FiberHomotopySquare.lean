/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.FiberSequence
public import Quillen.Topology.Prespectrum.HomotopyLoop
public import Quillen.Topology.Prespectrum.StableEquivalence
public import Mathlib.Algebra.FiveLemma

/-!
Actual fiber maps of specified whole homotopy-commuting prespectrum squares, signed stable boundary
naturality, and stable equivalence under stable side equivalences. The full original square track is
retained; the loop-inclusion square commutes by the explicitly constructed homotopy removing its
constant initial segment.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {A B E F G : LoopPrespectrum.{u}}

@[simp] theorem zeroHom_comp (f : F ⟶ G) : zeroHom E F ≫ f = zeroHom E G := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact f.map_point n

@[simp] theorem comp_zeroHom (f : E ⟶ F) : f ≫ zeroHom F G = zeroHom E G := rfl

variable (f : A ⟶ B) (g : E ⟶ F) (a : A ⟶ E) (b : B ⟶ F)
  (H : Homotopy (a ≫ g) (f ≫ b))

/-- The whole supplied square homotopy is followed by the actual postcomposed
fiber path; neither part is discarded or replaced by an endpoint class. -/
def homotopyFiberSquareNullHomotopy :
    Homotopy ((homotopyFiberProjection f ≫ a) ≫ g) (zeroHom (homotopyFiber f) F) := by
  let N : Homotopy ((homotopyFiberProjection f ≫ f) ≫ b)
      (zeroHom (homotopyFiber f) F) :=
    { level n := (b.map n).comp ((homotopyFiberNullHomotopy f).level n)
      at_zero n z := congrArg (b.map n) z.2.1
      at_one n z := (congrArg (b.map n) z.2.2).trans (b.map_point n)
      at_point n s := b.map_point n
      comm n s z t := congrArg (fun p ↦ p t) (b.comm n (z.1.2 s)) }
  exact (Homotopy.precomp (homotopyFiberProjection f) H).trans N

/-- A genuinely homotopy-commuting square gives an actual fiber spectrum map. -/
def homotopyFiberSquareMap : homotopyFiber f ⟶ homotopyFiber g :=
  homotopyFiberLift g (homotopyFiberProjection f ≫ a)
    (homotopyFiberSquareNullHomotopy f g a b H)

@[simp] theorem homotopyFiberSquareMap_source (n : ℕ)
    (z : (homotopyFiber f).space n) :
    ((homotopyFiberSquareMap f g a b H).map n z).1.1 = a.map n z.1.1 := rfl

@[simp] theorem homotopyFiberSquareMap_path (n : ℕ)
    (z : (homotopyFiber f).space n) (s : unitInterval) :
    ((homotopyFiberSquareMap f g a b H).map n z).1.2 s =
      (homotopyFiberSquareNullHomotopy f g a b H).level n (s,z) := rfl

theorem homotopyFiberSquareMap_projection :
    homotopyFiberSquareMap f g a b H ≫ homotopyFiberProjection g =
      homotopyFiberProjection f ≫ a := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  rfl

/-- The first half of the actual fiber path retains every value of the supplied
square homotopy, with its original source parameter. -/
theorem homotopyFiberSquareMap_first_half (n : ℕ)
    (z : (homotopyFiber f).space n) (t : unitInterval) :
    ((homotopyFiberSquareMap f g a b H).map n z).1.2
      ⟨(t : ℝ)/2, by constructor <;> linarith [t.2.1,t.2.2]⟩ = H.level n (t,z.1.1) := by
  change (((Homotopy.precomp (homotopyFiberProjection f) H).levelHomotopy n).trans
    (((homotopyFiberNullHomotopy f).postcomp b).levelHomotopy n))
      (⟨(t : ℝ)/2, _⟩,z) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change H.level n (⟨2*((t : ℝ)/2), _⟩,z.1.1) = _
    congr 2
    apply Subtype.ext
    dsimp
    ring
  · rename_i h
    exfalso
    apply h
    change (t : ℝ)/2 ≤ 1/2
    linarith [t.2.2]

/-- The loop-inclusion square commutes by the explicit removal of the constant
initial segment, as a whole structure-compatible based homotopy. -/
def homotopyFiberSquareMapLoopHomotopy :
    Homotopy (homotopyFiberLoopInclusion f ≫ homotopyFiberSquareMap f g a b H)
      (parameterLoopingMap b ≫ homotopyFiberLoopInclusion g) where
  level n :=
    { toFun z := (homotopyFiberLoopInclusion g).map n
        (Path.delayReflLeft z.1 ((parameterLoopingMap b).map n z.2))
      continuous_toFun := ((homotopyFiberLoopInclusion g).map n).continuous.comp
        (Path.continuous_delayReflLeft.comp
          (continuous_fst.prodMk (((parameterLoopingMap b).map n).continuous.comp continuous_snd)))
            }
  at_zero n γ := by
    apply Subtype.ext
    apply Prod.ext
    · exact (a.map_point n).symm
    · apply ContinuousMap.ext
      intro s
      change Path.delayReflLeft 0 ((parameterLoopingMap b).map n γ) s =
        (homotopyFiberSquareNullHomotopy f g a b H).level n
          (s,(homotopyFiberLoopInclusion f).map n γ)
      rw [Path.delayReflLeft_zero]
      change ((Path.refl (F.point n)).trans ((parameterLoopingMap b).map n γ)) s =
        (((Homotopy.precomp (homotopyFiberProjection f) H).levelHomotopy n).trans
          (((homotopyFiberNullHomotopy f).postcomp b).levelHomotopy n))
            (s,(homotopyFiberLoopInclusion f).map n γ)
      rw [Path.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
      split
      · exact (H.at_point n _).symm
      · rfl
  at_one n γ := by
    change (homotopyFiberLoopInclusion g).map n
      (Path.delayReflLeft 1 ((parameterLoopingMap b).map n γ)) = _
    rw [Path.delayReflLeft_one]
    rfl
  at_point n θ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      exact b.map_point n
  comm n θ γ t := by
    change Path (B.point n) (B.point n) at γ
    apply Subtype.ext
    apply Prod.ext
    · change E.point (n+1) = E.structureMap n (E.point n) t
      rw [E.map_point]
      rfl
    · apply ContinuousMap.ext
      intro s
      exact congrArg (fun p ↦ p t) (b.comm n (γ _))

/-- The whole supplied square homotopy induces the original stable boundary square. -/
theorem stableFiberConnecting_homotopySquare (d : ℤ) :
    (stableHomotopyFunctor (d+1)).map b ≫ stableFiberConnecting g d =
      stableFiberConnecting f d ≫
        (stableHomotopyFunctor d).map (homotopyFiberSquareMap f g a b H) := by
  have hs := (homotopyFiberSquareMapLoopHomotopy f g a b H).stableHomotopyMap_eq d
  rw [Functor.map_comp, Functor.map_comp] at hs
  unfold stableFiberConnecting
  rw [← Category.assoc, ← parameterStableHomotopyIso_inv_naturality,
    Category.assoc, ← hs, Category.assoc]

/-- A genuinely homotopy-commuting square with stable side equivalences gives
an original stable equivalence on its actual fiber map. -/
theorem homotopyFiberSquareMap_isStableEquivalence
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) :
    IsStableEquivalence (homotopyFiberSquareMap f g a b H) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((stableHomotopyFunctor (d+1)).map f).hom (stableFiberConnecting f d).hom
    ((stableHomotopyFunctor d).map (homotopyFiberProjection f)).hom
    ((stableHomotopyFunctor d).map f).hom
    ((stableHomotopyFunctor (d+1)).map g).hom (stableFiberConnecting g d).hom
    ((stableHomotopyFunctor d).map (homotopyFiberProjection g)).hom
    ((stableHomotopyFunctor d).map g).hom
    ((stableHomotopyFunctor (d+1)).map a).hom
    ((stableHomotopyFunctor (d+1)).map b).hom
    ((stableHomotopyFunctor d).map (homotopyFiberSquareMap f g a b H)).hom
    ((stableHomotopyFunctor d).map a).hom
    ((stableHomotopyFunctor d).map b).hom
    ?_ ?_ ?_ ?_
    (stableFiberConnecting_exact_target f d)
    (stableFiberConnecting_exact_fiber f d)
    (stableHomotopyFiber_exact_source f d)
    (stableFiberConnecting_exact_target g d)
    (stableFiberConnecting_exact_fiber g d)
    (stableHomotopyFiber_exact_source g d)
    ((ConcreteCategory.isIso_iff_bijective _).mp (ha (d+1))).surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp (hb (d+1)))
    ((ConcreteCategory.isIso_iff_bijective _).mp (ha d))
    ((ConcreteCategory.isIso_iff_bijective _).mp (hb d)).injective
  · ext x
    have he := H.stableHomotopyMap_eq (d+1)
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    exact ConcreteCategory.congr_hom (stableFiberConnecting_homotopySquare f g a b H d) x
  · ext x
    have he := congrArg ((stableHomotopyFunctor d).map)
      (homotopyFiberSquareMap_projection f g a b H)
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    have he := H.stableHomotopyMap_eq d
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x

end Quillen.LoopPrespectrum

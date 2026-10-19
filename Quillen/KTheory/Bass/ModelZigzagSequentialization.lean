/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramSuspension
public import Quillen.Topology.Prespectrum.ZigzagSequentializationLinearGrowth
public import Quillen.Topology.Prespectrum.ZigzagSequentializationNaturality

/-!
# Canonical homotopy-pushout sequentialization on actual finite Model Bass stages

The vertices here are the original Bass iterates `BⁿM`, and the backward legs are the
literal suspension units `Bⁿ⁺¹M ⟶ ΩΣBⁿ⁺¹M`. Their actual T1 topology, point HEP, unit
stability and all-point growth discharge every analytic premise of the canonical
pushout/telescope comparison. The monotone offset is `2 * n`; a uniform tower bound is
unnecessary.

Only a whole factorization of each supplied forward arrow through the supplied current
transition and the original unit is retained. In particular, this theorem does not
manufacture or identify Thomason--Trobaugh's tensor/cup forward arrows.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ Model.{w}) (X : C)

/-- The original finite Bass vertices, before any loop-normalized stage comparison. -/
abbrev vertex (n : ℕ) : LoopPrespectrum.{w} :=
  (((strictDiagramIterate Q n).obj (M ⋙ prespectrumFunctor)).obj X)

/-- The literal looped suspension of the next original vertex. -/
abbrev suspendedVertex (n : ℕ) : LoopPrespectrum.{w} :=
  parameterLooping (suspensionCone (vertex Q M X (n + 1)))

/-- The canonical original backward leg, with the forward cone-cylinder orientation. -/
abbrev unit (n : ℕ) : vertex Q M X (n + 1) ⟶ suspendedVertex Q M X n :=
  suspensionLoopUnit (vertex Q M X (n + 1))

variable (a : ∀ n, vertex Q M X n ⟶ suspendedVertex Q M X n)
    (f : ∀ n, vertex Q M X n ⟶ vertex Q M X (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ unit Q M X n))

/-- Original Model topology discharges every excision premise of the actual telescope map. -/
theorem telescopeMap_isStableEquivalence :
    IsStableEquivalence (ZigzagSequentialization.telescopeMap
      (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X) f H) := by
  let : ∀ n k, T1Space ((vertex Q M X n).space k) :=
    fun n k ↦ modelDiagramIterateSpaceT1Space Q n M X k
  let : ∀ n k, T1Space ((suspendedVertex Q M X n).space k) :=
    fun n k ↦ ModelDiagramSuspension.spaceT1Space Q (n + 1) M X k
  apply ZigzagSequentialization.telescopeMap_isStableEquivalence_of_linearGrowth
    (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X) (fun n ↦ 2 * n)
    (by intro i j hij; change 2 * i ≤ 2 * j; omega)
    (fun n k ↦ modelDiagramIterate_point_homotopyExtensionProperty Q n M X k)
    (fun n k ↦ ModelDiagramSuspension.point_homotopyExtensionProperty Q (n + 1) M X k)
    (fun i n x k hk ↦ modelDiagramIterate_homotopyGroup_subsingleton_of_le
      Q i M X (n + 2 * i + 2) (by omega) k (by omega) x)
    (fun i n x k hk ↦ ModelDiagramSuspension.homotopyGroup_subsingleton_at_offset
      Q (i + 1) M X (2 * (i + 1)) (by omega) n k hk x)
    (fun n ↦ ModelDiagramSuspension.unit_stable Q n M X) f H

/-- The localized comparison is the image of the original whole-track telescope map. -/
def telescopeIso :
    toStableLocalization.obj (Telescope.prespectrum (vertex Q M X) f) ≅
      toStableLocalization.obj (Telescope.prespectrum
        (ZigzagSequentialization.stage (vertex Q M X) (suspendedVertex Q M X) a (unit Q M X))
        (ZigzagSequentialization.transition (vertex Q M X) (suspendedVertex Q M X) a
          (unit Q M X))) :=
  stableLocalizationIso _ (telescopeMap_isStableEquivalence Q M X a f H)

end Quillen.KTheory.Bass.ModelZigzagSequentialization

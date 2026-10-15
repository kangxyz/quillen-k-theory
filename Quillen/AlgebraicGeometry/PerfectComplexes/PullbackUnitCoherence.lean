/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackCoherence

/-! The original termwise pullback identity comparisons satisfy the genuine geometric unit laws. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Left unitality retains the actual identity and composition comparisons. -/
lemma pullbackComplexCompIso_left_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackComplexCompIso f (𝟙 Y)).hom ≫
      Functor.whiskerRight (pullbackComplexIdIso Y).hom
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f) ≫
      (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro n
  simpa [pullbackComplexCompIso, pullbackComplexIdIso,
    AlgebraicGeometry.Scheme.Modules.Complex.pullback] using
    congrArg (fun η => η.app (K.X n)) (Scheme.Modules.pseudofunctor_left_unitality f)

/-- Right unitality retains the actual identity and composition comparisons. -/
lemma pullbackComplexCompIso_right_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackComplexCompIso (𝟙 X) f).hom ≫
      Functor.whiskerLeft (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)
        (pullbackComplexIdIso X).hom ≫
      (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro n
  simpa [pullbackComplexCompIso, pullbackComplexIdIso,
    AlgebraicGeometry.Scheme.Modules.Complex.pullback] using
    congrArg (fun η => η.app (K.X n)) (Scheme.Modules.pseudofunctor_right_unitality f)

end Quillen.PerfectComplexes

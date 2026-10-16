/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RelativeHomotopyRealization

/-! The whole original two-time transport, both endpoint maps and full relative union. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Topology
universe u v u' v'
namespace QuillenTest.RelativeHomotopyRealization
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure C) (V : Structure D)
  {f g : C(unitInterval × (originalPrespectrum W).space 1, (originalPrespectrum V).space 1)}
  {f' g' : C(unitInterval × W.Delooping, V.Delooping)}
  (J : f.HomotopyRel g {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (originalPrespectrum W).point 1})
  (hf : ∀ z : unitInterval × W.Delooping,
    V.smallModelDeloopingHomeomorph.symm (f (z.1, W.smallModelDeloopingHomeomorph z.2)) = f' z)
  (hg : ∀ z : unitInterval × W.Delooping,
    V.smallModelDeloopingHomeomorph.symm (g (z.1, W.smallModelDeloopingHomeomorph z.2)) = g' z)

/-- The original comparison and track times vary independently on every source point. -/
theorem original_two_times (a t : unitInterval) (x : W.Delooping) :
    originalPrespectrumLevelOneRelHomotopy W V J hf hg (a, (t, x)) =
      V.smallModelDeloopingHomeomorph.symm
        (J (a, (t, W.smallModelDeloopingHomeomorph x))) :=
  originalPrespectrumLevelOneRelHomotopy_apply W V J hf hg a t x

/-- The two full endpoint maps are retained before taking any homotopy classes. -/
theorem original_endpoints (t : unitInterval) (x : W.Delooping) :
    originalPrespectrumLevelOneRelHomotopy W V J hf hg (0, (t, x)) = f' (t, x) ∧
      originalPrespectrumLevelOneRelHomotopy W V J hf hg (1, (t, x)) = g' (t, x) :=
  ⟨(originalPrespectrumLevelOneRelHomotopy W V J hf hg).apply_zero (t, x),
    (originalPrespectrumLevelOneRelHomotopy W V J hf hg).apply_one (t, x)⟩

/-- The entire original relative union, including the whole based line, is fixed at every time. -/
theorem original_relative_union (a t : unitInterval) (x : W.Delooping)
    (h : t = 0 ∨ t = 1 ∨ x = W.kBasepoint) :
    originalPrespectrumLevelOneRelHomotopy W V J hf hg (a, (t, x)) = f' (t, x) :=
  (originalPrespectrumLevelOneRelHomotopy W V J hf hg).eq_fst a h

end QuillenTest.RelativeHomotopyRealization

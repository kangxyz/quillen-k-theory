/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.Basic

/-! # Actual perfect-complex gluing on a binary open cover -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens)
  {K : Complex (pullback U.ι V.ι)} {A : Complex U.toScheme} {B : Complex V.toScheme}
  (α : K ⟶ (restrict (pullback.fst U.ι V.ι)).obj A)
  (β : K ⟶ (restrict (pullback.snd U.ι V.ι)).obj B)

/-- The actual cone complex from the original two opens and original overlap maps. -/
def binary : Complex X :=
  glued (pullback.fst U.ι V.ι) (pullback.snd U.ι V.ι) U.ι V.ι pullback.condition α β

/-- The actual first original local-to-global restriction map. -/
def binaryFirst : A ⟶ (restrict U.ι).obj (binary U V α β) :=
  first (pullback.fst U.ι V.ι) (pullback.snd U.ι V.ι) U.ι V.ι pullback.condition α β

/-- The actual second original local-to-global restriction map. -/
def binarySecond : B ⟶ (restrict V.ι).obj (binary U V α β) :=
  second (pullback.fst U.ι V.ι) (pullback.snd U.ι V.ι) U.ι V.ι pullback.condition α β

/-- The first local map is quasi-isomorphic from the original weak overlap arrow. -/
theorem binaryFirst_quasiIso [QuasiIso β] : QuasiIso (binaryFirst U V α β) :=
  first_quasiIso _ _ _ _ _ _ _ (by
    intro x hx
    rw [IsOpenImmersion.range_pullbackFst]
    exact hx)

/-- The symmetric local map is quasi-isomorphic without additional geometry. -/
theorem binarySecond_quasiIso [QuasiIso α] : QuasiIso (binarySecond U V α β) :=
  second_quasiIso _ _ _ _ _ _ _ (by
    intro x hx
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hx)

/-- Actual local models prove perfection of the global cone. Its extended summands
are not required to be perfect or quasicoherent. -/
theorem locallyPerfect_binary (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] : locallyPerfect X (binary U V α β) := by
  have := binaryFirst_quasiIso U V α β
  have := binarySecond_quasiIso U V α β
  exact locallyPerfect_of_binaryOpenCover U V hUV
    ((locallyPerfect_iff_of_quasiIso (binaryFirst U V α β)).mp hA)
    ((locallyPerfect_iff_of_quasiIso (binarySecond U V α β)).mp hB)

/-- Genuine two-open gluing with explicit quasi-isomorphic maps to both original restrictions. -/
theorem exists_perfect_glue (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] :
    ∃ P : Complex X, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P),
        QuasiIso u ∧ QuasiIso v :=
  ⟨binary U V α β, locallyPerfect_binary U V α β hUV hA hB,
    binaryFirst U V α β, binarySecond U V α β,
    binaryFirst_quasiIso U V α β, binarySecond_quasiIso U V α β⟩

end Quillen.PerfectComplexes.OpenHomotopyGluing

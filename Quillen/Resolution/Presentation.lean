/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Resolution.Closure

/-!
# One-step presentations with controlled syzygy

These are actual kernel–cokernel pairs. They are used to prove closure of
resolution-length strata without assuming that the resolving objects are
projective or that comparison morphisms lift against arbitrary epimorphisms.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A conflation resolving `X` by a `P`-object and a `Q`-syzygy. -/
structure Presentation (P Q : C → Prop) (X : C) where
  /-- The kernel object of the presentation, required to satisfy `Q`. -/
  syzygy : C
  /-- The object satisfying `P` that admits the deflation onto `X`. -/
  middle : C
  /-- The inflation of the syzygy into the middle object. -/
  f : syzygy ⟶ middle
  /-- The deflation from the middle object onto the object being presented. -/
  g : middle ⟶ X
  zero : f ≫ g = 0
  conflation : E.conflation (ShortComplex.mk f g zero)
  middle_mem : P middle
  syzygy_mem : Q syzygy

/-- One additional admissible resolution step. -/
def ResolutionStep (P Q : C → Prop) : ObjectProperty C :=
  fun X => Nonempty (E.Presentation P Q X)

namespace Presentation
variable {E} {P Q : C → Prop} {X : C}

/-- The actual short complex underlying the presentation. -/
abbrev complex (T : E.Presentation P Q X) : ShortComplex C := ShortComplex.mk T.f T.g T.zero

lemma deflation (T : E.Presentation P Q X) : E.deflation T.g :=
  E.deflation_of_conflation T.conflation

lemma inflation (T : E.Presentation P Q X) : E.inflation T.f :=
  E.inflation_of_conflation T.conflation

/-- The identity presentation uses a genuine zero kernel. -/
def ofMem (hX : P X) (h₀ : Q (0 : C)) : E.Presentation P Q X where
  syzygy := 0
  middle := X
  f := 0
  g := 𝟙 X
  zero := by simp
  conflation := E.conflation_of_isKernel _ (kernel.isLimitConeZeroCone (𝟙 X)) (E.deflation_id X)
  middle_mem := hX
  syzygy_mem := h₀

/-- A resolving middle term and an actual finite syzygy resolution give an
actual successor resolution. -/
def finiteResolution (T : E.Presentation P Q X) (R : E.FiniteResolution P T.syzygy) :
    E.FiniteResolution P X := .step T.complex T.conflation T.middle_mem R

@[simp] lemma length_finiteResolution (T : E.Presentation P Q X)
    (R : E.FiniteResolution P T.syzygy) : (T.finiteResolution R).length = R.length + 1 := rfl

end Presentation

variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Every bounded finite resolution supplies a one-step presentation whose
syzygy lies in the previous resolution stratum. -/
lemma resolutionLength_succ_iff (n : ℕ) (X : C) :
    E.ResolutionLength P (n + 1) X ↔ E.ResolutionStep P (E.ResolutionLength P n) X := by
  constructor
  · rintro ⟨R, hR⟩
    cases R with
    | of_mem hX =>
      exact ⟨Presentation.ofMem hX ⟨.of_mem P.prop_zero, Nat.zero_le n⟩⟩
    | step S hS hP R =>
      exact ⟨⟨S.X₁, S.X₂, S.f, S.g, S.zero, hS, hP,
        ⟨R, Nat.le_of_succ_le_succ hR⟩⟩⟩
  · rintro ⟨T⟩
    obtain ⟨R, hR⟩ := T.syzygy_mem
    exact ⟨T.finiteResolution R, Nat.succ_le_succ hR⟩

variable (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
  [E.IsExtensionClosed Q] [E.IsKernelClosed Q]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Presentation independence: any admissible epimorphism from a `Q`-object
onto an object presented by a `P`-object with `Q`-kernel has `Q`-kernel, provided
`P ≤ Q`. The pullback proof needs no projective lifting property. -/
lemma kernel_mem_of_resolutionStep (hPQ : P ≤ Q) {S : ShortComplex C}
    (hS : E.conflation S) (hB : Q S.X₂) (hC : E.ResolutionStep P Q S.X₃) : Q S.X₁ := by
  obtain ⟨T⟩ := hC
  let : HasPullback T.g S.g := E.deflation.hasPullback S.g T.deflation
  let : HasPullback S.g T.g := hasPullback_symmetry _ _
  have hPB : Q (pullback T.g S.g) :=
    E.prop_pullback Q T.conflation T.syzygy_mem hB S.g
  have hPB' : Q (pullback S.g T.g) := Q.prop_of_iso (pullbackSymmetry _ _) hPB
  exact IsKernelClosed.prop_kernel (E := E) (P := Q)
    (S := pullbackConflation (S := S) T.middle T.g)
    (E.pullbackConflation_mem hS T.g) hPB' (hPQ _ T.middle_mem)

end Quillen.ExactStructure

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.OpenGluing.Descent

/-! # Actual perfect-complex gluing over an original global target -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens)
  {K : CochainComplex (pullback U.ι V.ι).Modules ℤ} {A : CochainComplex U.toScheme.Modules ℤ}
    {B : CochainComplex V.toScheme.Modules ℤ}
  {L : CochainComplex X.Modules ℤ}
  (α : K ⟶ (restrict (pullback.fst U.ι V.ι)).obj A)
  (β : K ⟶ (restrict (pullback.snd U.ι V.ι)).obj B)
  (p : A ⟶ (restrict U.ι).obj L) (q : B ⟶ (restrict V.ι).obj L)
  (H : Homotopy (α ≫ (restrict (pullback.fst U.ι V.ι)).map p)
    (β ≫ (restrict (pullback.snd U.ι V.ι)).map q ≫
      (openSquareRestrictIso (pullback.snd U.ι V.ι) (pullback.fst U.ι V.ι)
        V.ι U.ι pullback.condition.symm).hom.app L))

/-- The original global chain map from the explicit cone glued on the two opens. -/
def binaryDesc : binary U V α β ⟶ L :=
  desc (pullback.fst U.ι V.ι) (pullback.snd U.ι V.ι) U.ι V.ι pullback.condition α β p q H

/-- The first original local target triangle commutes as an exact chain-map equation. -/
@[reassoc (attr := simp)]
theorem binaryFirst_desc : binaryFirst U V α β ≫ (restrict U.ι).map (binaryDesc U V α β p q H) = p
  :=
  first_desc _ _ _ _ _ _ _ _ _ _

/-- The second original local target triangle also commutes strictly. -/
@[reassoc (attr := simp)]
theorem binarySecond_desc : binarySecond U V α β ≫ (restrict V.ι).map (binaryDesc U V α β p q H) = q
  :=
  second_desc _ _ _ _ _ _ _ _ _ _

/-- Weak local target maps yield a genuine global quasi-isomorphism of original complexes. -/
theorem quasiIso_binaryDesc (hUV : U ⊔ V = ⊤)
    [QuasiIso α] [QuasiIso β] [QuasiIso p] [QuasiIso q] :
    QuasiIso (binaryDesc U V α β p q H) := by
  apply quasiIso_of_openCover (binaryDesc U V α β p q H) (fun t : Bool => if t then U else V)
  · intro x
    have hx : x ∈ U ⊔ V := by rw [hUV]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  · intro t
    cases t with
    | false =>
      exact desc_restrict_second_quasiIso _ _ _ _ _ _ _ _ _ _ (by
        intro x hx
        rw [IsOpenImmersion.range_pullbackSnd]
        exact hx)
    | true =>
      exact desc_restrict_first_quasiIso _ _ _ _ _ _ _ _ _ _ (by
        intro x hx
        rw [IsOpenImmersion.range_pullbackFst]
        exact hx)

include H in
/-- An arbitrary pair of target maps and its actual overlap homotopy glue to
an original perfect source with strict triangles; no target-map weakness is required. -/
theorem exists_perfect_glue_with_target_map (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧
        u ≫ (restrict U.ι).map d = p ∧ v ≫ (restrict V.ι).map d = q :=
  ⟨binary U V α β, locallyPerfect_binary U V α β hUV hA hB,
    binaryFirst U V α β, binarySecond U V α β, binaryDesc U V α β p q H,
    binaryFirst_quasiIso U V α β, binarySecond_quasiIso U V α β,
    binaryFirst_desc U V α β p q H, binarySecond_desc U V α β p q H⟩

include H in
/-- Actual perfect gluing over a global target with original strict local triangles.
The only compatibility input is the displayed chain homotopy on the actual overlap. -/
theorem exists_perfect_glue_over_target (hUV : U ⊔ V = ⊤)
    (hA : locallyPerfect U.toScheme A) (hB : locallyPerfect V.toScheme B)
    [QuasiIso α] [QuasiIso β] [QuasiIso p] [QuasiIso q] :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      ∃ (u : A ⟶ (restrict U.ι).obj P) (v : B ⟶ (restrict V.ι).obj P) (d : P ⟶ L),
        QuasiIso u ∧ QuasiIso v ∧ QuasiIso d ∧
        u ≫ (restrict U.ι).map d = p ∧ v ≫ (restrict V.ι).map d = q :=
  ⟨binary U V α β, locallyPerfect_binary U V α β hUV hA hB,
    binaryFirst U V α β, binarySecond U V α β, binaryDesc U V α β p q H,
    binaryFirst_quasiIso U V α β, binarySecond_quasiIso U V α β,
    quasiIso_binaryDesc U V α β p q H hUV,
    binaryFirst_desc U V α β p q H, binarySecond_desc U V α β p q H⟩

end Quillen.PerfectComplexes.OpenHomotopyGluing

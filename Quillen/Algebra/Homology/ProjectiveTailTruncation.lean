/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.KProjectiveComparison
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Genuine projective lower-tail truncation

The actual tail homotopy splits the original opcycles quotient off the next
original term. This proves projectivity of that quotient, while its original
epimorphism proves finite generation. Good lower truncation of a bounded-above
finite-projective complex with an actual lower-bounded homotopy model is
therefore bounded finite-projective, and the original truncation projection is
a quasi-isomorphism. Exact upper/lower term bounds, including empty intervals,
are retained. No global replacement is assumed or fabricated.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A genuine tail homotopy splits the original cokernel of the preceding
complex differential off the next original term. -/
def opcyclesRetractOfHomotopyAt (P : CochainComplex C ℤ) (n : ℤ)
    (φ : P ⟶ P) (H : Homotopy (𝟙 P) φ) (hφ : φ.f n = 0) :
    Retract (P.opcycles n) (P.X (n + 1)) where
  i := P.fromOpcycles n (n + 1)
  r := H.hom (n + 1) n ≫ P.pOpcycles n
  retract := by
    apply (cancel_epi (P.pOpcycles n)).mp
    have hc := congrArg (fun t => t ≫ P.pOpcycles n) (H.comm n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n-1) n by dsimp; omega)] at hc
    simpa only [id_f, hφ, Preadditive.add_comp, zero_comp, Category.id_comp,
      Category.comp_id, Category.assoc, d_pOpcycles, comp_zero, add_zero,
      p_fromOpcycles_assoc] using hc.symm

/-- A bounded-below homotopy model gives the actual tail-cokernel retract,
without a projectivity or finiteness hypothesis on that model. -/
def opcyclesRetractOfHomotopyModel {P Q : CochainComplex C ℤ}
    (e : HomotopyEquiv P Q) (n : ℤ) (hQ : IsZero (Q.X n)) :
    Retract (P.opcycles n) (P.X (n + 1)) :=
  opcyclesRetractOfHomotopyAt P n (e.hom ≫ e.inv) e.homotopyHomInvId.symm (by
    change e.hom.f n ≫ e.inv.f n = 0
    rw [hQ.eq_of_src (e.inv.f n) 0, comp_zero])

/-- The original tail cokernel is projective because its constructed retract
lands in the actual next projective term. -/
theorem projective_opcycles_of_homotopy_model {P Q : CochainComplex C ℤ}
    (e : HomotopyEquiv P Q) (n : ℤ) (hQ : IsZero (Q.X n)) [Projective (P.X (n + 1))] :
    Projective (P.opcycles n) :=
  (opcyclesRetractOfHomotopyModel e n hQ).projective

/-- Every term of the actual good lower truncation is projective when its
boundary cokernel is split by the genuine tail homotopy. -/
theorem projective_truncGE_of_homotopy_model {P Q : CochainComplex C ℤ}
    (e : HomotopyEquiv P Q) (n : ℤ) (hQ : IsZero (Q.X n))
    (hP : ∀ i, Projective (P.X i)) (i : ℤ) : Projective ((P.truncGE n).X i) := by
  rcases lt_trichotomy i n with hi | hi | hi
  · exact ((P.truncGE n).isZero_of_isStrictlyGE n i hi).projective
  · subst i
    let := hP (n + 1)
    exact Projective.of_iso (P.truncGEXIsoOpcycles n).symm
      (projective_opcycles_of_homotopy_model e n hQ)
  · exact Projective.of_iso (P.truncGEXIso n i hi).symm (hP i)

/-- The original good-truncation projection is a quasi-isomorphism when the
actual homotopy model vanishes below the cutoff. -/
theorem quasiIso_πTruncGE_of_homotopy_model {P Q : CochainComplex C ℤ}
    (e : HomotopyEquiv P Q) (n : ℤ) (hQ : ∀ i, i < n → IsZero (Q.X i)) :
    QuasiIso (P.πTruncGE n) := by
  have : Q.IsStrictlyGE n := (CochainComplex.isStrictlyGE_iff Q n).mpr hQ
  have : P.IsGE n :=
    (HomologicalComplex.isSupported_iff_of_quasiIso e.hom (ComplexShape.embeddingUpIntGE n)).mpr
      inferInstance
  infer_instance

section Modules
variable {R : Type u} [CommRing R]

/-- The original quotient map proves finite generation of the actual boundary
cokernel from the original finite term. -/
theorem finite_opcycles (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    [Module.Finite R (P.X n)] : Module.Finite R (P.opcycles n) :=
  Module.Finite.of_surjective (P.pOpcycles n).hom
    ((ModuleCat.epi_iff_surjective (P.pOpcycles n)).mp inferInstance)

/-- Good truncation preserves finite generation of every original term. -/
theorem finite_truncGE (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hP : ∀ i, Module.Finite R (P.X i)) (i : ℤ) :
    Module.Finite R ((P.truncGE n).X i) := by
  rcases lt_trichotomy i n with hi | hi | hi
  · let := ModuleCat.isZero_iff_subsingleton.mp
      ((P.truncGE n).isZero_of_isStrictlyGE n i hi)
    infer_instance
  · subst i
    let := hP n
    let := finite_opcycles P n
    exact Module.Finite.equiv (P.truncGEXIsoOpcycles n).toLinearEquiv.symm
  · let := hP i
    exact Module.Finite.equiv (P.truncGEXIso n i hi).toLinearEquiv.symm

/-- Actual good lower truncation of the original finite-projective complex
is bounded finite-projective and the original projection is a quasi-isomorphism.
A model supported from `n+1` provides the boundary retraction at `n`; the exact
original upper bound is retained, even if the resulting interval is empty. -/
theorem bounded_finiteProjective_truncGE_of_homotopy_model
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : HomotopyEquiv P Q)
    (n b : ℤ) (hbound : ∀ i, b < i → IsZero (P.X i))
    (hfinite : ∀ i, Module.Finite R (P.X i))
    (hprojective : ∀ i, Module.Projective R (P.X i))
    (hQ : ∀ i, i < n + 1 → IsZero (Q.X i)) :
    (∀ i, i < n ∨ b < i → IsZero ((P.truncGE n).X i)) ∧
      (∀ i, Module.Finite R ((P.truncGE n).X i) ∧
        Module.Projective R ((P.truncGE n).X i)) ∧ QuasiIso (P.πTruncGE n) := by
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).mpr hbound
  have hproj (i : ℤ) : Projective (P.X i) := by
    let := hprojective i
    infer_instance
  refine ⟨fun i hi => ?_, fun i => ?_,
    quasiIso_πTruncGE_of_homotopy_model e n (fun i hi => hQ i (by omega))⟩
  · rcases hi with hi | hi
    · exact (P.truncGE n).isZero_of_isStrictlyGE n i hi
    · exact (P.truncGE n).isZero_of_isStrictlyLE b i hi
  · have := projective_truncGE_of_homotopy_model e n (hQ n (by omega)) hproj i
    exact ⟨finite_truncGE P n hfinite i, inferInstance⟩

end Modules
end Quillen.CochainComplex

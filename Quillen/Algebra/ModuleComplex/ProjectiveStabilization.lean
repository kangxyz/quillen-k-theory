/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Finite-free stabilization of bounded projective complexes

Finite projective modules have actual finite projective complements in finite
free modules, chosen to vanish on zero terms. Adding the contractible identity
cone of their zero-differential complex to `K ⊞ K⟦1⟧` gives an actual bounded
finite-free complex and an explicit chain-homotopy equivalence. The resulting
bounds are `[a - 1, b]`; the original complex alone is not claimed to be stably
free or to extend across a localization.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
namespace Quillen.ModuleComplex
variable {R : Type u} [CommRing R]

/-- Finite projective modules have genuine finite projective complements in
finite free modules; zero modules admit zero complements. -/
theorem exists_finiteProjective_complement (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] :
    ∃ Q : ModuleCat.{u} R, Module.Finite R Q ∧ Module.Projective R Q ∧
      Module.Free R (M × Q) ∧ (IsZero M → IsZero Q) := by
  classical
  by_cases hM : IsZero M
  · let : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
    exact ⟨M, inferInstance, inferInstance, inferInstance, fun _ => hM⟩
  · obtain ⟨n, f, g, hf, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
    let Q := ModuleCat.of R f.ker
    let e : (Q × M) ≃ₗ[R] (Fin n → R) :=
      lequivProdOfRightSplitExact (j := f.ker.subtype) (g := f) (f := g)
        (Submodule.subtype_injective _) (Submodule.range_subtype _) hfg
    let q : (Fin n → R) →ₗ[R] Q := (LinearMap.fst R Q M).comp e.symm.toLinearMap
    have hq : Function.Surjective q := by
      intro x
      exact ⟨e (x, 0), by simp [q]⟩
    let : Module.Finite R Q := Module.Finite.of_surjective q hq
    let i : Q →ₗ[R] (Fin n → R) := e.toLinearMap.comp (LinearMap.inl R Q M)
    let : Module.Projective R Q := Module.Projective.of_split i q (by ext; simp [i, q])
    let : Module.Free R (M × Q) :=
      Module.Free.of_equiv (e.symm.trans (LinearEquiv.prodComm R Q M))
    exact ⟨Q, inferInstance, inferInstance, inferInstance, fun h => (hM h).elim⟩

/-- Removing an explicitly contractible summand is a genuine homotopy equivalence. -/
def biprodContractibleHomotopyEquiv
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    (K L : CochainComplex C ℤ) (hL : Homotopy (𝟙 L) 0) :
    HomotopyEquiv (K ⊞ L) K where
  hom := biprod.fst
  inv := biprod.inl
  homotopyHomInvId := by
    have h := (Homotopy.refl (biprod.fst ≫ biprod.inl : K ⊞ L ⟶ K ⊞ L)).add
      ((hL.compLeft (biprod.snd : K ⊞ L ⟶ L)).compRight biprod.inr)
    simpa using h.symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- The actual zero-differential complex on a family of modules. -/
def zeroDifferentialComplex (Q : ℤ → ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of Q (fun _ => 0) (fun _ => by simp)

/-- The actual stabilized complex, with a genuinely contractible added cone. -/
def projectiveStabilization (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (Q : ℤ → ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (K ⊞ K⟦(1 : ℤ)⟧) ⊞ CochainComplex.mappingCone (𝟙 (zeroDifferentialComplex Q))

/-- Stabilization retains the original complex plus its actual shift up to
an explicit chain-homotopy equivalence. -/
def projectiveStabilizationHomotopyEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (Q : ℤ → ModuleCat.{u} R) :
    HomotopyEquiv (projectiveStabilization K Q) (K ⊞ K⟦(1 : ℤ)⟧) :=
  biprodContractibleHomotopyEquiv _ _
    (CochainComplex.mappingCone.homotopyToZeroOfId (zeroDifferentialComplex Q))

/-- The terms regroup into the two original free completion pairs. -/
def projectiveStabilizationTermEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (Q : ℤ → ModuleCat.{u} R) (i : ℤ) :
    (projectiveStabilization K Q).X i ≃ₗ[R]
      (K.X i × Q i) × (K.X (i + 1) × Q (i + 1)) := by
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i
  let e₁ : (K ⊞ K⟦(1 : ℤ)⟧).X i ≅ ModuleCat.of R (K.X i × K.X (i + 1)) :=
    E.mapBiprod _ _ ≪≫ ModuleCat.biprodIsoProd _ _
  let e₂ : (CochainComplex.mappingCone (𝟙 (zeroDifferentialComplex Q))).X i ≅
      ModuleCat.of R (Q i × Q (i + 1)) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (zeroDifferentialComplex Q)) i (i + 1) rfl ≪≫
      biprod.braiding _ _ ≪≫ ModuleCat.biprodIsoProd _ _
  let e : (projectiveStabilization K Q).X i ≅
      ModuleCat.of R ((K.X i × K.X (i + 1)) × (Q i × Q (i + 1))) :=
    E.mapBiprod _ _ ≪≫ biprod.mapIso e₁ e₂ ≪≫ ModuleCat.biprodIsoProd _ _
  exact e.toLinearEquiv.trans (LinearEquiv.prodProdProdComm R _ _ _ _)

/-- Genuine finite-projective bounded complexes become finite free after adding
one shifted copy and an explicit contractible complex. -/
theorem exists_bounded_finiteFree_stabilization
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hbound : ∀ i, i < a ∨ b < i → IsZero (K.X i))
    (hfinite : ∀ i, Module.Finite R (K.X i))
    (hprojective : ∀ i, Module.Projective R (K.X i)) :
    ∃ T : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, i < a - 1 ∨ b < i → IsZero (T.X i)) ∧
      (∀ i, Module.Free R (T.X i) ∧ Module.Finite R (T.X i)) ∧
      Nonempty (HomotopyEquiv T (K ⊞ K⟦(1 : ℤ)⟧)) := by
  classical
  have hm (i : ℤ) : ∃ Q : ModuleCat.{u} R, Module.Finite R Q ∧ Module.Projective R Q ∧
      Module.Free R (K.X i × Q) ∧ (IsZero (K.X i) → IsZero Q) := by
    let := hfinite i
    let := hprojective i
    exact exists_finiteProjective_complement (K.X i)
  choose Q hQfinite hQprojective hfree hzero using hm
  refine ⟨projectiveStabilization K Q, ?_, ?_, ⟨projectiveStabilizationHomotopyEquiv K Q⟩⟩
  · intro i hi
    have h₁ : IsZero (K.X i) := hbound i (by omega)
    have h₂ : IsZero (K.X (i + 1)) := hbound (i + 1) (by omega)
    let := ModuleCat.isZero_iff_subsingleton.mp h₁
    let := ModuleCat.isZero_iff_subsingleton.mp h₂
    let := ModuleCat.isZero_iff_subsingleton.mp (hzero i h₁)
    let := ModuleCat.isZero_iff_subsingleton.mp (hzero (i + 1) h₂)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (projectiveStabilizationTermEquiv K Q i).injective.subsingleton
  · intro i
    let := hfree i
    let := hfree (i + 1)
    let := hfinite i
    let := hfinite (i + 1)
    let := hQfinite i
    let := hQfinite (i + 1)
    exact ⟨Module.Free.of_equiv (projectiveStabilizationTermEquiv K Q i).symm,
      Module.Finite.equiv (projectiveStabilizationTermEquiv K Q i).symm⟩

end Quillen.ModuleComplex

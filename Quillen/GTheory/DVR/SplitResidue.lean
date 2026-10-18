/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.QuillenComparison.ExactAdditivity
public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.Algebra.Category.FGModuleCat.RestrictScalars
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Quillen.GTheory.Dedekind.Localization
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Original generic localization is injective for a split-residue DVR

Let `R` be an actual DVR and `F` a field, with ring maps `σ : F →+* R` and
`ρ : R →+* F` satisfying `ρ.comp σ = id` and `ker ρ = maximalIdeal R`.
The literal tensor functor `T(M)=R ⊗[F] M` and original finite restriction
`H=ρ_*` form the genuine natural sequence
`0 → T → T → H → 0`, with multiplication by an irreducible uniformizer and
reduction `r ⊗ m ↦ ρ(r)m` as its two maps.

Canonical small-model whiskering and `KMap_conflation_additivity` prove
`H.smallKMap n = 1` for every `n`. The induced coefficient section of the
original quotient-residue map, native residue dévissage, and actual finite-module
localization exactness then prove `localizationKMap_injective`.
`localizationKMap_two_injective` supplies the degree-two current consumer.
A section of the original quotient-residue map is an alternative sufficient input.

The coefficient section and residue-kernel equation are explicit hypotheses.
This module does not construct them for a smooth-curve origin, identify Milnor
and Quillen symbols, prove unit generation, or provide product or same-μ marking.
No residue-field K-group vanishing is used.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped TensorProduct nonZeroDivisors

universe u v w

namespace Quillen.SplitResidueDvr

attribute [local instance] Abelian.hasFiniteBiproducts

section SmallAdditivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

private def smallNatTrans {F G : ExactFunctor EC ED} (a : F.toFunctor ⟶ G.toFunctor) :
    F.smallModel.toFunctor ⟶ G.smallModel.toFunctor :=
  Functor.whiskerRight (Functor.whiskerLeft (equivSmallModel.{w} C).inverse a)
    (equivSmallModel.{w} D).functor

private theorem smallKMap_eq_one_of_self_conflation (T H : ExactFunctor EC ED)
    (a : T.toFunctor ⟶ T.toFunctor) (b : T.toFunctor ⟶ H.toFunctor)
    (hab : a ≫ b = 0)
    (hc : ∀ X, ED.conflation (ShortComplex.mk (a.app X) (b.app X)
      (NatTrans.congr_app hab X))) (n : ℕ) : H.smallKMap.{w} n = 1 := by
  let as := smallNatTrans a
  let bs := smallNatTrans b
  have hs : as ≫ bs = 0 := by
    ext X
    change (equivSmallModel.{w} D).functor.map (a.app _) ≫
      (equivSmallModel.{w} D).functor.map (b.app _) = 0
    have habX : a.app ((equivSmallModel.{w} C).inverse.obj X) ≫
        b.app ((equivSmallModel.{w} C).inverse.obj X) = 0 :=
      NatTrans.congr_app hab _
    rw [← Functor.map_comp, habX, Functor.map_zero]
  have hcs (X : SmallModel.{w} C) : ED.smallModel.conflation
      (ShortComplex.mk (as.app X) (bs.app X) (NatTrans.congr_app hs X)) :=
    ED.originalToSmallModel.map_conflation _ (hc ((equivSmallModel.{w} C).inverse.obj X))
  ext x
  have h := ExactFunctor.KMap_conflation_additivity T.smallModel T.smallModel H.smallModel
    as bs hs hcs n x
  change H.smallModel.KMap n x = 1
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

end SmallAdditivity

section Functors

variable {F R : Type u} [Field F] [CommRing R] [IsNoetherianRing R]

/-- Literal extension of scalars on actual finite modules. -/
def tensorFunctor (σ : F →+* R) : FGModuleCat.{u} F ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift (ModuleCat.isFG R)
    (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F) ⋙ ModuleCat.extendScalars σ) (fun M => by
      let := σ.toAlgebra
      let : Module.Finite F M := M.property
      change Module.Finite R (R ⊗[F] M)
      infer_instance)

instance tensorFunctor_additive (σ : F →+* R) : (tensorFunctor σ).Additive := by
  dsimp [tensorFunctor]
  infer_instance

instance tensorFunctor_preservesFiniteLimits (σ : F →+* R) :
    PreservesFiniteLimits (tensorFunctor σ) := by
  have hflat : σ.Flat := by
    let := σ.toAlgebra
    change Module.Flat F R
    infer_instance
  let := ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  have : PreservesFiniteLimits
      (tensorFunctor σ ⋙ forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F) ⋙ ModuleCat.extendScalars σ)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (tensorFunctor σ)
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))

instance tensorFunctor_preservesFiniteColimits (σ : F →+* R) :
    PreservesFiniteColimits (tensorFunctor σ) := by
  have hflat : σ.Flat := by
    let := σ.toAlgebra
    change Module.Flat F R
    infer_instance
  let := ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hflat
  have : PreservesFiniteColimits
      (tensorFunctor σ ⋙ forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F) ⋙ ModuleCat.extendScalars σ)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (tensorFunctor σ)
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))

/-- Scalar extension from a field preserves the genuine finite-module exact structures. -/
def tensorExact (σ : F →+* R) : ExactFunctor
    (ModuleCat.finiteModuleExactStructure.{u,u} F)
    (ModuleCat.finiteModuleExactStructure.{u,u} R) where
  toFunctor := tensorFunctor σ
  map_conflation _ h := h.map_of_exact _

omit [IsNoetherianRing R] in
/-- A coefficient-field retraction is surjective. -/
lemma split_surjective (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) : Function.Surjective ρ := by
  intro a
  exact ⟨σ a, DFunLike.congr_fun hσ a⟩

/-- The original exact finite restriction of scalars along the surjective residue map. -/
def restrictionExact (ρ : R →+* F) (hρ : Function.Surjective ρ) : ExactFunctor
    (ModuleCat.finiteModuleExactStructure.{u,u} F)
    (ModuleCat.finiteModuleExactStructure.{u,u} R) :=
  ModuleCat.FiniteRestrictionScalars.moduleRestrictionExact (CommRingCat.ofHom ρ)
    (RingHom.Finite.of_surjective _ hρ)

/-- The residue homomorphism as a linear map over its coefficient field. -/
def residueLinear (σ : F →+* R) (ρ : R →+* F) (hσ : ρ.comp σ = RingHom.id F) :
    letI := σ.toAlgebra
    R →ₗ[F] F := by
  letI := σ.toAlgebra
  exact
    { toFun := ρ
      map_add' := ρ.map_add
      map_smul' := by
        intro a r
        change ρ (σ a * r) = a * ρ r
        have hs : ρ (σ a) = a := DFunLike.congr_fun hσ a
        rw [map_mul, hs] }

/-- The actual reduction map on each tensor module, sending `r ⊗ m` to `ρ(r)m`. -/
def reductionHom (σ : F →+* R) (ρ : R →+* F) (hσ : ρ.comp σ = RingHom.id F)
    (hρ : Function.Surjective ρ) (M : FGModuleCat.{u} F) :
    (tensorFunctor σ).obj M ⟶ (restrictionExact ρ hρ).toFunctor.obj M := by
  letI := σ.toAlgebra
  let ψ : R ⊗[F] M →ₗ[F] M :=
    (TensorProduct.lid F M).toLinearMap.comp ((residueLinear σ ρ hσ).rTensor M)
  exact FGModuleCat.ofHom (V := (tensorFunctor σ).obj M)
    (W := (restrictionExact ρ hρ).toFunctor.obj M)
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r x
        change ψ (r • x) = ρ r • ψ x
        induction x using TensorProduct.inductionOn with
        | tmul s m =>
          change R at s
          change ρ (r * s) • m = ρ r • (ρ s • m)
          rw [map_mul, mul_smul]
        | add x y hx hy =>
          change ψ (r • (x + y)) = ρ r • ψ (x + y)
          simp only [smul_add, map_add, hx, hy] }

/-- Multiplication by the actual scalar on the literal tensor functor. -/
def multiplicationNat (σ : F →+* R) (π : R) : tensorFunctor σ ⟶ tensorFunctor σ where
  app M := FGModuleCat.ofHom (V := (tensorFunctor σ).obj M)
    (W := (tensorFunctor σ).obj M) (LinearMap.lsmul R ((tensorFunctor σ).obj M) π)
  naturality {M N} f := by
    apply FGModuleCat.hom_ext
    ext x
    exact (((tensorFunctor σ).map f).hom.hom.map_smul π x).symm

/-- The actual reduction maps form a natural transformation into original restriction. -/
def reductionNat (σ : F →+* R) (ρ : R →+* F) (hσ : ρ.comp σ = RingHom.id F)
    (hρ : Function.Surjective ρ) :
    tensorFunctor σ ⟶ (restrictionExact ρ hρ).toFunctor where
  app := reductionHom σ ρ hσ hρ
  naturality {M N} f := by
    let := σ.toAlgebra
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (reductionHom σ ρ hσ hρ N).hom.hom (((tensorFunctor σ).map f).hom.hom x) =
      ((restrictionExact ρ hρ).toFunctor.map f).hom.hom
        ((reductionHom σ ρ hσ hρ M).hom.hom x)
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
      change ρ r • f.hom.hom m = f.hom.hom (ρ r • m)
      exact (f.hom.hom.map_smul _ _).symm
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Reduction kills multiplication by an element of the actual residue kernel. -/
lemma multiplication_reduction_zero (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hρ : Function.Surjective ρ)
    (π : R) (hπ : ρ π = 0) :
    multiplicationNat σ π ≫ reductionNat σ ρ hσ hρ = 0 := by
  apply NatTrans.ext
  funext M
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (reductionHom σ ρ hσ hρ M).hom.hom (π • x) = 0
  rw [map_smul]
  change @SMul.smul F M (inferInstanceAs (SMul F M)) (ρ π)
    ((reductionHom σ ρ hσ hρ M).hom.hom x) = (0 : M)
  rw [hπ]
  exact zero_smul F (show M from (reductionHom σ ρ hσ hρ M).hom.hom x)

/-- The literal tensor and restriction maps give genuine pointwise short exact sequences. -/
theorem pointwise_shortExact [IsDomain R] (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hρ : Function.Surjective ρ)
    (π : R) (hπ0 : ρ π = 0) (hπ : π ≠ 0)
    (hker : RingHom.ker ρ = Ideal.span {π}) (M : FGModuleCat.{u} F) :
    (ShortComplex.mk ((multiplicationNat σ π).app M) ((reductionNat σ ρ hσ hρ).app M)
      (NatTrans.congr_app (multiplication_reduction_zero σ ρ hσ hρ π hπ0) M)).ShortExact := by
  let := σ.toAlgebra
  let f : R →ₗ[F] R := LinearMap.mul F R π
  let g : R →ₗ[F] F := residueLinear σ ρ hσ
  have hfg : Function.Exact f g := by
    intro r
    change ρ r = 0 ↔ ∃ s, π * s = r
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩
  have hmul (x : R ⊗[F] M) : f.rTensor M x = π • x := by
    induction x using TensorProduct.inductionOn with
    | tmul r m => rfl
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have htensor : Function.Exact (f.rTensor M) (g.rTensor M) :=
    _root_.rTensor_exact M hfg hρ
  have hinj : Function.Injective (f.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap f (by
      intro x y h
      exact mul_left_cancel₀ hπ h)
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (TensorProduct.lid F M) (g.rTensor M x) = 0 at hx
    have hx0 : g.rTensor M x = 0 := (TensorProduct.lid F M).injective (by
      simpa only [map_zero] using hx)
    obtain ⟨y, hy⟩ := (htensor x).mp hx0
    refine ⟨y, ?_⟩
    change π • y = x
    exact (hmul y).symm.trans hy
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y h
    apply hinj
    change π • x = π • y at h
    exact (hmul x).trans (h.trans (hmul y).symm)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro m
    change M at m
    refine ⟨((1 : R) ⊗ₜ[F] m : R ⊗[F] M), ?_⟩
    change ρ (1 : R) • m = m
    rw [map_one, one_smul]

/-- The actual tensor conflation makes original residue restriction trivial on SmallK. -/
theorem restriction_smallKMap_eq_one [IsDomain R] (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hρ : Function.Surjective ρ)
    (π : R) (hπ0 : ρ π = 0) (hπ : π ≠ 0)
    (hker : RingHom.ker ρ = Ideal.span {π}) (n : ℕ) :
    (restrictionExact ρ hρ).smallKMap.{u} n = 1 := by
  apply smallKMap_eq_one_of_self_conflation (tensorExact σ) (restrictionExact ρ hρ)
    (multiplicationNat σ π) (reductionNat σ ρ hσ hρ)
    (multiplication_reduction_zero σ ρ hσ hρ π hπ0)
  intro M
  exact pointwise_shortExact σ ρ hσ hρ π hπ0 hπ hker M

end Functors

section Dvr

open ModuleCat.FiniteLocalization.IdealClosedSupport

variable {F R : Type u} [Field F] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Original residue restriction has trivial SmallK-map for every split-residue DVR. -/
theorem residueRestriction_smallKMap_eq_one (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R)
    (n : ℕ) : (restrictionExact ρ (split_surjective σ ρ hσ)).smallKMap.{u} n = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmem : π ∈ IsLocalRing.maximalIdeal R := hπ.not_isUnit
  have hπ0 : ρ π = 0 := (RingHom.mem_ker).mp (hker.symm ▸ hmem)
  exact restriction_smallKMap_eq_one σ ρ hσ (split_surjective σ ρ hσ) π hπ0 hπ.ne_zero
    (hker.trans hπ.maximalIdeal_eq) n

/-- The coefficient projection induces a section of the original quotient-residue map. -/
def quotientSection (σ : F →+* R) (ρ : R →+* F)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R) :
    (R ⧸ IsLocalRing.maximalIdeal R) →+* R :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (σ.comp ρ) (by
    intro r hr
    have hz : ρ r = 0 := (RingHom.mem_ker).mp (hker.symm ▸ hr)
    change σ (ρ r) = 0
    rw [hz, map_zero])

/-- The induced section splits the actual quotient ring homomorphism. -/
lemma quotientSection_splits (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp (quotientSection σ ρ hker) =
      RingHom.id (R ⧸ IsLocalRing.maximalIdeal R) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (σ (ρ r)) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r
  rw [Ideal.Quotient.eq, ← hker, RingHom.mem_ker, map_sub]
  have hs : ρ (σ (ρ r)) = ρ r := DFunLike.congr_fun hσ (ρ r)
  rw [hs, sub_self]

/-- The original quotient-residue pushforward is trivial in every SmallK-degree. -/
theorem closedRestriction_smallKMap_eq_one (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R)
    (n : ℕ) : (closedRestrictionExact (IsLocalRing.maximalIdeal R)).smallKMap.{u} n = 1 := by
  let s := quotientSection σ ρ hker
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : q π = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hπ.not_isUnit
  have hkq : RingHom.ker q = Ideal.span {π} :=
    (Ideal.mk_ker).trans hπ.maximalIdeal_eq
  change (restrictionExact (F := IsLocalRing.ResidueField R) (R := R) q
    Ideal.Quotient.mk_surjective).smallKMap.{u} n = 1
  exact restriction_smallKMap_eq_one (F := IsLocalRing.ResidueField R) s q
    (quotientSection_splits σ ρ hσ hker)
    Ideal.Quotient.mk_surjective π hπ0 hπ.ne_zero hkq n

/-- Every height-one prime of the actual DVR is its maximal ideal. -/
lemma prime_eq_maximal (p : IsDedekindDomain.HeightOneSpectrum R) :
    p = IsDiscreteValuationRing.maximalIdeal R :=
  IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal p.isMaximal)

/-- Original quotient-residue pushforward onto actual torsion support is surjective. -/
theorem residueSupport_surjective (n : ℕ) : Function.Surjective
    (Quillen.DedekindResidue.quotientResidueSupportKMap R
      (IsDiscreteValuationRing.maximalIdeal R) n) := by
  let p := IsDiscreteValuationRing.maximalIdeal R
  intro x
  obtain ⟨a, ha⟩ := (Quillen.DedekindResidue.residuePrimaryKEquiv R p n).surjective
    ((Quillen.DedekindPrimary.primaryEvaluationExactFunctor R p).KMap n x)
  refine ⟨a, ?_⟩
  apply Quillen.DedekindPrimary.supportedK_ext R n
  intro q
  have hq : q = p := prime_eq_maximal q
  subst q
  have hi := DFunLike.congr_fun
    (Quillen.DedekindPrimary.primaryEvaluationKMap_comp_inclusion R n p)
      ((Quillen.DedekindResidue.residueToPrimaryExact R p).KMap n a)
  have he := DFunLike.congr_fun
    (Quillen.DedekindResidue.residuePrimaryKEquiv_toMonoidHom R p n) a
  change (Quillen.DedekindPrimary.primaryEvaluationExactFunctor R p).KMap n
      (Quillen.DedekindResidue.quotientResidueSupportKMap R p n a) = _
  rw [Quillen.DedekindResidue.quotientResidueSupportKMap_eq]
  exact hi.trans (he.symm.trans ha)

/-- The original supported-to-ambient map is trivial for a split-residue DVR. -/
theorem supportedKMap_eq_one (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R)
    (n : ℕ) : Quillen.FiniteModuleLocalization.supportedKMap (nonZeroDivisors R) n = 1 := by
  ext x
  obtain ⟨a, rfl⟩ := residueSupport_surjective (R := R) n x
  have he := DFunLike.congr_fun
    (Quillen.DedekindResidue.supportedKMap_comp_quotientResidueSupport R
      (IsDiscreteValuationRing.maximalIdeal R) n) a
  calc
    _ = (closedRestrictionExact (IsLocalRing.maximalIdeal R)).smallKMap n a := he
    _ = 1 := by rw [closedRestriction_smallKMap_eq_one σ ρ hσ hker n]; rfl

/-- Original generic finite-module localization is injective for a split-residue DVR. -/
theorem localizationKMap_injective (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R)
    (n : ℕ) : Function.Injective
      (Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← Quillen.FiniteModuleLocalization.supported_range_eq_localization_ker,
    supportedKMap_eq_one σ ρ hσ hker n, MonoidHom.range_one]

/-- The degree-two original localization map, for the current DVR application. -/
theorem localizationKMap_two_injective (σ : F →+* R) (ρ : R →+* F)
    (hσ : ρ.comp σ = RingHom.id F) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal R) :
    Function.Injective
      (Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) 2) :=
  localizationKMap_injective σ ρ hσ hker 2

/-- A section of the original quotient-residue map suffices for all-degree injectivity. -/
theorem localizationKMap_injective_of_residueSection
    (s : IsLocalRing.ResidueField R →+* R)
    (hs : (IsLocalRing.residue R).comp s = RingHom.id (IsLocalRing.ResidueField R)) (n : ℕ) :
    Function.Injective
      (Quillen.FiniteModuleLocalization.localizationKMap (nonZeroDivisors R) n) :=
  localizationKMap_injective s (IsLocalRing.residue R) hs (IsLocalRing.ker_residue (R := R)) n

end Dvr

end Quillen.SplitResidueDvr

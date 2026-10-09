import Quillen.Scheme.Coherent.ClosedImmersion.AffineReflection

/-!
# Actual affine closed-unit kernels lower ideal-power exponents

The ordinary quotient by I M has an actual closed-image target, so its map
factors through the genuine adjunction unit. The kernel of that unit is
therefore a subobject of I M. This proves exponent reduction without replacing
the geometric unit by an unrelated quotient map.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme.ClosedImmersion.General
open FiniteModuleLocalization.IdealClosedSupport
variable {Z : Scheme.{u}} [IsLocallyNoetherian Z]
  (R : CommRingCat.{u}) [IsNoetherianRing R]
  (i : Z ⟶ Spec R) [IsClosedImmersion i]
  (I : Ideal R) (e : Z ≅ Spec (Ideal.closedRing R I))
  (hi : i = e.hom ≫ Ideal.closedMap R I)

/-- Maps into the actual closed essential image factor through the genuine
closed pullback unit, by its adjunction. -/
theorem factor_through_unit (M : Coherent (Spec R)) {Q : Coherent (Spec R)}
    (hQ : (coherentPushforward i).essImage Q) (p : M ⟶ Q) :
    ∃ q : (coherentPushforward i).obj ((coherentPullback i).obj M) ⟶ Q,
      (coherentAdjunction i).unit.app M ≫ q = p := by
  obtain ⟨N, ⟨d⟩⟩ := hQ
  let f := ((coherentAdjunction i).homEquiv M N).symm (p ≫ d.inv)
  refine ⟨(coherentPushforward i).map f ≫ d.hom, ?_⟩
  rw [← Category.assoc]
  change ((coherentAdjunction i).homEquiv M N f) ≫ d.hom = p
  rw [Equiv.apply_symm_apply]
  simp

include e hi in
/-- Every actual section in the unit kernel maps into the genuine
ideal-product submodule I M. -/
theorem kernelUnit_section_mem_idealProduct (M : Coherent (Spec R))
    (x : (coherentSpecModuleEquivalence R).functor.obj
      (kernel ((coherentAdjunction i).unit.app M))) :
    ((coherentSpecModuleEquivalence R).functor.map
      (kernel.ι ((coherentAdjunction i).unit.app M))).hom.hom x ∈
        idealProduct I ((coherentSpecModuleEquivalence R).functor.obj M) := by
  let F := (coherentSpecModuleEquivalence R).functor
  let Q := idealQuotientModule I (F.obj M)
  let A := (coherentSpecModuleEquivalence R).inverse.obj Q
  let π : F.obj M ⟶ Q := FGModuleCat.ofHom (V := F.obj M) (W := Q) (idealProduct I (F.obj M)).mkQ
  let d := (coherentSpecModuleEquivalence R).counitIso.app Q
  let p : M ⟶ A := F.preimage (π ≫ d.inv)
  have hA : (coherentPushforward i).essImage A :=
    (coherentPushforward_essImage_iff R i I e hi A).mpr
      (Ideal.associatedCoherent_killed R I Q (idealQuotientModule_killed I (F.obj M)))
  obtain ⟨q, hq⟩ := factor_through_unit R i M hA p
  have hk : kernel.ι ((coherentAdjunction i).unit.app M) ≫ p = 0 := by
    rw [← hq, ← Category.assoc, kernel.condition, zero_comp]
  have hkF := congrArg F.map hk
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero] at hkF
  have hp : F.map p = π ≫ d.inv := F.map_preimage _
  rw [hp] at hkF
  have hπ : F.map (kernel.ι ((coherentAdjunction i).unit.app M)) ≫ π = 0 :=
    (cancel_mono d.inv).mp (by simpa only [Category.assoc, zero_comp] using hkF)
  have hx := congrArg (fun f ↦ f.hom.hom x) hπ
  change (idealProduct I (F.obj M)).mkQ
    ((F.map (kernel.ι ((coherentAdjunction i).unit.app M))).hom.hom x) = 0 at hx
  exact (Submodule.Quotient.mk_eq_zero _).mp hx

include e hi in
/-- The actual unit kernel lowers an annihilating ideal-power exponent. -/
theorem kernelUnit_power_annihilator (M : Coherent (Spec R)) (n : ℕ)
    (h : I ^ (n + 1) ≤
      Module.annihilator R ((coherentSpecModuleEquivalence R).functor.obj M)) :
    I ^ n ≤ Module.annihilator R ((coherentSpecModuleEquivalence R).functor.obj
      (kernel ((coherentAdjunction i).unit.app M))) := by
  let F := (coherentSpecModuleEquivalence R).functor
  let f := F.map (kernel.ι ((coherentAdjunction i).unit.app M))
  have : Mono f.hom := inferInstanceAs
    (Mono ((forget₂ (FGModuleCat R) (ModuleCat R)).map f))
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  apply (ModuleCat.mono_iff_injective f.hom).mp inferInstance
  rw [f.hom.hom.map_smul, map_zero]
  have hx : f.hom.hom x ∈ idealProduct I (F.obj M) :=
    kernelUnit_section_mem_idealProduct R i I e hi M x
  have hy := Module.mem_annihilator.mp
    (idealProductModule_power_annihilator I (F.obj M) n h hr)
      (⟨f.hom.hom x, hx⟩ : idealProduct I (F.obj M))
  exact congrArg Subtype.val hy

include e hi in
/-- An annihilating ideal power makes the genuine unit-kernel iteration
terminate on the original coherent sheaf. -/
theorem kernelIterate_isZero_of_power_annihilator (M : Coherent (Spec R)) (n : ℕ)
    (h : I ^ n ≤ Module.annihilator R ((coherentSpecModuleEquivalence R).functor.obj M)) :
    IsZero (ReflectorDevissage.kernelIterate (coherentAdjunction i).unit n M) := by
  induction n generalizing M with
  | zero =>
    change IsZero M
    rw [IsZero.iff_id_eq_zero]
    apply (coherentSpecModuleEquivalence R).functor.map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    ext m
    have h1 : (1 : R) ∈ Module.annihilator R
        ((coherentSpecModuleEquivalence R).functor.obj M) := h (by simp)
    simpa using Module.mem_annihilator.mp h1 m
  | succ n ih =>
    exact ih _ (kernelUnit_power_annihilator R i I e hi M n h)

end Quillen.CoherentScheme.ClosedImmersion.General

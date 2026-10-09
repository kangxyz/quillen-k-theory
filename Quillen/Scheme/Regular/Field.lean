import Quillen.Scheme.Comparison.KToG
import Quillen.Scheme.Coherent.Affine.Comparison
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The canonical K-to-G comparison on the spectrum of a field

A coherent sheaf on the spectrum of a field has a finite-dimensional module
of global sections. Its finite basis gives an actual global finite free
sheaf. Thus the genuine vector-bundle inclusion is an exact equivalence,
and the induced canonical comparison is an isomorphism in every degree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- A genuinely finite free module gives a finite locally free sheaf by
transporting its basis through the actual tilde/free-sheaf comparison. -/
theorem finiteLocallyFree_tilde_of_finite_free (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    IsFiniteLocallyFree (Spec R) (tilde M) := by
  let b := Module.Free.chooseBasis R M
  let e : SheafOfModules.free (R := (Spec R).ringCatSheaf)
      (Module.Free.ChooseBasisIndex R M) ≅ tilde M :=
    (tildeFinsupp (Module.Free.ChooseBasisIndex R M)).symm ≪≫
      (tilde.functor R).mapIso b.repr.symm.toModuleIso
  exact finiteLocallyFree_of_iso e

variable (k : Type u) [Field k]

/-- On the spectrum of a field, every actual coherent sheaf is finite
locally free. The proof chooses a finite basis of global sections. -/
theorem finiteLocallyFree_of_coherent_field
    (M : (Spec (CommRingCat.of k)).Modules)
    (hM : CoherentScheme.coherent (Spec (CommRingCat.of k)) M) :
    IsFiniteLocallyFree (Spec (CommRingCat.of k)) M := by
  have h := (CoherentScheme.coherent_spec_iff (CommRingCat.of k) M).mp hM
  have : M.IsQuasicoherent := h.1
  have : Module.Finite k (moduleSpecΓFunctor.obj M) := h.2
  have : IsFiniteLocallyFree (Spec (CommRingCat.of k))
      (tilde (moduleSpecΓFunctor.obj M)) :=
    finiteLocallyFree_tilde_of_finite_free (CommRingCat.of k) _
  let e : tilde (moduleSpecΓFunctor.obj M) ≅ M := asIso M.fromTildeΓ
  exact finiteLocallyFree_of_iso e

/-- The inverse to the actual vector-bundle inclusion on a field spectrum.
It retains the sheaf and every sheaf morphism. -/
def coherentToVectorBundleField :
    CoherentScheme.Coherent (Spec (CommRingCat.of k)) ⥤
      FiniteLocallyFree (Spec (CommRingCat.of k)) :=
  ObjectProperty.ιOfLE (fun M hM => finiteLocallyFree_of_coherent_field k M hM)

instance coherentToVectorBundleField_additive : (coherentToVectorBundleField k).Additive where
  map_add := by intros; rfl

/-- The inverse preserves actual short exact sheaf sequences. -/
def coherentToVectorBundleFieldExact :
    ExactFunctor (CoherentScheme.coherentExactStructure (Spec (CommRingCat.of k)))
      (vectorBundleExactStructure (Spec (CommRingCat.of k))) where
  toFunctor := coherentToVectorBundleField k
  map_conflation S hS :=
    (CoherentScheme.coherent_shortExact_iff (Spec (CommRingCat.of k)) S).mp hS

/-- Inclusion followed by the field inverse keeps the same vector bundle. -/
def vectorBundleFieldUnitIso :
    ((vectorBundleToCoherentExact (Spec (CommRingCat.of k))).comp
      (coherentToVectorBundleFieldExact k)).toFunctor ≅
      (ExactFunctor.id (vectorBundleExactStructure (Spec (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

/-- The field inverse followed by inclusion keeps the same coherent sheaf. -/
def vectorBundleFieldCounitIso :
    ((coherentToVectorBundleFieldExact k).comp
      (vectorBundleToCoherentExact (Spec (CommRingCat.of k)))).toFunctor ≅
      (ExactFunctor.id (CoherentScheme.coherentExactStructure
        (Spec (CommRingCat.of k)))).toFunctor :=
  Iso.refl _

end Quillen.SchemeSheaf

namespace Quillen.Scheme
variable (k : Type u) [Field k]

/-- The K-theory map of the actual inverse exact functor over a field. -/
def GToKField (n : ℕ) :
    G (Spec (CommRingCat.of k)) n →* K (Spec (CommRingCat.of k)) n :=
  (SchemeSheaf.coherentToVectorBundleFieldExact k).smallKMap.{u+1} n

@[simp]
theorem GToKField_comp_KToG (n : ℕ) :
    (GToKField k n).comp (KToG (Spec (CommRingCat.of k)) n) =
      MonoidHom.id (K (Spec (CommRingCat.of k)) n) := by
  change ((SchemeSheaf.coherentToVectorBundleFieldExact k).smallKMap.{u+1} n).comp
      ((SchemeSheaf.vectorBundleToCoherentExact (Spec (CommRingCat.of k))).smallKMap.{u+1} n) = _
  rw [← ExactFunctor.smallKMap_comp]
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u+1} (SchemeSheaf.vectorBundleFieldUnitIso k) n).trans
    (ExactFunctor.smallKMap_id.{u+1} _ n)

@[simp]
theorem KToG_comp_GToKField (n : ℕ) :
    (KToG (Spec (CommRingCat.of k)) n).comp (GToKField k n) =
      MonoidHom.id (G (Spec (CommRingCat.of k)) n) := by
  change ((SchemeSheaf.vectorBundleToCoherentExact (Spec (CommRingCat.of k))).smallKMap.{u+1} n).comp
      ((SchemeSheaf.coherentToVectorBundleFieldExact k).smallKMap.{u+1} n) = _
  rw [← ExactFunctor.smallKMap_comp]
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u+1} (SchemeSheaf.vectorBundleFieldCounitIso k) n).trans
    (ExactFunctor.smallKMap_id.{u+1} _ n)

/-- The canonical finite-locally-free K-to-coherent-G map is bijective on a
field spectrum, in every degree. -/
theorem KToG_field_bijective (n : ℕ) :
    Function.Bijective (KToG (Spec (CommRingCat.of k)) n) := by
  have hl := DFunLike.congr_fun (GToKField_comp_KToG k n)
  have hr := DFunLike.congr_fun (KToG_comp_GToKField k n)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- The canonical comparison as a multiplicative equivalence. Its forward
homomorphism is exactly `Scheme.KToG`, not a newly chosen unrelated map. -/
def KToGFieldEquiv (n : ℕ) :
    K (Spec (CommRingCat.of k)) n ≃* G (Spec (CommRingCat.of k)) n :=
  MulEquiv.ofBijective (KToG (Spec (CommRingCat.of k)) n) (KToG_field_bijective k n)

@[simp]
theorem KToGFieldEquiv_toMonoidHom (n : ℕ) :
    (KToGFieldEquiv k n).toMonoidHom = KToG (Spec (CommRingCat.of k)) n := rfl

end Quillen.Scheme

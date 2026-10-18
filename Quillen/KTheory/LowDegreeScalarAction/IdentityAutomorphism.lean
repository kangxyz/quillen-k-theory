/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HomotopyGroups.SelfTrackOperation
public import Quillen.KTheory.SpaceAction
public import Quillen.KTheory.Map.NaturalIso
public import Quillen.Topology.ClassifyingSpace.FunctorChain
public import Quillen.CategoryTheory.QConstruction.ZeroEndomorphisms
public import Quillen.CategoryTheory.TheoremB.CompositionHomotopy

/-!
# Low-degree operations of actual identity natural automorphisms

A natural automorphism of the identity exact functor gives a whole based
self-homotopy of the unchanged original Q identity map. Its actual normalized
self-tracks define K0-to-K1 and K1-to-K2 operations. Both are additive in their
source class. The genuine composition prism proves additivity and the identity
law in the natural-automorphism variable for the displayed consumer universes.

Those universes cover the native finite-module and finite-projective categories
and the chosen upper SmallModel. The representative equations retain the original
track-first cubes and their existing sign relative to loop normalization.
These are identity-automorphism operations; scalar-unit instantiation, ordered
symbol/product marking, exact-functor coherence and localization-boundary
compatibility are separate obligations.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
universe u v
namespace Quillen.LowDegreeScalarAction.IdentityAutomorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- The original zero-normalized identity Q-functor is the identity functor. -/
theorem normalizedIdentityQ : (ExactFunctor.id E).normalizedQ = 𝟭 E.QCategory := by
  have hz : (ExactFunctor.id E).toFunctor.mapZeroObject = Iso.refl (0 : C) := by
    apply Iso.ext
    apply Subsingleton.elim
  change rebaseFunctor (ExactFunctor.id E).mapQ E.qZero E.qZero
    (E.qIsoOfIso (ExactFunctor.id E).toFunctor.mapZeroObject) = _
  rw [hz]
  change rebaseFunctor (ExactFunctor.id E).mapQ E.qZero E.qZero (Iso.refl _) = _
  exact (rebaseFunctor_refl (ExactFunctor.id E).mapQ E.qZero).trans (ExactFunctor.mapQ_id E)

/-- The original normalized identity Q-map is the unchanged identity continuous map. -/
theorem normalizedIdentityMap :
    (classifyingSpaceMap (ExactFunctor.id E).normalizedQ).hom = ContinuousMap.id E.KSpace := by
  rw [normalizedIdentityQ, classifyingSpaceMap_id]
  rfl

/-- The original normalized-Q natural transformation, realized as a whole
identity self-homotopy fixed at the original zero vertex. -/
def homotopy (u : 𝟭 C ≅ 𝟭 C) :
    (ContinuousMap.id E.KSpace).HomotopyRel (ContinuousMap.id E.KSpace) {E.kBasepoint} :=
  (classifyingSpaceNaturalTransformationBasedHomotopy
    (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u).hom
    E.qZero (ExactFunctor.normalizedQIso_obj_base (F := ExactFunctor.id E) (G := ExactFunctor.id E))
    (ExactFunctor.normalizedQIso_hom_base (F := ExactFunctor.id E) (G := ExactFunctor.id E) u)).cast
      (normalizedIdentityMap E) (normalizedIdentityMap E)

/-- The whole original normalized-Q track fixes the distinguished zero vertex. -/
lemma homotopy_fixed (u : 𝟭 C ≅ 𝟭 C) (t : unitInterval) :
    homotopy E u (t, E.kBasepoint) = E.kBasepoint :=
  (homotopy E u).eq_snd t rfl

/-- Actual degree-(0,1) operation on the original quotient. Its proved
source group law is bundled below as kZeroActionHom. -/
def kZeroAction (u : 𝟭 C ≅ 𝟭 C) : E.K 0 → E.K 1 :=
  IdentityTrack.operation (homotopy E u).toHomotopy (homotopy_fixed E u) 0

/-- Actual degree-(1,1) operation, already additive in its source class. -/
def kOneAction (u : 𝟭 C ≅ 𝟭 C) : E.K 1 →* E.K 2 :=
  IdentityTrack.hom (homotopy E u).toHomotopy (homotopy_fixed E u) 0

/-- The original zero input gives the identity output. -/
@[simp] theorem kZeroAction_one (u : 𝟭 C ≅ 𝟭 C) : kZeroAction E u 1 = 1 :=
  IdentityTrack.operation_one (homotopy E u).toHomotopy (homotopy_fixed E u) 0

/-- Source additivity in K-zero uses the proved actual object-loop action. -/
theorem kZeroAction_mul (u : 𝟭 C ≅ 𝟭 C) (a b : E.K 0) :
    kZeroAction E u (a * b) = kZeroAction E u a * kZeroAction E u b :=
  IdentityTrack.operation_mul_zero (homotopy E u).toHomotopy (homotopy_fixed E u)
    (qSpace_piTwo_pathTransport_loop E) a b

/-- The original degree-(0,1) operation, now equipped with its proved source group law. -/
def kZeroActionHom (u : 𝟭 C ≅ 𝟭 C) : E.K 0 →* E.K 1 where
  toFun := kZeroAction E u
  map_one' := kZeroAction_one E u
  map_mul' := kZeroAction_mul E u

/-- The actual K-zero input cube gives the unchanged track-first output cube. -/
theorem kZeroAction_cube (u : 𝟭 C ≅ 𝟭 C)
    (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    kZeroAction E u ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 0 p
        (IdentityTrack.track (homotopy E u).toHomotopy (homotopy_fixed E u) 0 p)⟧ : E.K 1) :=
  (genLoopNormalizedSelfTrackCube_class 0 p _).symm

/-- The actual K-one input cube gives the unchanged track-first output cube. -/
theorem kOneAction_cube (u : 𝟭 C ≅ 𝟭 C)
    (p : GenLoop (Fin 2) E.KSpace E.kBasepoint) :
    kOneAction E u ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 1 p
        (IdentityTrack.track (homotopy E u).toHomotopy (homotopy_fixed E u) 1 p)⟧ : E.K 2) :=
  (genLoopNormalizedSelfTrackCube_class 1 p _).symm

/-- Every track time is the original normalized-Q natural-transformation
homotopy evaluated on the original input cube. -/
theorem track_apply (u : 𝟭 C ≅ 𝟭 C) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) E.KSpace E.kBasepoint)
    (t : unitInterval) (z : Fin (m + 1) → unitInterval) :
    IdentityTrack.track (homotopy E u).toHomotopy (homotopy_fixed E u) m p t z =
      classifyingSpaceNaturalTransformationHomotopy
        (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u).hom
          (t, p z) := rfl

/-- The degree-zero representative retains the original inverse relating
track-first and spatial-first normalization. -/
theorem kZeroAction_normalization (u : 𝟭 C ≅ 𝟭 C)
    (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    kZeroAction E u ⟦p⟧ =
      (loopKOneNormalization (genLoopHomeomorphOfUnique (Fin 1) p)
        ⟦(IdentityTrack.track (homotopy E u).toHomotopy (homotopy_fixed E u) 0 p).map
          (genLoopHomeomorphOfUnique (Fin 1)).continuous⟧)⁻¹ :=
  IdentityTrack.operation_zero_normalization (homotopy E u).toHomotopy (homotopy_fixed E u) p

end Quillen.LowDegreeScalarAction.IdentityAutomorphism

namespace Quillen.LowDegreeScalarAction.IdentityAutomorphism
variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

private theorem normalizedQIso_trans (u v : 𝟭 C ≅ 𝟭 C) :
    ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) (u ≪≫ v) =
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) ≪≫
        (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) v) := by
  have hm : ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) (u ≪≫ v) =
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) ≪≫
        (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) v) := by
    apply Iso.ext
    apply NatTrans.ext
    funext A
    exact congrArg Iso.hom (E.qIsoOfIso_trans (u.app A.obj.of) (v.app A.obj.of))
  unfold ExactFunctor.normalizedQIso
  rw [rebaseFunctorNatIso, hm]
  simp [rebaseFunctorNatIso, Iso.trans_assoc]

/-- The actual composable-transformation prism compares the whole original
tracks; the displayed universe condition makes this original Q-category small. -/
private def compositionHomotopy (u v : 𝟭 C ≅ 𝟭 C) :
    (homotopy E (u ≪≫ v)).toHomotopy.toContinuousMap.HomotopyRel
      (((homotopy E u).toHomotopy).trans (homotopy E v).toHomotopy).toContinuousMap
      {z : unitInterval × E.KSpace | z.1 = 0 ∨ z.1 = 1} := by
  let α := (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u).hom
  let β := (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) v).hom
  have he : (homotopy E (u ≪≫ v)).toHomotopy.toContinuousMap =
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).toContinuousMap := by
    change (classifyingSpaceNaturalTransformationHomotopy
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E)
        (u ≪≫ v)).hom).toContinuousMap = _
    rw [normalizedQIso_trans]
    rfl
  exact (TheoremB.naturalTransformationCompositionHomotopy α β).cast he.symm rfl

/-- The entire composable-transformation prism fixes the original zero vertex. -/
private lemma compositionHomotopy_fixed (u v : 𝟭 C ≅ 𝟭 C) (s t : unitInterval) :
    compositionHomotopy E u v (s, (t, E.kBasepoint)) = E.kBasepoint := by
  let α := (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u).hom
  let β := (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) v).hom
  change TheoremB.functorChainRealization (ComposableArrows.mk₂ α β)
    (classifyingSpacePoint E.qZero,
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 2)).symm
        (TheoremB.compositionTriangleHomotopy (s, t))) =
        classifyingSpacePoint E.qZero
  apply TheoremB.functorChainRealization_vertex_of_subsingleton _ E.qZero E.qZero
  · intro i
    fin_cases i <;> change (ExactFunctor.id E).normalizedQ.obj E.qZero = E.qZero <;>
      rw [normalizedIdentityQ E] <;> rfl
  · intro A
    exact E.qHom_subsingleton_of_isZero A E.qZero (isZero_zero C)

/-- Composition of identity automorphisms adds their actual normalized-track
operations, in the unchanged track-product convention. -/
theorem action_trans (u v : 𝟭 C ≅ 𝟭 C) (m : ℕ) (a : E.K m) :
    IdentityTrack.operation (homotopy E (u ≪≫ v)).toHomotopy
      (homotopy_fixed E (u ≪≫ v)) m a =
      IdentityTrack.operation (homotopy E v).toHomotopy (homotopy_fixed E v) m a *
        IdentityTrack.operation (homotopy E u).toHomotopy (homotopy_fixed E u) m a := by
  have hUV (t : unitInterval) :
      ((homotopy E u).toHomotopy.trans (homotopy E v).toHomotopy) (t, E.kBasepoint) =
        E.kBasepoint := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> apply homotopy_fixed
  exact (IdentityTrack.operation_eq_of_relative_homotopy
    (homotopy E (u ≪≫ v)).toHomotopy (homotopy_fixed E (u ≪≫ v))
    ((homotopy E u).toHomotopy.trans (homotopy E v).toHomotopy) hUV
    (compositionHomotopy E u v) (compositionHomotopy_fixed E u v) m a).trans
      (IdentityTrack.operation_trans (homotopy E u).toHomotopy (homotopy_fixed E u)
        (homotopy E v).toHomotopy (homotopy_fixed E v) hUV m a)

/-- The identity natural automorphism has zero operation, deduced from the
actual composition prism and cancellation in the target group. -/
theorem action_one (m : ℕ) (a : E.K m) :
    IdentityTrack.operation (homotopy E (Iso.refl (𝟭 C))).toHomotopy
      (homotopy_fixed E (Iso.refl (𝟭 C))) m a = 1 := by
  let F : Aut (𝟭 C) → E.K (m + 1) := fun u =>
    IdentityTrack.operation (homotopy E u).toHomotopy (homotopy_fixed E u) m a
  let e : Aut (𝟭 C) := Iso.refl (𝟭 C)
  have h : F e = F e * F e :=
    (congrArg F (Iso.refl_trans e)).symm.trans (action_trans E e e m a)
  exact mul_left_cancel (h.symm.trans (mul_one (F e)).symm)

/-- The actual automorphism-group multiplication has exactly its ordinary
induced operation product, with the category's composition convention retained. -/
theorem action_mul (u v : Aut (𝟭 C)) (m : ℕ) (a : E.K m) :
    IdentityTrack.operation (homotopy E (u * v)).toHomotopy
      (homotopy_fixed E (u * v)) m a =
      IdentityTrack.operation (homotopy E u).toHomotopy (homotopy_fixed E u) m a *
        IdentityTrack.operation (homotopy E v).toHomotopy (homotopy_fixed E v) m a :=
  action_trans E v u m a

/-- Degree-(0,1) additivity in the actual natural-automorphism variable. -/
def kZeroNatAut (a : E.K 0) : Aut (𝟭 C) →* E.K 1 where
  toFun u := kZeroAction E u a
  map_one' := action_one E 0 a
  map_mul' u v := action_mul E u v 0 a

/-- Degree-(1,1) additivity in the actual natural-automorphism variable. -/
def kOneNatAut (a : E.K 1) : Aut (𝟭 C) →* E.K 2 where
  toFun u := kOneAction E u a
  map_one' := action_one E 1 a
  map_mul' u v := action_mul E u v 1 a

end Quillen.LowDegreeScalarAction.IdentityAutomorphism

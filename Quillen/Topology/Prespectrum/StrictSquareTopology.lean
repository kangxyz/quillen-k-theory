/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareCone
public import Quillen.Topology.Prespectrum.HomotopyPushoutSeparation
public import Quillen.Topology.Prespectrum.ConeLoopSeparation
public import Quillen.Topology.Prespectrum.PushoutReduction
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Quillen.Topology.Prespectrum.ParameterLoopingPointHEP

/-!
# Point-set closure of the original strict-square Bass value

The actual reduced double cylinder, cone and compact-open loop retain T1 separation and
HEP of their literal chosen points. The assertions hold at every original level, including
zero; no replacement topology or inference from T1 separation to point HEP is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)

/-- T1 separation passes through the original double cylinder. -/
instance spanSpaceT1Space [T1Space (S.left.left.space n)] [T1Space (S.left.right.space n)]
    [T1Space (S.right.left.space n)] : T1Space ((span S).space n) :=
  HomotopyPushout.prespectrumSpaceT1Space S.left.hom S.hom.left n

/-- T1 separation passes through the unchanged cone and parameter loop. -/
instance loopedConeSpaceT1Space [T1Space (S.left.left.space n)]
    [T1Space (S.left.right.space n)] [T1Space (S.right.left.space n)]
    [T1Space (S.right.right.space n)] :
    T1Space ((strictSquareLoopedConeFunctor.obj S).space n) := by
  change T1Space ((parameterLooping (mappingCone (comparison S))).space n)
  infer_instance

/-- The actual chosen span point has HEP whenever the three original corner points do. -/
theorem span_point_homotopyExtensionProperty
    (hA : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n)))) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((span S).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty S.left.hom S.hom.left n hA hB hC

/-- The literal cone point inherits the four genuine point-extension properties. -/
theorem cone_point_homotopyExtensionProperty
    (hA : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n))))
    (hD : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point n)))) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
      ((mappingCone (comparison S)).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty
    ((span S).point n) (S.right.right.point n) ((comparison S).map n)
    ((comparison S).map_point n) (span_point_homotopyExtensionProperty S n hA hB hC) hD

/-- Closed original points with HEP remain well-based in the actual looped cone. -/
theorem loopedCone_point_homotopyExtensionProperty
    [T1Space (S.left.left.space n)] [T1Space (S.left.right.space n)]
    [T1Space (S.right.left.space n)] [T1Space (S.right.right.space n)]
    (hA : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n))))
    (hD : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point n)))) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
      ((strictSquareLoopedConeFunctor.obj S).point n))) :=
  parameterLooping_point_homotopyExtensionProperty (mappingCone (comparison S)) n
    isClosed_singleton (cone_point_homotopyExtensionProperty S n hA hB hC hD)

end Quillen.LoopPrespectrum.StrictSquare

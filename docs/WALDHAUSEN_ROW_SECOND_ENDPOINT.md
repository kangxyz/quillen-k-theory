# The genuine second cylinder endpoint on actual quotient rows

The second original endpoint injection is a genuine Reedy row cofibration,
proved by the accepted displayed endpoint coproduct pushout and cofibration
pushout closure. Composing it with the actual joint cylinder cofibration
gives `RowFactorization.targetInclusion` with its unchanged component formula.

`JointData` records only the first endpoint factorization. Its existing
fields do not imply that the projection retracts the second endpoint.
The new `SecondEndpointSection` names this precise additional structural
identity; the generic row lift proves the same identity on original row maps.
For the actual complex cylinder `complexJointData_secondEndpointSection`
proves it directly: the target component is the literal biproduct inclusion,
and its original projection is the biproduct second projection. No section
identity is assumed in this concrete instance.

Coarse two-out-of-three makes the target inclusion coarse weak, since its
composite with the coarse-weak projection is identity. For an original
coarse-weak arrow it also makes the first inclusion coarse weak. The result
is the actual span X → T(f) ← Y of coarse-weak cofibrations over Y, with
its original natural maps. No extension or fine-saturation hypothesis is
needed. Cone/shift closure remains the exact accepted complex joint-cylinder
hypothesis.

This is the small structural input for a prospective Quillen-A comma
contraction. No comma contraction, mixed-nerve equivalence, or fibration is
asserted by this source. The focused source check passed warning-free;
the final fixed18 recursive audit and all13 consumers also passed
warning-free after an audit-only instance-style cleanup. The
source manifest is `logs/row-cylinder-second-endpoint-sources.sha256`, and
the audit is `audits/RowCylinderSecondEndpointAudit.lean`.

Independent review passed: fresh target rebuild, fixed18 recursive origins and15
original-map/ordinal-reindexing/combined-endpoint consumers, warning-free with
unchanged source and prerequisite hashes.

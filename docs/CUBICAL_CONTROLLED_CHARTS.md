# Finite cubical lifting with all incident charts

The four frozen modules are FaceContainment, IncidentCharts,
ControlledLifting, and ControlledChartLifting, under CubicalSubdivision.

An interior intersection of canonical grid faces forces actual whole-face
containment. Each face therefore carries every chart assigned to any
containing face. Filling in dimension order retains every one of these source
constraints; pasting uses the actual quotient skeleton and preserves the
whole original outer boundary and target map. Source chart sets need not be
open. Actual RLP on every nonempty finite intersection, together with a genuine
open parameter cover controlling the original target and boundary, supplies
each local filler.

This is a proved finite local-to-global lifting theorem. It does not replace
its local RLP inputs by weak equivalences. The separate ControlledWeakCharts
module supplies ordinary strict HELP from weak inputs by genuine mapping paths.

The source manifest is `logs/cubical-controlled-charts-sources.sha256`.
The author audit `audits/CubicalControlledChartsAudit.lean` checked exactly
22 origins split `[3,12,2,5]` and 13 consumers, including dimension zero and
empty chart index. Initial terminal evidence is
`logs/cubical-controlled-charts-initial-audit.log`; fixed-count replay is
`logs/cubical-controlled-weak-charts-check2.log` (terminal 14:52:35 UTC).
Only the standard three axioms occur. Independent fresh acceptance and the
stronger 21-consumer audit are recorded in
`docs/REVIEW_20261009_CUBICAL_CONTROLLED_CHARTS.md`.

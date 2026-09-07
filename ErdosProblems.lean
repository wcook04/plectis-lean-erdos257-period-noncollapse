-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
--
-- Problem-centric root for the Erdős Problems library.
--
-- `Erdos249257` holds the shared machinery: the certificate kernel, the greedy
-- achievement set, the Mersenne–Lambert ladder, and the carry systems both
-- problems are built on. This library holds the work that is stated per
-- problem and reads more naturally under the problem's own name.
--
-- Both Erdős Problem 249 (irrationality of ∑ φ(n)/2ⁿ) and Erdős Problem 257
-- (irrationality of ∑_{n∈A} 1/(2ⁿ−1) for every infinite A) are OPEN. Nothing
-- imported here decides either of them.
-- Keep the reviewed finite `t ≤ 82` certificate band inside the supported
-- root closure, so a clean root build re-elaborates its proof authority.

import ErdosProblems.AxiomAudit
import ErdosProblems.DemandLedger
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Root
import ErdosProblems.Skip.LadderT67
import ErdosProblems.Erdos68.GapScalarNormalForm
import ErdosProblems.Erdos68.PrimeThresholdParity
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow
import ErdosProblems.Erdos243.RepairEntropy
import ErdosProblems.Erdos1041.CriticalBlaschkePairBound
import ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo
import ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo
import ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector
import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice
import ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse
import ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector
import ErdosProblems.Erdos1041.NearFeketeTransverseClosure
import ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1NoGo
import ErdosProblems.Erdos1041.PolarDerivativeCircle
import ErdosProblems.Erdos1041.PoissonTaylorFiniteIdentity
import ErdosProblems.Erdos1049.TwoSelectorRemainderEscape
import ErdosProblems.Erdos1049.QAperyTailDenominator
import ErdosProblems.Erdos1049.FixedDiagonalRationalClearing
import ErdosProblems.Erdos1049.SoutheastBlockDeterminant
import ErdosProblems.Erdos1049.BezoutPluckerJets
import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import ErdosProblems.Erdos1049.PrimitiveTwoAdicMinor
import ErdosProblems.Erdos243.HorizonEscapeOfMass
import ErdosProblems.Erdos243.RepairEntropy
import ErdosProblems.Erdos243.CleanRecoveryLengthCounterexample
import ErdosProblems.Erdos243.CenteredEuclideanFeedback
import ErdosProblems.Erdos243.OrientedFeedbackRoot
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import ErdosProblems.Erdos243.IntegerRoundingBarrier
import ErdosProblems.Erdos243.RecordIncrementBarrier
import ErdosProblems.Erdos243.SaturatedSquareTransport
import ErdosProblems.Erdos243.TwoModulusRecordCut
import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.CubicNeighbourIdentity
import ErdosProblems.Erdos243.SignedDuverneyAlgebra
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.AffineShiftEscape
import ErdosProblems.Erdos251.AffineCylinderCollapse
import ErdosProblems.Erdos251.PolynomialGapSeriesValue
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.PairedCongruenceRationalisation
import ErdosProblems.Erdos249.ResidueClassTotientSeries
import ErdosProblems.Erdos249.PrimeSquareResidueWitness
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity
import ErdosProblems.Erdos249.AffineTotientSignature
import ErdosProblems.Erdos68.RunCylinder
import ErdosProblems.Erdos68.MultiplicativeSuccessorRigidity
import ErdosProblems.Erdos68.PrimePoleCriterion
import ErdosProblems.Erdos68.SecondLayerDigit
import ErdosProblems.Erdos68.BinaryCarryNormalForm
import ErdosProblems.Erdos68.AffineDefectRigidity
import ErdosProblems.Erdos68.DivisorChannelBasis
import ErdosProblems.Erdos269.FloorProductLatticeJump
import ErdosProblems.Erdos257.SignedFinitePeriodNoncollapse
import ErdosProblems.Erdos257.SignedFinitePeriodNoncollapse


/-!
# Problem-centric Erdős research library

This is the supported root for the problem-owned modules. The `Erdos249257`
library remains available as the reviewed #249/#257 corpus.
-/

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
import ErdosProblems.Erdos1041.PaperCriticalValueMeanR10
import ErdosProblems.Erdos1041.PaperCubicCompletion
import ErdosProblems.Erdos1041.PaperMetricScaling
import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos249.PaperCompleteR8.KernelRelationBasis
import ErdosProblems.Erdos249.TypeBReturnV8.CenteringCounterexample
import ErdosProblems.Erdos249.TypeBReturnV8.FiniteFirstHarmonic
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralAssembly
import ErdosProblems.Erdos249.TypeBReturnV8.Audit
import ErdosProblems.Erdos251.AffineCylinderCollapse
import ErdosProblems.Erdos251.AffineShiftEscape
import ErdosProblems.Erdos251.BoundedPerturbationCountermodel
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.KernelDenominatorFloor
import ErdosProblems.Erdos251.OrderLatticeDiagonal
import ErdosProblems.Erdos251.PolynomialGapSeriesValue
import ErdosProblems.Erdos251.RealPrimeGapTail
import ErdosProblems.Erdos269.CertificateSafetyR12
import ErdosProblems.Erdos269.PaperR12WaveAAxiomAudit
import ErdosProblems.Erdos269.PurePowerIrrationality
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.R12.OcticWindowBand
import ErdosProblems.Erdos269.R12.PrefixExtension
import ErdosProblems.Root
import ErdosProblems.Skip.LadderT67
import ErdosProblems.Erdos68.GapScalarNormalForm
import ErdosProblems.Erdos68.PrimeThresholdParity
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow
import ErdosProblems.Erdos68.CanonicalFactorialTermination
import ErdosProblems.Erdos68.FactorialAnalyticBoundary
import ErdosProblems.Erdos68.FactorialShiftFamilyOrbit
import ErdosProblems.Erdos68.FactorialZeroPlateauCertificates
import ErdosProblems.Erdos68.FactorialZeroPlateauSupplement
import ErdosProblems.Erdos68.PrimePoleCriterion
import ErdosProblems.Erdos68.PrimePoleDenominator
import ErdosProblems.Erdos68.ShrinkingTargetNormalForm
import ErdosProblems.Erdos243.LcmRecordExcess
import ErdosProblems.Erdos243.PaperCompleteR11.WindowIncidence
import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape
import ErdosProblems.Erdos243.RepairEntropy
import ErdosProblems.Erdos243.SlowRiseBarrier

/-!
# Problem-centric Erdős research library

This is the supported root for the problem-owned modules. The `Erdos249257`
library remains available as the reviewed #249/#257 corpus.
-/

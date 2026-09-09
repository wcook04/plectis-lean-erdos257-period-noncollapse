import ErdosProblems.Erdos1041.ConnectorR18.All
import ErdosProblems.Erdos1041.ReturnV5.All
import ErdosProblems.Erdos1041.ReturnV5.CrossReturnR18

/-!
# Declaration-complete audit for ConnectorR18 and ReturnV5

AUTHORED / UNRUN. This source-current roster prints every theorem declared
by the 104-theorem ConnectorR18 return, the 63-theorem ReturnV5 roster,
and the separate CrossReturnR18 theorem. A successful allowed-axiom audit
would establish elaboration of these conditional declarations; it would not
construct either analytic supplier or prove the unconditional paper endpoint.
-/

set_option pp.universes false
set_option pp.fullNames true

-- ConnectorR18/Averaging.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.exists_good_lt_of_integral_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.radialWeight_nonneg
#print axioms ErdosProblems.Erdos1041.ConnectorR18.radialWeight_le
#print axioms ErdosProblems.Erdos1041.ConnectorR18.radial_energy_of_coefficient_energy
#print axioms ErdosProblems.Erdos1041.ConnectorR18.two_component_cauchy

-- ConnectorR18/CollectiveReduction.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_log_bounds
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_boundary_squared
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_energy_constant
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collectiveQ_positive
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collectiveQ_lt_open
#print axioms ErdosProblems.Erdos1041.ConnectorR18.two_rpow_one_fourth_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_top_scale
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_closed_constant
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_area_budget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connector_of_collectiveBudget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.collective_connector_573
#print axioms ErdosProblems.Erdos1041.ConnectorR18.conclusion_of_collectiveBudget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.constantFactorPath_of_collectiveBudgets

-- ConnectorR18/CubicBranch.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.nonneg_cube_eq
#print axioms ErdosProblems.Erdos1041.ConnectorR18.scaled_hub_from_critical_expansion
#print axioms ErdosProblems.Erdos1041.ConnectorR18.cubic_minimum_connector
#print axioms ErdosProblems.Erdos1041.ConnectorR18.cubic_complete

-- ConnectorR18/CurveAlgebra.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.inSetAtMost_closed_iff
#print axioms ErdosProblems.Erdos1041.ConnectorR18.InSetAtMost.mono
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connectedAtMost_mono
#print axioms ErdosProblems.Erdos1041.ConnectorR18.closed_to_open
#print axioms ErdosProblems.Erdos1041.ConnectorR18.closed_to_open_mono
#print axioms ErdosProblems.Erdos1041.ConnectorR18.InSetAtMost.refl
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connectedAtMost_of_spokes
#print axioms ErdosProblems.Erdos1041.ConnectorR18.joinCurve_left
#print axioms ErdosProblems.Erdos1041.ConnectorR18.joinCurve_right
#print axioms ErdosProblems.Erdos1041.ConnectorR18.joinCurve_continuousOn
#print axioms ErdosProblems.Erdos1041.ConnectorR18.joinCurve_variation_le
#print axioms ErdosProblems.Erdos1041.ConnectorR18.InSetAtMost.trans
#print axioms ErdosProblems.Erdos1041.ConnectorR18.InSetAtMost.symm
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connectedAtMost_trans
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connectedAtMost_symm

-- ConnectorR18/FiniteAssembly.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sum_conformalRadius_sq_le
#print axioms ErdosProblems.Erdos1041.ConnectorR18.low_energy_of_radius_energy
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sum_sq_le_card_mul_sum_sq
#print axioms ErdosProblems.Erdos1041.ConnectorR18.linear_bound_of_quadratic
#print axioms ErdosProblems.Erdos1041.ConnectorR18.three_energy_budget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sum_permutation
#print axioms ErdosProblems.Erdos1041.ConnectorR18.exists_le_of_sum_le_card_mul
#print axioms ErdosProblems.Erdos1041.ConnectorR18.adjacent_connector_of_budget

-- ConnectorR18/NumericalBounds.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.lowConstant_nonneg
#print axioms ErdosProblems.Erdos1041.ConnectorR18.highConstant_nonneg
#print axioms ErdosProblems.Erdos1041.ConnectorR18.lowConstant_value
#print axioms ErdosProblems.Erdos1041.ConnectorR18.rationalConstant_identity
#print axioms ErdosProblems.Erdos1041.ConnectorR18.rationalConstant_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.openConstant_identity
#print axioms ErdosProblems.Erdos1041.ConnectorR18.openConstant_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sqrt_two_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.log_two_lower
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sqrt_log_two_lower
#print axioms ErdosProblems.Erdos1041.ConnectorR18.pi_upper
#print axioms ErdosProblems.Erdos1041.ConnectorR18.log_forty_thirds_upper
#print axioms ErdosProblems.Erdos1041.ConnectorR18.sqrt_log_forty_thirds_upper
#print axioms ErdosProblems.Erdos1041.ConnectorR18.boundary_squared_constant
#print axioms ErdosProblems.Erdos1041.ConnectorR18.pi_div_sqrt_log_two_upper
#print axioms ErdosProblems.Erdos1041.ConnectorR18.two_rpow_one_third_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.one_div_natCast_le_third
#print axioms ErdosProblems.Erdos1041.ConnectorR18.two_rpow_degree_lt
#print axioms ErdosProblems.Erdos1041.ConnectorR18.top_scale_le
#print axioms ErdosProblems.Erdos1041.ConnectorR18.small_scale_le_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.cfCoefficient_le_rational
#print axioms ErdosProblems.Erdos1041.ConnectorR18.cfCoefficient_lt_seventy_one_tenths
#print axioms ErdosProblems.Erdos1041.ConnectorR18.separatedCoefficient_four_thirds

-- ConnectorR18/PolynomialBranches.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.enumeration_eval
#print axioms ErdosProblems.Erdos1041.ConnectorR18.listed_root
#print axioms ErdosProblems.Erdos1041.ConnectorR18.enumeration_derivative
#print axioms ErdosProblems.Erdos1041.ConnectorR18.listed_root_derivative
#print axioms ErdosProblems.Erdos1041.ConnectorR18.duplicate_is_critical
#print axioms ErdosProblems.Erdos1041.ConnectorR18.criticalMinimum_nonneg
#print axioms ErdosProblems.Erdos1041.ConnectorR18.criticalMinimum_eq_zero_of_duplicate
#print axioms ErdosProblems.Erdos1041.ConnectorR18.factor_two_occurrences
#print axioms ErdosProblems.Erdos1041.ConnectorR18.squarefree_enumeration_injective
#print axioms ErdosProblems.Erdos1041.ConnectorR18.criticalMinimum_pos_of_injective
#print axioms ErdosProblems.Erdos1041.ConnectorR18.repeated_occurrences_complete
#print axioms ErdosProblems.Erdos1041.ConnectorR18.quadratic_critical_value
#print axioms ErdosProblems.Erdos1041.ConnectorR18.quadratic_segment_containment
#print axioms ErdosProblems.Erdos1041.ConnectorR18.quadratic_segment_certificate
#print axioms ErdosProblems.Erdos1041.ConnectorR18.quadratic_length_identity
#print axioms ErdosProblems.Erdos1041.ConnectorR18.quadratic_complete

-- ConnectorR18/R13Relevance.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.ValueSeparatedAt.mono
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_eval_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_eval_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_norm_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_norm_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_normalized_gap_at_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_normalized_gap_at_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_critical_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_critical_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_simple_critical_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_simple_critical_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_middle_value_gt_half
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_criticalMinimum
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_not_valueSeparated_minus_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_not_valueSeparated_one
#print axioms ErdosProblems.Erdos1041.ConnectorR18.r13_minimum_fails_four_thirds
#print axioms ErdosProblems.Erdos1041.ConnectorR18.separated_length_certificate_to_71_10

-- ConnectorR18/SupplierReduction.lean
#print axioms ErdosProblems.Erdos1041.ConnectorR18.connector_of_rayBudget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.conclusion_of_rayBudget
#print axioms ErdosProblems.Erdos1041.ConnectorR18.constantFactorPath_of_rayBudgets

-- ReturnV5/CrossReturnR18.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.constantFactor_iff_degreeFour_residual

-- ReturnV5/CurveInfrastructure.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.connectedAtMost_mono
#print axioms ErdosProblems.Erdos1041.ReturnV5.connectedBelow_of_closed_slack
#print axioms ErdosProblems.Erdos1041.ReturnV5.connectedAtMost_of_spokes
#print axioms ErdosProblems.Erdos1041.ReturnV5.connectedAtMost_refl
#print axioms ErdosProblems.Erdos1041.ReturnV5.connectedAtMost_affine
#print axioms ErdosProblems.Erdos1041.ReturnV5.open_zero_impossible

-- ReturnV5/CyclicCostSelection.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.cyclic_cost_sum
#print axioms ErdosProblems.Erdos1041.ReturnV5.exists_cyclic_cost_le
#print axioms ErdosProblems.Erdos1041.ReturnV5.exists_cyclic_cost_le_average
#print axioms ErdosProblems.Erdos1041.ReturnV5.actual_cyclic_connector_of_budget
#print axioms ErdosProblems.Erdos1041.ReturnV5.shortest_arc_not_shortest_total
#print axioms ErdosProblems.Erdos1041.ReturnV5.cyclic_budget_of_separate_bounds

-- ReturnV5/FirstMergeReduction.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.constantFactor_iff_highDegree_residual

-- ReturnV5/LobeBarrier.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_eval
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_eval_factor
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_root_iff
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_inner_disk
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_outer_circle
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_unique_root_in_barrier
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_no_common_root
#print axioms ErdosProblems.Erdos1041.ReturnV5.lobe_perimeter_numeric_gap

-- ReturnV5/NumericalEnvelopes.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.closed_envelope_exact
#print axioms ErdosProblems.Erdos1041.ReturnV5.closed_envelope_lt
#print axioms ErdosProblems.Erdos1041.ReturnV5.open_envelope_lt
#print axioms ErdosProblems.Erdos1041.ReturnV5.closed_numeric_consumer
#print axioms ErdosProblems.Erdos1041.ReturnV5.open_numeric_consumer
#print axioms ErdosProblems.Erdos1041.ReturnV5.strict_threshold_needs_slack

-- ReturnV5/PrecriticalFinite.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.precritical_energy_of_area
#print axioms ErdosProblems.Erdos1041.ReturnV5.precritical_sum_sq_le
#print axioms ErdosProblems.Erdos1041.ReturnV5.precritical_sum_le
#print axioms ErdosProblems.Erdos1041.ReturnV5.summed_low_piece_budget

-- ReturnV5/QuadraticBranch.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_critical_iff
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_center_value
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_critical_minimum
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_minimum_eq
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_radius_eq
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_diameter_norm
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_diameter_bound
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_segment
#print axioms ErdosProblems.Erdos1041.ReturnV5.constantFactor_quadratic_branch
#print axioms ErdosProblems.Erdos1041.ReturnV5.lowCritical_quadratic
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_open_connector
#print axioms ErdosProblems.Erdos1041.ReturnV5.quadratic_distance

-- ReturnV5/RetainedEndpointAdapters.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.weighted_free_point_exact_target
#print axioms ErdosProblems.Erdos1041.ReturnV5.critical_value_mean_exact_target
#print axioms ErdosProblems.Erdos1041.ReturnV5.reflected_critical_value_exact_target
#print axioms ErdosProblems.Erdos1041.ReturnV5.cubic_root_count_exact_target
#print axioms ErdosProblems.Erdos1041.ReturnV5.primitive_quintic_selector_exact_target

-- ReturnV5/RootOccurrences.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.enumeration_eval
#print axioms ErdosProblems.Erdos1041.ReturnV5.enumeration_root
#print axioms ErdosProblems.Erdos1041.ReturnV5.enumeration_root_iff
#print axioms ErdosProblems.Erdos1041.ReturnV5.enumeration_derivative_eval
#print axioms ErdosProblems.Erdos1041.ReturnV5.enumeration_derivative_at_root
#print axioms ErdosProblems.Erdos1041.ReturnV5.repeated_occurrence_critical
#print axioms ErdosProblems.Erdos1041.ReturnV5.squarefree_rootEnumeration_injective
#print axioms ErdosProblems.Erdos1041.ReturnV5.criticalMinimum_nonneg
#print axioms ErdosProblems.Erdos1041.ReturnV5.criticalMinimum_zero_of_repeated
#print axioms ErdosProblems.Erdos1041.ReturnV5.criticalMinimum_pos_of_injective
#print axioms ErdosProblems.Erdos1041.ReturnV5.constantFactor_repeated_branch

-- ReturnV5/ValueSeparationGuardrail.lean
#print axioms ErdosProblems.Erdos1041.ReturnV5.quartic_normalized_gap_minus_one
#print axioms ErdosProblems.Erdos1041.ReturnV5.quartic_normalized_gap_plus_one
#print axioms ErdosProblems.Erdos1041.ReturnV5.quartic_fails_value_separation_minus_one
#print axioms ErdosProblems.Erdos1041.ReturnV5.quartic_fails_value_separation_plus_one


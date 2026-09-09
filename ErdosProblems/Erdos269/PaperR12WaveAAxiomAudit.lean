import ErdosProblems.Erdos269.R12.ExactModulus
import ErdosProblems.Erdos269.R12.OcticWindowBand
import ErdosProblems.Erdos269.R12.PrefixExtension
import ErdosProblems.Erdos269.CertificateSafetyR12

/-!
# R12 Wave A declaration and axiom audit

This file lists every declaration introduced by the four selected Wave A
modules. It is source-only authoring: no Lean command had been run when this
file and its adoption receipt were created. A future successful build must
capture every `#print axioms` result and check it against the permitted set
`propext`, `Classical.choice`, and `Quot.sound`; missing output fails closed.
-/

namespace ErdosProblems.Erdos269.PaperR12

#check nonintegral_has_integer_gap
#print axioms nonintegral_has_integer_gap
#check exact_modulus_pinning
#print axioms exact_modulus_pinning
#check eventual_escape_of_exact_decay
#print axioms eventual_escape_of_exact_decay
#check actual_exact_modulus_pinning
#print axioms actual_exact_modulus_pinning
#check escape_of_irrational_of_exact_beating
#print axioms escape_of_irrational_of_exact_beating

#check octic_cap_is_exactly_beaten
#print axioms octic_cap_is_exactly_beaten
#check octic_window_band
#print axioms octic_window_band

#check reverseRationalState
#print axioms reverseRationalState
#check completedBase
#print axioms completedBase
#check completedDigit
#print axioms completedDigit
#check completedState
#print axioms completedState
#check reverseRationalState_pos
#print axioms reverseRationalState_pos
#check completedState_pos
#print axioms completedState_pos
#check completedState_recurrence
#print axioms completedState_recurrence
#check finite_prefix_has_positive_rational_completion
#print axioms finite_prefix_has_positive_rational_completion
#check actual_prefix_has_abstract_rational_completion
#print axioms actual_prefix_has_abstract_rational_completion

#check widthCheckBoundedR12
#print axioms widthCheckBoundedR12
#check widthCheckBoundedR12_sound
#print axioms widthCheckBoundedR12_sound
#check widthCheckBoundedR12_actual
#print axioms widthCheckBoundedR12_actual
#check widthCheckBoundedR12_append
#print axioms widthCheckBoundedR12_append
#check cumulativeCheckBoundedR12
#print axioms cumulativeCheckBoundedR12
#check cumulativeCheckBoundedR12_sound
#print axioms cumulativeCheckBoundedR12_sound
#check width_shape_regressions_R12
#print axioms width_shape_regressions_R12
#check factor_two_cannot_be_cancelled_R12
#print axioms factor_two_cannot_be_cancelled_R12
#check finite_coverage_not_cofinal_R12
#print axioms finite_coverage_not_cofinal_R12

end ErdosProblems.Erdos269.PaperR12

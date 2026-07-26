import QuartetV060

/-!
# Axiom audit for the final v0.60 theorem chain

This file is an audit artifact.  The commands below print the axioms used by
the concrete Appendix A nonnegativity theorem, the finite main theorem, and
the sharp asymptotic corollary.
-/

#print axioms QuartetV060.ConcreteFourFamilies.auxiliaryFunctional_nonnegative
#print axioms QuartetV060.MainTheorem.normalized_bounds
#print axioms QuartetV060.Sharpness.normalizedMaximum_tendsto_two_thirds
#print axioms QuartetV060.DistanceCovariance.splitSystemDistanceCovariance_eq_detSquare
#print axioms QuartetV060.DistanceCovariance.splitSystemDistanceCovariance_nonnegative

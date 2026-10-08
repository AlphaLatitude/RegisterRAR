import RegisterRAR

/-! # The axiom ledger

For every main theorem of RegisterRAR, the axioms its proof depends on.  A physical input is never
an axiom here: it is a named hypothesis in the statement of the theorem that uses it.  The expected
output for every line is `[propext, Classical.choice, Quot.sound]`, the logical minimum of classical
mathematics in Lean; `sorryAx` would flag an unfinished proof.  The statement of the main theorem
is printed first, so that its hypotheses, the inputs the paper claims, can be read off. -/

#check @Register.Relation.radial_acceleration_relation

-- The main theorem: its hypotheses are the paper's claimed inputs (Secs. II–VI)
#print axioms Register.Relation.radial_acceleration_relation
#print axioms Register.Relation.hypotheses_consistent

-- Sec. II, the count of the register from Postulate 2 (Horizon.lean)
#print axioms Register.Horizon.exists_loop_not_mem
#print axioms Register.Horizon.two_mul_card_through
#print axioms Register.Horizon.card_cell_eq
#print axioms Register.Horizon.card_cell_eq_two_mul_card_loop
#print axioms Register.Horizon.counts
#print axioms Register.Horizon.even_L

-- Sec. II, positions along the rings: the horizon counts every largest ring (Positions.lean)
#print axioms Register.Horizon.Positions.even_of_halfway
#print axioms Register.Horizon.Positions.dist_opp
#print axioms Register.Horizon.Positions.card_ringDist
#print axioms Register.Horizon.Positions.card_dist_eq
#print axioms Register.Horizon.Positions.card_dist_le
#print axioms Register.Horizon.Positions.horizon_weight_ring

-- The axioms of the count and of the positions have a model (Models.lean)
#print axioms Register.Models.fano_counts
#print axioms Register.Models.fano_even

-- Sec. II, the inputs: one bit, horizon temperatures, Einstein's equations, the horizon, Newton's law, the vacuum (Chain.lean)
#print axioms Register.Reg.one_bit
#print axioms Register.Reg.area_in_cells
#print axioms Register.Reg.lap_time
#print axioms Register.Reg.quarter_lap
#print axioms Register.Reg.T_dS
#print axioms Register.Reg.La_lap
#print axioms Register.Reg.T_Unruh
#print axioms Register.Reg.eta_eq
#print axioms Register.Reg.einstein_coefficient
#print axioms Register.Reg.G_eq
#print axioms Register.Reg.cell_from_G
#print axioms Register.Reg.entropy_quarter
#print axioms Register.Reg.hasDerivAt_fSdS
#print axioms Register.Reg.gSdS_eq
#print axioms Register.Reg.gSdS_mass
#print axioms Register.Reg.deSitter
#print axioms Register.Reg.Ns_eq
#print axioms Register.Reg.radius_from_geodesics
#print axioms Register.Reg.newton_komar
#print axioms Register.Reg.newton_share
#print axioms Register.Reg.vacuum_per_string
#print axioms Register.Reg.string_split

-- Sec. II, the de Sitter horizon: a quarter of a largest ring away, a largest ring's lap as its period (DeSitter.lean)
#print axioms Register.Reg.proper_distance_exists
#print axioms Register.Reg.proper_distance
#print axioms Register.Reg.horizon_period
#print axioms Register.Reg.horizon_temperature

-- Secs. III–VI, the share, what reaches a string, the tolerance, the law and its limits (Law.lean)
#print axioms Register.Law.share_of_equipartition
#print axioms Register.Reg.share_acceleration
#print axioms Register.Reg.fill_fraction
#print axioms Register.Reg.law
#print axioms Register.Reg.law_scale_mean
#print axioms Register.Law.near_limit
#print axioms Register.Law.deep_limit
#print axioms Register.Law.classical_limit
#print axioms Register.Law.tully_fisher

-- Sec. VIII, the scale and Λ at every epoch (Law.lean)
#print axioms Register.Reg.scale_over_time

-- Every number the paper quotes (Numerics.lean)
#print axioms Register.Numerics.Hinf_tight
#print axioms Register.Numerics.κ_tight
#print axioms Register.Numerics.a0_tight
#print axioms Register.Numerics.a0_val
#print axioms Register.Numerics.coefficient
#print axioms Register.Numerics.horizon_values
#print axioms Register.Numerics.elastic_bound
#print axioms Register.Numerics.thermal_values
#print axioms Register.Numerics.string_energy_check
#print axioms Register.Numerics.a0_uncertainty
#print axioms Register.Numerics.a0_sigmas
#print axioms Register.Numerics.a0_local_H0
#print axioms Register.Numerics.tolerance_mean_from_data
#print axioms Register.Numerics.cH0_coefficients
#print axioms Register.Numerics.tully_fisher_speeds
#print axioms Register.Numerics.deep_radii
#print axioms Register.Numerics.solar_system
#print axioms Register.Numerics.neptune_departure
#print axioms Register.Numerics.rar_table
#print axioms Register.Numerics.reg_RL
#print axioms Register.Numerics.reg_a0
#print axioms Register.Numerics.reg_jacobson

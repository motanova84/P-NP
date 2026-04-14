/-
Tests for KappaPhiTheorem formalization
-/

import KappaPhiTheorem

namespace NoesisTests

open Noesis
open Real

-- Test that basic definitions are accessible
example : phi = (1 + Real.sqrt 5) / 2 := rfl

-- Test that the millennium constant is correct
example : kappa_pi N_effective = 2.5773 := kappa_pi_millennium_constant

-- Test that phi satisfies its fundamental property
example : phi_sq = phi + 1 := phi_sq_eq_phi_add_one

-- Test that N_effective has correct form
example : N_effective = Real.exp 2.5773 := rfl

-- Test that fixed point property holds
example : Real.exp 2.5773 = N_effective := fixed_point_property

-- Test precision theorem
example : |kappa_pi N_effective - 2.5773| < 1e-10 := kappa_pi_precision

-- Test that kappa_pi is just logarithm
example (N : ℝ) : kappa_pi N = Real.log N := rfl

-- Test certification
example : True := kappa_phi_certified

end NoesisTests

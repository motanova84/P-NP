/-!
# Tests for Holographic Duality

Basic tests to verify the holographic duality structures compile.
-/

import HolographicDuality
import TseitinHardFamily

open HolographicDuality
open TseitinHardFamily

-- Test that we can construct an AdS3 point
example : AdS3 := ⟨1, 0, 0, by norm_num⟩

-- Test that we can compute geodesic distance
example (p q : AdS3) : ℝ := AdS3_geodesic_distance p q

-- Test that we can build Tseitin formulas
example : TseitinFormula := buildTseitinFormula 1001 (by norm_num) (by omega)

-- Verify the main theorem is stated
#check P_neq_NP_holographic
#check exponential_time_for_SAT_holographic
#check holographic_time_lower_bound
#check tseitin_has_holographic_embedding
#check tseitin_AdSCFT_duality

end

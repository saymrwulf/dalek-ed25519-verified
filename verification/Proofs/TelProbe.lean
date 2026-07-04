import Proofs.ScalarDenote
open Aeneas Aeneas.Std

set_option maxHeartbeats 8000000
set_option exponentiation.threshold 600

namespace ScalarProofs

/-- The 512-bit lo/hi split telescope. -/
theorem wide_split_telescope (v0 v1 v2 v3 v4 v5 v6 v7 : ℕ)
    (h0 : v0 < 2^64) (h1 : v1 < 2^64) (h2 : v2 < 2^64) (h3 : v3 < 2^64)
    (h4 : v4 < 2^64) (h5 : v5 < 2^64) (h6 : v6 < 2^64) (h7 : v7 < 2^64) :
    (v0 % 2^52
      + 2^52  * ((v0 / 2^52 + 2^12 * (v1 % 2^52)) % 2^52)
      + 2^104 * ((v1 / 2^40 + 2^24 * (v2 % 2^40)) % 2^52)
      + 2^156 * ((v2 / 2^28 + 2^36 * (v3 % 2^28)) % 2^52)
      + 2^208 * ((v3 / 2^16 + 2^48 * (v4 % 2^16)) % 2^52))
    + 2^260 *
      ((v4 / 2^4 % 2^52)
      + 2^52  * ((v4 / 2^56 + 2^8  * (v5 % 2^56)) % 2^52)
      + 2^104 * ((v5 / 2^44 + 2^20 * (v6 % 2^44)) % 2^52)
      + 2^156 * ((v6 / 2^32 + 2^32 * (v7 % 2^32)) % 2^52)
      + 2^208 * (v7 / 2^20 % 2^52))
    = v0 + 2^64 * v1 + 2^128 * v2 + 2^192 * v3 + 2^256 * v4
      + 2^320 * v5 + 2^384 * v6 + 2^448 * v7 := by
  omega

end ScalarProofs

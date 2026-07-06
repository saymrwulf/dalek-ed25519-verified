# Trusted base

What you must believe for the theorems in this repository to transfer to the
running Rust code. Everything else is machine-checked.

1. **Lean 4 kernel** (v4.30.0-rc2) and its three foundational axioms
   `[propext, Classical.choice, Quot.sound]`. Every certificate is
   `#print axioms`-audited against exactly this list.
2. **mathlib** (prebuilt oleans fetched by `lake exe cache get`).
3. **Charon + Aeneas** (pinned `9dd7f23c` / `bf13c42e`): the translation
   from Rust MIR to the Lean model is assumed faithful. The generated
   `gen/` files are never edited (comments only); proofs are stated ABOUT them.
4. **External-function models** (`gen/*/FunsExternal.lean`): Rust items that
   Aeneas cannot translate (constant-time `subtle` primitives, iterator
   plumbing, formatting) are axiomatized as opaque symbols. The axiom audit
   proves none of these axioms enters the dependency cone of any certificate,
   except where a model is explicitly listed below.
5. **The signature-apex boundary (signature layer only)**: FOUR apex-tier
   certificates — `CurveFieldProofs.verify_accepts_iff` (byte apex:
   accepted iff compress([s]·B − [k]·A) = R byte-for-byte),
   `verify_accepts_iff_point` (half-lift: R is the canonical encoding of
   the recomputed point), `verify_accepts_iff_point_eq` (point equation:
   canonically-encoded Q accepted iff Q equals the recomputed point), and
   `verify_accepts_iff_decompress` (full lift: R decompresses to a valid
   on-curve point that equals the recomputed point) — are each
   `#print axioms`-audited by check.sh Phase 3b against EXACTLY the
   standard three plus this documented set, and the build fails on any
   deviation:
   `ed25519.Signature` (wire-format type), the three SHA-512 wrapper
   oracles `verifying.sha512_new/update/finalize_bytes` (+ the opaque
   `sha2.Sha512` state type), `ed25519.Signature.to_bytes`, and
   `signature.error.Error`/`Error.new` (opaque error type). The hash is an
   oracle with no algebraic properties assumed — the theorems hold for
   whatever bytes it produces; the SHA-512 implementation itself is NOT
   verified. Zero curve, scalar, or backend axioms are in any of the four
   cones. The constructive decompress theorem underneath the full lift
   (`decompress_of_canonical`) carries the standard three axioms ONLY.
6. **Compilation of Rust to machine code** (rustc backend) is out of scope,
   as is side-channel behaviour (timing, speculation). The proofs are about
   functional correctness at the MIR/LLBC level.

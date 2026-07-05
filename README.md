# dalek-ed25519-verified

Formal verification of the ed25519 implementation in **dalek-cryptography/curve25519-dalek (upstream, v5.0.0-rc.1)**, built as a
coherent proof pyramid in Lean 4 via the Charon/Aeneas transpilation pipeline:

```
        ┌──────────────────────────────┐
        │  Signature (EdDSA verify)    │   accepted ⇔ compress([s]B−[k]A) = R
        ├──────────────────────────────┤
        │  Scalar arithmetic mod ℓ     │   Scalar52 ops correct mod ℓ
        ├──────────────────────────────┤
        │  Group law (twisted Edwards) │   point ops = complete addition law
        ├──────────────────────────────┤
        │  Field 𝔽_p, p = 2²⁵⁵ − 19    │   FieldElement51 ops correct mod p
        └──────────────────────────────┘
```

Every layer states its theorems about the **actual Aeneas-transpiled Rust
code** (never about a hand-written re-model), and every claim in the status
table below is backed by a compiled proof plus an axiom audit of the named
certificate. Files that do not compile under `verification/check.sh` are not
in this repository.

## Layer status

| Layer | Certificate | Status | Axioms of certificate |
|-------|-------------|--------|-----------------------|
| Field 𝔽_p          | `fieldImplementation`    | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Group law (Edwards) | `edwardsImplementation`  | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Scalar mod ℓ        | `scalarImplementation` (add ✅ sub ✅ mul ✅) | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Signature (EdDSA)   | `verify_accepts_iff` | ✅ proven (phase 1) | standard three + the button-enforced SHA-512/wire-format boundary — see [The signature apex](#the-signature-apex-phase-1) |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

## The signature apex (phase 1)

The apex certificate `CurveFieldProofs.verify_accepts_iff` is the literal EdDSA
acceptance criterion, proven about the extracted verifier:

> For a signature that parses, the verifier returns `Ok(())` **iff** the
> recomputed compressed point `compress([s]·B − [k]·A)` equals the signature's
> `R`, byte-for-byte — where `k` is whatever scalar the opaque SHA-512 oracle
> produces from `(R, A, msg)`.

The recomputation runs entirely through the **proven** model: the vendored `ed25519-dalek` verify glue is extracted as `gen/CurveSig`, whose
hand-maintained externals import `gen/CurveField` — every curve and scalar call
resolves by fully-qualified name to a **proven** definition. Only SHA-512 (three
stateful wrapper calls) and the wire-format types stay opaque.

`check.sh` has a dedicated audit phase (Phase 3b) that fails the build unless
the apex certificate's axiom cone is **exactly**

`[propext, Classical.choice, Quot.sound]` + `{ed25519.Signature, sha2.Sha512, verifying.sha512_new, verifying.sha512_update, verifying.sha512_finalize_bytes, ed25519.Signature.to_bytes, signature.error.Error, signature.error.Error.new}`

— i.e. the three Lean foundations plus the documented SHA-512/wire-format
boundary. Zero curve, scalar, or backend axioms. The companion certificate
`verify_loop_full` (the 32-byte comparison loop computes array equality)
carries the standard three axioms only.

**Phase 2 (deferred, documented):** lifting the byte-level equation to the
point level (`[s]B − [k]A = decompress R`) additionally needs `compress`
canonicity and a verified `decompress`; it is deliberately out of scope for
this milestone, mirroring the layer-by-layer phase split used below the apex.


## Source

- **Upstream**: [dalek-cryptography/curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek), commit `4cf8db2`
- **Pinned/patched source**: [saymrwulf/curve25519-dalek-source](https://github.com/saymrwulf/curve25519-dalek-source), commit `135ed70`
- **Patches**: minimal Aeneas-compatibility only (documented in the source repo)
- Verified backend: `backend/serial/u64` (`FieldElement51`, `Scalar52`). SIMD/AVX backends are out of scope (marked opaque).

## Toolchain (pinned)

| Component | Version |
|-----------|---------|
| Aeneas    | `bf13c42e` |
| Charon    | `9dd7f23c` |
| Lean      | `v4.30.0-rc2` |
| OCaml     | `5.3.0` |

## Reproducing

```bash
source ~/aeneas-toolchain/env.sh
cd verification
./extract.sh    # Rust → LLBC → Lean (regenerates gen/)
./check.sh      # compiles EVERY shipped file + axiom-audits EVERY certificate
```

The gen model is ONE merged universe (`gen/CurveField`: field + curve +
scalar + the verify path's reachable code), regenerated in full by
`extract.sh`. The scalar layer keeps its own check button:

```bash
./check-scalar.sh     # compiles the merged gen + all scalar proofs (add, sub,
                      # Montgomery mul, byte-parsing) and kernel-audits the
                      # scalar certificates, incl. the scalarImplementation
                      # aggregate
```


## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md) for the complete list of assumptions
(Lean kernel, mathlib, Charon/Aeneas semantics, external-function models,
and — in the signature layer only — an opaque SHA-512 model).

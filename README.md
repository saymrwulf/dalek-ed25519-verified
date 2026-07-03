# dalek-ed25519-verified

Formal verification of the ed25519 implementation in **dalek-cryptography/curve25519-dalek (upstream, v5.0.0-rc.1)**, built as a
coherent proof pyramid in Lean 4 via the Charon/Aeneas transpilation pipeline:

```
        ┌──────────────────────────────┐
        │  Signature (EdDSA verify)    │   accepted ⇒ [8][S]B = [8]R + [8][k]A
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
| Scalar mod ℓ        | `scalarImplementation` (planned; `L_val` proven)   | 🔨 foundation | denotation + L=ℓ proven; add/sub/mul in progress |
| Signature (EdDSA)   | `verifyEquation` (planned)          | ⏳ planned | — |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

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

The scalar layer has its own pair of buttons:

```bash
./extract-scalar.sh   # regenerates gen/CurveScalar (Scalar52 limb arithmetic)
./check-scalar.sh     # compiles the scalar gen + the proven scalar foundation
```


## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md) for the complete list of assumptions
(Lean kernel, mathlib, Charon/Aeneas semantics, external-function models,
and — in the signature layer only — an opaque SHA-512 model).

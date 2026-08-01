/- ──────────────────────────────────────────────────────────────────────────
   Proofs/Inventory.lean — environment-derived declaration inventory (main chain).

   Audit INFRASTRUCTURE, not corpus. It proves nothing and is imported by
   nothing. It IS a member of check.sh's compile manifest — lines 42-44 of
   PROOFS — so Phase 2b's kernel-side gate reads its `.olean` and an axiom
   declared here is rejected. (An earlier version of this comment claimed the
   drivers were excluded from the manifest. That was false, and the capability
   matrix in the control repo found it on 2026-07-31.)

   Its constants are outside the corpus walk below, and are emitted separately
   by `emitDrivers` as DRV rows: the kernel counted 3058 declarations where the
   inventory accounted for 3022, and those 36 are this machinery. check.sh now
   requires the two walks to account for the kernel's count exactly.

   Covers every module check.sh compiles except any listed as needing a
   separate driver (see Proofs/InventoryBasic.lean if present). Whether
   a split is needed was determined by compiling a probe, per repo.
   ────────────────────────────────────────────────────────────────────────── -/
import Proofs.InventoryCore
import Proofs.Audit
import Proofs.Denote
import Proofs.P25519
import Proofs.ReduceSpec
import Proofs.SubNegSpec
import Proofs.ConstSpecs
import Proofs.AddSpec
import Proofs.MulSpec
import Proofs.SquareSpec
import Proofs.Square2Spec
import Proofs.Field
import Proofs.InvertSpec
import Proofs.FieldMain
import Proofs.FeQ
import Proofs.EdCurve
import Proofs.EdDenote
import Proofs.EdDouble
import Proofs.EdAddProjNiels
import Proofs.EdAddAffNiels
import Proofs.EdConvert
import Proofs.EdMain
import Proofs.DsmTableSpec
import Proofs.DsmStepSpec
import Proofs.DsmLoopSpec
import Proofs.DsmNafLoadSpec
import Proofs.DsmNafMath
import Proofs.DsmNafLoopSpec
import Proofs.DsmNafSpec
import Proofs.DsmMulSpec
import Proofs.ToBytesMath
import Proofs.ToBytesSpec
import Proofs.CompressSpec
import Proofs.ScalarPackSpec
import Proofs.SigApexSpec
import Proofs.PointLiftSpec
import Proofs.PointEqSpec
import Proofs.DecompressSpec
import Proofs.FromBytesSpec
import Proofs.DecompressMain
open Lean Ed25519Inventory

/-- Exactly the modules this driver covers. check.sh verifies, in BOTH
    directions, that the union of the two drivers' lists is its PROOFS
    manifest minus the audit infrastructure. -/
def corpus : Array Name :=
  #[`Proofs.Denote, `Proofs.P25519, `Proofs.ReduceSpec, `Proofs.SubNegSpec,
   `Proofs.ConstSpecs, `Proofs.AddSpec, `Proofs.MulSpec,
   `Proofs.SquareSpec, `Proofs.Square2Spec, `Proofs.Field,
   `Proofs.InvertSpec, `Proofs.FieldMain, `Proofs.FeQ, `Proofs.EdCurve,
   `Proofs.EdDenote, `Proofs.EdDouble, `Proofs.EdAddProjNiels,
   `Proofs.EdAddAffNiels, `Proofs.EdConvert, `Proofs.EdMain,
   `Proofs.DsmTableSpec, `Proofs.DsmStepSpec, `Proofs.DsmLoopSpec,
   `Proofs.DsmNafLoadSpec, `Proofs.DsmNafMath, `Proofs.DsmNafLoopSpec,
   `Proofs.DsmNafSpec, `Proofs.DsmMulSpec, `Proofs.ToBytesMath,
   `Proofs.ToBytesSpec, `Proofs.CompressSpec, `Proofs.ScalarPackSpec,
   `Proofs.SigApexSpec, `Proofs.PointLiftSpec, `Proofs.PointEqSpec,
   `Proofs.DecompressSpec, `Proofs.FromBytesSpec, `Proofs.DecompressMain]

/-- The instruments. `Proofs.Audit` is the statement-binding driver: it is a
    member of check.sh's compile manifest and it was enumerated by NOTHING —
    26 of the 39 declarations the accounting identity found missing were its.
    `Proofs.InventoryBasic` is reachable by module index only
    if this driver imports it; it does not, so it emits its own DRV rows under
    its own run and check.sh sums the two. This module has no index while it is
    being elaborated, so `emitDrivers` picks its declarations up as the ones the
    environment reports with no originating module. -/
def drivers : Array Name := #[`Proofs.InventoryCore, `Proofs.Audit]

#eval show MetaM Unit from emitInventory corpus
#eval show MetaM Unit from emitDrivers drivers

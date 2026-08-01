/- ──────────────────────────────────────────────────────────────────────────
   Proofs/InventoryBasic.lean — environment-derived declaration inventory (Proofs.Basic only).

   Audit INFRASTRUCTURE, not corpus: excluded from check.sh's compile manifest
   and from its own inventory (its constants live in modules the corpus list
   below does not name). It proves nothing and is imported by nothing.

   Proofs.Basic is compiled by check.sh but imported by no other module,
   and deliberately reuses `CurveFieldProofs.zero_spec`, which
   Proofs.ConstSpecs also declares. Importing both at once is an
   elaboration error, so Basic is inventoried separately and check.sh
   concatenates the two outputs before gating.
   ────────────────────────────────────────────────────────────────────────── -/
import Proofs.InventoryCore
import Proofs.Basic
open Lean Ed25519Inventory

/-- Exactly the modules this driver covers. check.sh verifies, in BOTH
    directions, that the union of the two drivers' lists is its PROOFS
    manifest minus the audit infrastructure. -/
def corpus : Array Name :=
  #[`Proofs.Basic]

#eval show MetaM Unit from emitInventory corpus

-- This driver accounts for ITS OWN declarations only. `Proofs.InventoryCore`
-- is shared machinery and is accounted by `Proofs/Inventory.lean`; counting it
-- here as well would make the two walks overlap and the kernel-count identity
-- in check.sh Phase 2c would fail — correctly, since a declaration would then
-- be accounted twice.
#eval show MetaM Unit from emitDrivers #[]

import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor

/-! # Air-gap file drop conventions (`inbox/` and `outbox/`)

In v1, Tricorder reads requests from `<dataDir>/inbox/` and writes exported keys and signed results to
`<dataDir>/outbox/` (also rendered directly as QR codes on the LCARS screen):
- `inbox/descriptor.txt` — Taproot or SegWit v0 descriptor to register
- `inbox/psbt.b64` / `inbox/psbt.psbt` — PSBT for Override Key review & signing
- `inbox/approve.b64` / `inbox/approve.psbt` — PSBT for Silo Approver (`silo/approve`) review & signing
- `outbox/keys.txt` — Override key expression + Approver x-only pubkey + fingerprint
- `outbox/signed.psbt.b64` — Signed Base64 PSBT
- `outbox/approval.txt` — `approval <64-byte hex sig>` -/

namespace Tricorder.Signer.Protocol

def inboxDir : String := "inbox"
def outboxDir : String := "outbox"
def keysOutFile : String := "outbox/keys.txt"

inductive InboxKind where
  | descriptor
  | overridePsbt
  | approvePsbt
  deriving BEq, DecidableEq, Repr, Inhabited

structure InboxEntry where
  fileName : String
  relPath : String
  kind : InboxKind
  deriving BEq, Repr, Inhabited

def classifyInboxFile (name : String) : Option InboxEntry :=
  let low := name.toLower
  if low.endsWith ".desc" || low.startsWith "descriptor" then
    some { fileName := name, relPath := s!"{inboxDir}/{name}", kind := .descriptor }
  else if low.startsWith "approve" then
    some { fileName := name, relPath := s!"{inboxDir}/{name}", kind := .approvePsbt }
  else if low.endsWith ".psbt" || low.endsWith ".b64" || low.startsWith "psbt" then
    some { fileName := name, relPath := s!"{inboxDir}/{name}", kind := .overridePsbt }
  else none

def formatKeysExport (i : Identity) (wallet? : Option RegisteredWallet) : String :=
  let base :=
    s!"fingerprint {i.fingerprintHex}\n" ++
    s!"override_key {i.overrideKeyExpression}\n" ++
    s!"approver_key {i.approverPubKeyHex}\n"
  match wallet? with
  | none => base
  | some w => base ++ s!"wallet_kind {w.kindLabel}\nfirst_address {w.firstAddress}\ndescriptor {w.descriptor}\n"

end Tricorder.Signer.Protocol

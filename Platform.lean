import Runtime.Big
import Runtime.Utf8

/-! # Tricorder platform interface

The narrow set of capabilities Tricorder asks of the OS underneath:
- entropy (`random`, from Linux `getrandom` / macOS `getentropy`);
- console / diagnostic output (`write`, `log`);
- private file storage scoped strictly inside the app's data directory (`readFile?`, `writeFile`, `deleteFile`,
  `listFiles`), rejecting traversal paths in C as defense-in-depth.

Nothing here touches the network or Java. -/

namespace Platform

/-- Writes bytes to stdout (hosted) or logcat (Android). -/
@[extern "silo_plat_write"]
opaque write (bytes : @& ByteArray) : IO Unit

/-- `count` cryptographically random bytes from the OS CSPRNG. Fails closed if unavailable. -/
@[extern "silo_plat_random"]
opaque random (count : USize) : IO ByteArray

/-- Diagnostic log line (stderr on host, Android logcat on Pixel). -/
@[extern "tricorder_plat_log"]
opaque log (msg : @& String) : IO Unit

/-- Reads a file relative to the app's private data directory; returns `none` if absent. -/
@[extern "tricorder_plat_read_file"]
opaque readFile? (relPath : @& String) : IO (Option ByteArray)

/-- Atomically writes `bytes` to a file relative to the app's private data directory. -/
@[extern "tricorder_plat_write_file"]
opaque writeFile (relPath : @& String) (bytes : @& ByteArray) : IO Unit

/-- Overwrites a file with zeros and unlinks it (no-op if absent). -/
@[extern "tricorder_plat_delete_file"]
opaque deleteFile (relPath : @& String) : IO Unit

/-- Lists regular filenames inside a subdirectory relative to the app's private data directory. -/
@[extern "tricorder_plat_list_files"]
opaque listFiles (relDir : @& String) : IO (Array String)

end Platform

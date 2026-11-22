import Lake
open Lake DSL

/-! silo-signer: the override key of a silo wallet, as the whole software of a Pixel 9 Pro XL (`komodo`) and
under QEMU. "Tricorder" is its working name in the code. -/

package tricorder

/-- Winnow's verified Lean Bitcoin & crypto libraries (`WinnowCore`, `SecpCt`, `Winnow.Crypto`,
`Winnow.Keys.BIP39Wordlist`), pinned directly to GitHub so fresh clones build cleanly. -/
require winnow from git
  "https://github.com/winnowwallet/winnow-lean.git" @ "v0.9.27" / "Lean"

/-- Proved parts of the minimal runtime written in Lean (`Big`, `Utf8`). -/
@[default_target]
lean_lib Runtime

/-- Formal proofs for `Runtime/` and `Mini/`. -/
@[default_target]
lean_lib Proofs

/-- Small verified language for low-level runtime programs (`Alloc`, `Free`, `Number`, `Array`, `String`, `Secret`). -/
@[default_target]
lean_lib Mini

/-- Prints the C files for `Mini/` programs when building the minimal runtime. -/
@[default_target]
lean_exe «mini-print» where
  root := `MiniPrint

lean_lib MiniStringTest

@[default_target]
lean_exe «mini-test» where
  root := `MiniTest

@[default_target]
lean_exe «mini-fuzz» where
  root := `MiniFuzz

/-- Platform interface (`random`, `write`, `log`, private file I/O). -/
@[default_target]
lean_lib Platform

target platformHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "platform.c")
  buildO (pkg.buildDir / "rt" / "platform_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

target hwHosted pkg : System.FilePath := do
  let src ← inputTextFile (pkg.dir / "rt" / "hosted" / "hw.c")
  buildO (pkg.buildDir / "rt" / "hw_hosted.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

/-- Constant-time byte compare and word select over `Mini/Secret.lean`. -/
@[default_target]
lean_lib Secret

target secretHosted pkg : System.FilePath := do
  let some printer ← findLeanExe? `«mini-print» | error "no mini-print"
  let printed ← (← printer.fetch).mapM fun exe => do
    let c := pkg.buildDir / "printed" / "secret.c"
    IO.FS.createDirAll (pkg.buildDir / "printed")
    IO.FS.writeFile c (← captureProc { cmd := exe.toString, args := #["secret"] })
    return c
  buildO (pkg.buildDir / "printed" / "secret.o") printed
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-fPIC"] "cc"

@[default_target]
lean_lib SelfTest

@[default_target]
lean_exe «rt-test» where
  root := `RtTest
  moreLinkObjs := #[platformHosted, secretHosted]

@[default_target]
lean_lib BigTest

@[default_target]
lean_exe «big-test» where
  root := `BigTestMain
  moreLinkObjs := #[platformHosted]

/-- Formally verified bare-metal AArch64 kernel subsystems & drivers (`Mmu`, `Fdt`, `Rng`, `VaultStore`,
`Wire`, `Fb`, `GpioKeys`, QEMU & Pixel `komodo` hardware). -/
@[default_target]
lean_lib Kernel

@[default_target]
lean_lib Tricorder

/-- A payment the tests review and sign. -/
lean_lib TestsFixture where
  roots := #[`Tests.Fixture]

/-- Proof gate checked at build time (never imported by the runtime binary). -/
@[default_target]
lean_lib TricorderGate where
  roots := #[`Tricorder.Gate]

@[default_target]
lean_exe «signer-test» where
  root := `Tests.SignerTest
  moreLinkObjs := #[platformHosted, secretHosted]

@[default_target]
lean_exe «journey-test» where
  root := `Tests.JourneyTest
  moreLinkObjs := #[platformHosted, secretHosted]

@[default_target]
lean_exe «regtest-cli» where
  root := `Tests.RegtestCli
  moreLinkObjs := #[platformHosted, secretHosted]

/-- Anchor target for `scripts/build-bare probe` (exact C closure of bare-metal AArch64 probe). -/
@[default_target]
lean_exe «tricorder-probe» where
  root := `Tricorder.ProbeMain
  moreLinkObjs := #[platformHosted, hwHosted, secretHosted]

/-- Anchor target for `scripts/build-bare os` (exact C closure of full bare-metal AArch64 Tricorder OS). -/
@[default_target]
lean_exe «tricorder-os» where
  root := `Tricorder.OsMain
  moreLinkObjs := #[platformHosted, hwHosted, secretHosted]

/-- Pure-Lean ELF->ARM64 Image flattener, AOSP boot_img_hdr_v4 packager, and AVB2 RSA-4096 signer/verifier. -/
@[default_target]
lean_lib MkBoot

@[default_target]
lean_exe mkboot where
  root := `MkBoot.Main

@[default_target]
lean_exe «boot-img-test» where
  root := `Tests.BootImgTest
  moreLinkObjs := #[platformHosted, hwHosted]

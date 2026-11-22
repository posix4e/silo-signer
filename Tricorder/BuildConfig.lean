import Tricorder.Network

/-! Build-time network selection (`scripts/build-bare` sets this for `regtest`, `signet`, or `mainnet`). -/

namespace Tricorder.BuildConfig

def activeNetwork : Network := .signet

end Tricorder.BuildConfig

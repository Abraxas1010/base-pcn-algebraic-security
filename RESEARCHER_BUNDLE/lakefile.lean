import Lake
open Lake DSL

package «HeytingLean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib «HeytingLean» where
  globs := #[.submodules `HeytingLean]

lean_exe base_pcn_demo where
  root := `HeytingLean.CLI.PaymentChannelsDemo

lean_exe base_pcn_evm_demo where
  root := `HeytingLean.CLI.PaymentChannelsEVMDemo

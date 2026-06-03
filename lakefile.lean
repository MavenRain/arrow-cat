import Lake
open Lake DSL

package «arrow-cat» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «ArrowCat» where
  roots := #[`ArrowCat]

require «kan-tactics» from git
  "https://github.com/MavenRain/kan-tactics.git" @ "main"

import Lake
open Lake DSL
package sixthmoment where
  moreLeanArgs := #["-j1", "-M0", "-DwarningAsError=true"]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"
@[default_target]
lean_lib SixthMoment where
  globs := #[.one `SixthMoment, .submodules `SixthMoment]

@[default_target]
lean_lib Salt where
  weakLeanArgs := #["-Dlinter.style.haveILetI=false"]
  roots := #[`Salt]
  globs := #[.submodules `Salt]

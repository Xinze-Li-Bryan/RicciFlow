import Lake
open Lake DSL

package «ricciflow» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

-- 新的顶层库 Poincare（庞加莱猜想形式化的最终目标）
@[default_target]
lean_lib «Poincare» where
  -- Poincare 层依赖底层的 RicciFlow 模块

-- 原有的 RicciFlow 库（已完成证明，0 sorry）
lean_lib «RicciFlow» where

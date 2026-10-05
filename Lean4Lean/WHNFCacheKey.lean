import Lean.Expr

namespace Lean4Lean
open Lean

/-- Cache only heads whose strict translations cannot already be a dependent
function type. Let bindings and local definitions are normalized directly,
so their forall translations need no witness-dependent cache replay. -/
def whnfCacheKey : Expr → Bool
  | .app .. | .const .. | .lam .. | .proj .. => true
  | _ => false

end Lean4Lean

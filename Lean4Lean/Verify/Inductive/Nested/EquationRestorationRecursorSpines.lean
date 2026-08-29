import Lean4Lean.Verify.Inductive.Nested.EquationRestorationLambdas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/- This module intentionally contains no generic constant-spine theorem.
A checked projection translates to an eliminator application whose
administrative head need not be inherited from its concrete major.  Thus an
arbitrary `ExprRestorationAlignment` does not preserve constant-headed
application spines.  Generated recursive calls are instead reconstructed
from their producer trace at the rule-RHS boundary. -/

end VerifyInductive
end Lean4Lean

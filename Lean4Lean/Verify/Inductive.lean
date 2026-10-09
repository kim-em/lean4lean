import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expression
import Lean4Lean.Verify.Inductive.Nested.Restoration.ParameterOpening
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment
import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Rules.RuleSyntax
import Lean4Lean.Verify.Inductive.Primitive.Shape
import Lean4Lean.Verify.Inductive.Primitive.Constants
import Lean4Lean.Verify.Inductive.Header.Telescope
import Lean4Lean.Verify.Inductive.TypeAnnotations
import Lean4Lean.Verify.Inductive.Prelude.EqReady
import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Primitive.Context
import Lean4Lean.Verify.Inductive.Primitive.Run
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Primitive.Extension
import Lean4Lean.Verify.Inductive.Prelude.Eq
import Lean4Lean.Verify.Inductive.Dispatch
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-!
# Verification of inductive declarations

Collects the verification of the executable inductive checker (`Lean4Lean/Verify/Inductive/`):
headers, constructors, checked formation, recursors and rules, block installation, primitive
families and nested declarations (section 3 of the design notes). The dispatch
theorems that use them are in `Lean4Lean/Verify/Environment.lean`.
-/

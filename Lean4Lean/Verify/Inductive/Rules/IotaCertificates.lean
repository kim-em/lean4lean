import Lean4Lean.Verify.Inductive.Constructor.Normalization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Semantic image of one higher-order recursive result emitted by
`mkRecRules.loopU`.  This is deliberately independent of the executable
syntax: the generator-facing proof only has to show that translating one
`GeneratedRecursiveCall` produces this shape. -/
structure IotaRecursiveResultCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (_recursiveArg result : VExpr) where
  domains : List VExpr
  recursor : Name
  levels : List VLevel
  init : List VExpr
  major : VExpr
  result_eq : result = (VExpr.wrapLams domains <|
    VExpr.mkApps (.const recursor levels) (init ++ [major]))
  domains_recursor_free : ∀ dom ∈ domains,
    dom.SourceConstFree recursors
  recursor_mem : recursor ∈ recursors
  arguments_guarded : ∀ arg ∈ init ++ [major],
    arg.GuardedIota recursors fieldVars domains.length
  major_is_field : major.IsFieldApp fieldVars domains.length

theorem IotaRecursiveResultCertificate.guarded
    (H : IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) :
    result.GuardedIota recursors fieldVars 0 := by
  rw [H.result_eq]
  exact VExpr.GuardedIota.recCallWrapped H.domains_recursor_free
    H.recursor_mem (by simpa using H.arguments_guarded)
      (by simpa using H.major_is_field)

/-- Pointwise alignment of selected recursive constructor arguments with the
translated recursive results supplied to the minor premise. -/
structure IotaRecursiveResultsCertificate
    (recursors : List Name) (fieldVars : List Nat)
    (recursiveArgs recursiveResults : List VExpr) : Prop where
  aligned : List.Forall₂ (fun major result =>
    Nonempty (IotaRecursiveResultCertificate
      recursors fieldVars major result)) recursiveArgs recursiveResults

theorem IotaRecursiveResultsCertificate.length
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    recursiveResults.length = recursiveArgs.length := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem IotaRecursiveResultsCertificate.results_guarded
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults) :
    ∀ result ∈ recursiveResults,
      result.GuardedIota recursors fieldVars 0 := by
  rcases H with ⟨aligned⟩
  induction aligned with
  | nil => simp
  | cons hhead _ ih =>
    intro result hresult
    simp only [List.mem_cons] at hresult
    rcases hresult with rfl | htail
    · rcases hhead with ⟨cert⟩
      exact cert.guarded
    · exact ih result htail

/-- Once ordinary constructor arguments are recursor-free, the aligned
recursive-result certificate discharges guardedness of the complete minor
application used on an iota right-hand side. -/
theorem IotaRecursiveResultsCertificate.minorRhs
    (H : IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults)
    (hfields : ∀ arg ∈ fieldArgs,
      arg.SourceConstFree recursors) :
    (VExpr.mkApps (.bvar minorVar)
      (fieldArgs ++ recursiveResults)).GuardedIota
        recursors fieldVars 0 := by
  apply VExpr.GuardedIota.minorRhs
  · intro arg harg
    exact VExpr.SourceConstFree.guardedIota (hfields arg harg)
  · exact H.results_guarded

/-- Complete right-hand-side fragment of an iota rule. The executable minor
application is represented once; its spine, field/result split, cardinality,
and guardedness are derived below. -/
structure IotaRhsCertificate
    (recursors : List Name) (domains fieldArgs recursiveArgs : List VExpr)
    (rhsBody : VExpr) where
  minorVar : Nat
  minor_in_scope : minorVar < domains.length
  recursiveResults : List VExpr
  rhs_eq : rhsBody = VExpr.mkApps (.bvar minorVar)
    (fieldArgs ++ recursiveResults)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    recursiveArgs.filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  fields_recursor_free : ∀ arg ∈ fieldArgs,
    arg.SourceConstFree recursors
  recursive_results : IotaRecursiveResultsCertificate
    recursors fieldVars recursiveArgs recursiveResults

theorem IotaRhsCertificate.rhs_spine
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.getAppFnArgs =
      (.bvar H.minorVar, fieldArgs ++ H.recursiveResults) := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.getAppFnArgs =
    (.bvar minorVar, fieldArgs ++ results)
  rw [hrhs]
  exact VExpr.getAppFnArgs_mkApps_bvar _ _

theorem IotaRhsCertificate.results_length
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    ((fieldArgs ++ H.recursiveResults).drop fieldArgs.length).length =
      recursiveArgs.length := by
  simpa using H.recursive_results.length

theorem IotaRhsCertificate.guarded
    (H : IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) :
    rhsBody.GuardedIota recursors H.fieldVars 0 := by
  rcases H with ⟨minorVar, hminor, results, hrhs, fieldVars,
    hfieldVars, hfieldsScope, hfieldsFree, hresults⟩
  change rhsBody.GuardedIota recursors fieldVars 0
  rw [hrhs]
  exact hresults.minorRhs hfieldsFree

namespace mkRecInfos.loopCtorArgs.loop

end mkRecInfos.loopCtorArgs.loop

namespace mkRecRules.loopCtors

end mkRecRules.loopCtors

/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursiveFieldDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env decl.uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursiveFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursiveFieldDomain env decl) → Prop
  | nil : RecursiveFieldSelections env decl #[] #[] []
  | nonrecursive : RecursiveFieldSelections env decl bu u fields →
      RecursiveFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursiveFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursiveFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursiveFieldSelections.selectedSublist
    (H : RecursiveFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]

/-- The complete recursive-field fragment of `VInductDecl.IotaRule`, isolated
from the surrounding lhs/rhs telescope bookkeeping. -/
structure IotaFieldCertificate (env : VEnv) (decl : VInductDecl)
    (ctorArgs : List VExpr) (fields : List (decl.RecursiveField env))
    (recursiveArgs : List VExpr) where
  fieldPositions : List Nat
  fieldPositions_eq : fieldPositions = fields.map (fun field => field.fieldIndex)
  fieldPositions_ordered : fieldPositions.Pairwise (· < ·)
  fields_at_positions : ∀ field ∈ fields,
    ∃ h : field.fieldIndex < ctorArgs.length,
      field.arg = ctorArgs[field.fieldIndex]'h
  recursiveArgs_eq : recursiveArgs = fields.map (fun field => field.arg)
  recursive_args : recursiveArgs.Sublist ctorArgs

/-- Non-recursive equation shape shared by generated iota rules. Recursive
field selection and RHS guardedness are supplied by separate certificates. -/
structure IotaEquationCertificate
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)

/-- Assemble the independent iota judgment from its three reviewable pieces:
equation shape, recursive-field selection, and guarded RHS construction. -/
def VInductDecl.IotaRule.ofCertificates
    (Hshape : IotaEquationCertificate decl block owner ctor rule)
    (Hfields : IotaFieldCertificate env decl
      (Hshape.ctorArgs.drop decl.nparams) fields recursiveArgs)
    (Hrhs : IotaRhsCertificate (block.recursors.map (·.name))
      Hshape.domains (Hshape.ctorArgs.drop decl.nparams)
      recursiveArgs Hshape.rhsBody) :
    decl.IotaRule env block owner ctor rule where
  recursor := Hshape.recursor
  recursor_mem := Hshape.recursor_mem
  recursor_name := Hshape.recursor_name
  rule_uvars := Hshape.rule_uvars
  domains := Hshape.domains
  lhsBody := Hshape.lhsBody
  rhsBody := Hshape.rhsBody
  typeBody := Hshape.typeBody
  lhs_wrapped := Hshape.lhs_wrapped
  rhs_wrapped := Hshape.rhs_wrapped
  type_wrapped := Hshape.type_wrapped
  recursorLevels := Hshape.recursorLevels
  leadingArgs := Hshape.leadingArgs
  ctorLevels := Hshape.ctorLevels
  ctorArgs := Hshape.ctorArgs
  lhs_pattern := Hshape.lhs_pattern
  recursor_levels := Hshape.recursor_levels
  ctor_levels := Hshape.ctor_levels
  leading_arity := Hshape.leading_arity
  constructor_arity := Hshape.constructor_arity
  parameter_args := Hshape.parameter_args
  domains_arity := Hshape.domains_arity
  recursiveFields := fields
  fieldPositions := Hfields.fieldPositions
  fieldPositions_eq := Hfields.fieldPositions_eq
  fieldPositions_ordered := Hfields.fieldPositions_ordered
  fields_at_positions := Hfields.fields_at_positions
  recursiveArgs := recursiveArgs
  recursiveArgs_eq := Hfields.recursiveArgs_eq
  recursive_args := Hfields.recursive_args
  fieldVars := Hrhs.fieldVars
  fieldVars_eq := Hrhs.fieldVars_eq
  fields_in_scope := Hrhs.fields_in_scope
  minorVar := Hrhs.minorVar
  minor_in_scope := Hrhs.minor_in_scope
  rhsArgs := Hshape.ctorArgs.drop decl.nparams ++ Hrhs.recursiveResults
  rhs_spine := Hrhs.rhs_spine
  field_args := by
    simpa using Hrhs.field_args
  recursive_results := by
    simpa using Hrhs.results_length
  rhs_guarded := Hrhs.guarded

/-- Exact concrete common-parameter prefix consumed by recursor generation.
The relation is intentionally separate from field classification: agreement
of these substitutions with the abstract parameter telescope is established
during constructor checking. -/
inductive ParameterPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → ParameterPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      ParameterPrefix stats (i + 1) (body.instantiate1 param) tail →
      ParameterPrefix stats i (.forallE name dom body bi) tail

/-- Replaying the cached parameter prefix is deterministic. -/
theorem ParameterPrefix.tail_eq
    (Hleft : ParameterPrefix stats i source left)
    (Hright : ParameterPrefix stats i source right) : left = right := by
  induction Hleft with
  | done hi =>
    cases Hright with
    | done => rfl
    | step hparam _ =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
  | @step i param body left dom name bi hparam Hleft ih =>
    cases Hright with
    | done hi =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
    | step hparam' Hright =>
      have heq : param = _ := Option.some.inj (hparam.symm.trans hparam')
      subst_vars
      exact ih Hright

/-- A pure forall spine of the cached-parameter tail extends to the closed
constructor type: the consumed parameters are free variables, which cannot
alter the binder structure. -/
theorem ParameterPrefix.forallSpine
    (H : ParameterPrefix stats i source tail)
    (hfv : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv)
    (hspine : Expr.ForallSpine tail k) :
    Expr.ForallSpine source (stats.params.size - i + k) := by
  induction H with
  | done hi =>
    subst hi
    simpa using hspine
  | @step i param body tail name dom bi hparam _ ih =>
    have hi : i < stats.params.size :=
      (Array.getElem?_eq_some_iff.mp hparam).1
    rcases hfv param (Array.mem_of_getElem? hparam) with ⟨fv, rfl⟩
    have hbody := ih hspine
    rw [Expr.instantiate1_eq] at hbody
    have hbody' := Expr.ForallSpine.of_instantiate1'_fvar hbody
    have heq : stats.params.size - i + k =
        stats.params.size - (i + 1) + k + 1 := by omega
    rw [heq]
    exact .step hbody'

/-- A partially consumed common-parameter prefix.  Constructor checking
builds this left-to-right; when `stop = stats.params.size`, it is exactly the
complete prefix replay required by recursor generation. -/
inductive ParameterSegment (stats : AddInductive.InductiveStats) :
    Nat → Nat → Expr → Expr → Prop
  | done : ParameterSegment stats i i source source
  | step {i stop : Nat} {param body tail dom : Expr}
      {name : Name} {bi : BinderInfo} :
      stats.params[i]? = some param →
      ParameterSegment stats (i + 1) stop
        (body.instantiate1 param) tail →
      ParameterSegment stats i stop (.forallE name dom body bi) tail

theorem ParameterSegment.trans
    (H₁ : ParameterSegment stats start middle source current)
    (H₂ : ParameterSegment stats middle stop current tail) :
    ParameterSegment stats start stop source tail := by
  induction H₁ with
  | done => exact H₂
  | step hparam _ ih => exact .step hparam (ih H₂)

theorem ParameterSegment.push
    {body param dom : Expr} {name : Name} {bi : BinderInfo}
    (H : ParameterSegment stats start i source
      (.forallE name dom body bi))
    (hparam : stats.params[i]? = some param) :
    ParameterSegment stats start (i + 1) source
      (body.instantiate1 param) := by
  exact H.trans (.step hparam .done)

theorem ParameterSegment.complete
    (H : ParameterSegment stats start stop source tail)
    (hstop : stop = stats.params.size) :
    ParameterPrefix stats start source tail := by
  induction H with
  | done => exact .done hstop
  | step hparam _ ih => exact .step hparam (ih hstop)

namespace mkRecInfos.loopCtorArgs.loop

/-- `loopCtorArgs.loop` follows a certified common-parameter prefix without
changing either accumulator, then delegates to the supplied tail proof. Fuel
exhaustion is harmless because it cannot return successfully. -/
theorem followsParamPrefix {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t tail : Expr} {i : Nat} {bu u : Array Expr}
    {c : AddInductive.Context} {Q : α → Prop}
    (hprefix : ParameterPrefix stats i t tail)
    (Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size bu u fuel c).WF Q) :
    ∀ fuel, (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  intro fuel
  induction fuel generalizing t i with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases hprefix with
    | done hi =>
      subst i
      exact Htail (fuel + 1)
    | @step i param body tail name dom bi hparam hprefix =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop, hparam]
      exact ih hprefix

end mkRecInfos.loopCtorArgs.loop

namespace mkRecInfos.loopArgs1

end mkRecInfos.loopArgs1

/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopInd1

end mkRecInfos.loopInd1

namespace mkRecInfos.loopU

end mkRecInfos.loopU

namespace mkRecInfos.loopUTemplates

end mkRecInfos.loopUTemplates

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[], ruleTemplates := #[] } =
    { b with minors := #[], ruleTemplates := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

end mkRecInfos.loopInd2

end VerifyInductive
end Lean4Lean

import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Declaration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value! ci'.value

/-- Translation of a source constant before the kernel has assigned it a
`ConstantInfo` variant. This is used for inductive headers and constructors,
whose types are translated at different environment stages. -/
structure TrSourceConst (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type
  wf : ci'.toVConstant.WF env

structure TrInductiveType (env envTypes : VEnv) (lparams : List Name)
    (type : InductiveType) (type' : VInductiveType) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' => TrSourceConst envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

/-- Translation of the original, pre-lowering inductive declaration. The
constructor relation deliberately uses `envTypes`, obtained by installing all
translated mutual headers, so an ill-typed nested parameter cannot disappear
behind auxiliary declarations. -/
def TrInductDecl (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧
  decl.uvars = lparams.length ∧
  decl.nparams = nparams ∧
  decl.isUnsafe = isUnsafe ∧
  ∃ envTypes envCtors,
    env.addConsts decl.typeConstants = some envTypes ∧
    envTypes.addConsts decl.constructorConstants = some envCtors ∧
    List.Forall₂ (TrInductiveType env envTypes lparams) types decl.types

theorem TrInductDecl.sourceWF
    (H : TrInductDecl env lparams nparams types isUnsafe decl) : decl.SourceWF env :=
  H.1

variable (safety : DefinitionSafety) (env : VEnv) in
def TrThmVal (ci : TheoremVal) (ci' : VDefVal) : Prop :=
  TrConstVal safety env (.thmInfo ci) ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value ci'.value

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H

theorem VInductBlock.install_le
    (H : VInductBlock.install env block = some env') : env ≤ env' := by
  unfold VInductBlock.install at H
  cases htypes : env.addConsts block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConsts block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : envCtors.addConsts block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        exact (VEnv.addConsts_le htypes).trans <|
          (VEnv.addConsts_le hctors).trans <|
            (VEnv.addConsts_le hrecursors).trans VEnv.addDefEqs_le

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

/-- Constructive implementation boundary for an inductive extension. Besides
the independent compilation and installation witnesses, it records the exact
production-map alignment proof that the executable `addInductive` verifier
must eventually construct. The `Eq` clause is the canonicality fact consumed
by quotient initialization. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  | intro (_block : VInductBlock) :
    decl.WF env₁ →
    VInductDecl.CompilesTo env₁ decl _block →
    VInductBlock.WF env₁ _block →
    VInductBlock.install env₁ _block = some env₂ →
    (∀ safety, Aligned safety m₁ env₁ → Aligned safety m₂ env₂) →
    (∀ {name ci}, m₂.find? name = some ci → ci.deltaValue?.isSome →
      m₁.find? name = some ci) →
    (∀ info, m₂.find? ``Eq = some (.inductInfo info) →
      env₂.constants ``Eq = some eqConst) →
    AddInduct m₁ env₁ decl m₂ env₂

theorem AddInduct.toVEnv
    (H : AddInduct m₁ env₁ decl m₂ env₂) : VEnv.AddInduct env₁ decl env₂ :=
  match H with
  | .intro _ hdecl hcompile hblock hinstall _ _ _ =>
    .intro hdecl hcompile hblock hinstall

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  | thm {ci' : VDefVal} :
    TrThmVal safety env ci ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  /-- Opaque bodies do not contribute definitional equalities, so `TrEnv'` retains only
  the checked header. Soundness of the opaque-body checker is not represented here. -/
  | opaque {ci' : VConstVal} :
    TrConstVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.toVConstant.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .axiom h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.toVEnv⟩

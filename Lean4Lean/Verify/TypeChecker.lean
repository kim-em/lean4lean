import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

structure VEnvs where
  venv : DefinitionSafety → VEnv

structure VEnvs.WFCore (env : Environment) (ves : VEnvs) where
  tr : TrEnv safety env (ves.venv safety)
  hasPrimitives : VEnv.HasPrimitives (ves.venv safety)
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  inductivesClosed : VerifyInductive.MutualInductivesClosed env
  constructorOwners : VerifyInductive.ConstructorOwnersPresent env
  constructorParameterAlignment : VerifyInductive.ConstructorParameterAlignment
    safety env (ves.venv safety)
  inductFamiliesInstalled : InductFamiliesInstalled
    safety env.constants (ves.venv safety)
  mono : safety ≤ safety' → ves.venv safety' ≤ ves.venv safety

/-- The unsafe observer sees every kernel inductive, so the persistent
semantic invariant also supplies safety-independent exact constructor
metadata coherence. -/
theorem VEnvs.WFCore.inductiveConstructorsCoherent
    {env : Environment} {ves : VEnvs} (wf : ves.WFCore env) :
    VerifyInductive.InductiveConstructorsCoherent env := by
  intro familyName familyInfo hfamily i hi
  rcases wf.constructorParameterAlignment (safety := .unsafe)
      familyName familyInfo hfamily DefinitionSafety.unsafe_le i hi with ⟨C⟩
  exact ⟨C.toCtorInfoCoherentAt⟩

theorem VEnvs.WFCore.projectionRegistryCoherent
    {env : Environment} {ves : VEnvs} (wf : ves.WFCore env) :
    ProjectionRegistryCoherent safety env.constants (ves.venv safety) :=
  wf.inductFamiliesInstalled.projectionRegistryCoherent

/-- Every visible constructor of `env` carries a telescope certificate at every safety level
(`CtorTelescopes`). This is the environment invariant that makes the non-dependent field walk
of `inferProj` sound (section 5.3 of `docs/inductives/DESIGN.md`). -/
def VEnvs.AllCtorTelescopes (env : Environment) (ves : VEnvs) : Prop :=
  ∀ safety, CtorTelescopes safety env (ves.venv safety)

/-- The well-formedness invariant of the checker's environment model: the core invariant
(`VEnvs.WFCore`) together with the constructor certificates (`VEnvs.AllCtorTelescopes`). Any core-valid
environment without constructors satisfies it (`VEnvs.WF.ofNoCtors`), and every checked
declaration preserves it (`addDecl.WF_of_canonicalEq`). -/
structure VEnvs.WF (env : Environment) (ves : VEnvs) : Prop extends VEnvs.WFCore env ves where
  ctorTelescopes : ves.AllCtorTelescopes env

/-- Certificate preservation from `env, ves` to `env', ves'`: the conclusion every declaration
check provides alongside `VEnvs.WFCore`. -/
def VEnvs.CtorTelescopesPreserved (env env' : Environment) (ves ves' : VEnvs) : Prop :=
  ves.AllCtorTelescopes env → ves'.AllCtorTelescopes env'

/-- An environment without constructors carries the constructor certificates vacuously. -/
theorem VEnvs.AllCtorTelescopes.ofNoCtors {env : Environment} {ves : VEnvs}
    (h : ∀ name ci, env.find? name ≠ some (.ctorInfo ci)) : ves.AllCtorTelescopes env :=
  fun _ name ci hfind _ => absurd hfind (h name ci)

/-- A core-valid environment without constructors satisfies the full invariant. -/
theorem VEnvs.WF.ofNoCtors {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (h : ∀ name ci, env.find? name ≠ some (.ctorInfo ci)) : ves.WF env :=
  ⟨wf, .ofNoCtors h⟩

open private Lean.Kernel.Environment.add from Lean.Environment in
/-- A fresh non-constructor constant needs no certificate. -/
theorem VEnvs.CtorTelescopesPreserved.addNonCtor {env : Environment} {ves ves' : VEnvs} {ci : ConstantInfo}
    (wf : ves.WFCore env) (hn : env.find? ci.name = none)
    (hle : ∀ safety, ves.venv safety ≤ ves'.venv safety)
    (hnot : ∀ info, ci ≠ .ctorInfo info) : VEnvs.CtorTelescopesPreserved env (env.add ci) ves ves' :=
  fun H safety => CtorTelescopes.addNonCtor (H safety) (wf.tr (safety := safety)).map_wf hn
    (hle safety) hnot

/-- Certificate preservation for an inductive installation: every constructor of the output is
a base constructor, or a new constructor of the declaration (with its safety flag) certified in an abstract
environment below the output model at the declaration's safety. Base constructors keep their
certificates by monotonicity; a new one is visible only to observers at most as strict as the
declaration's safety, whose models extend the declaration's. -/
theorem VEnvs.CtorTelescopesPreserved.ofOrigin {env env' : Environment} {ves ves' : VEnvs} {isUnsafe : Bool}
    {venvH : VEnv}
    (hle : ∀ safety, ves.venv safety ≤ ves'.venv safety)
    (hmono : ∀ {safety safety'}, safety ≤ safety' → ves'.venv safety' ≤ ves'.venv safety)
    (hH : venvH ≤ ves'.venv (if isUnsafe then .unsafe else .safe))
    (horigin : ∀ {name ci}, env'.find? name = some (.ctorInfo ci) →
      env.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci)) :
    VEnvs.CtorTelescopesPreserved env env' ves ves' := by
  intro hold safety name ci hfind hvis
  rcases horigin hfind with h | ⟨hu, hc⟩
  · exact (hold safety h hvis).mono (hle safety)
  · have hs : safety ≤ (if isUnsafe then .unsafe else .safe) := by
      simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hu] using hvis
    exact hc.mono (hH.trans (hmono hs))

/-- Assemble a `VEnvs` from a pointwise existential by case analysis on the
three safety levels. -/
theorem VEnvs.ofPointwiseExists {P : DefinitionSafety → VEnv → Prop}
    (H : ∀ sf, ∃ x, P sf x) :
    ∃ x : VEnvs, ∀ sf, P sf (x.venv sf) := by
  have ⟨x1, _⟩ := H .safe; have ⟨x2, _⟩ := H .partial; have ⟨x3, _⟩ := H .unsafe
  exact ⟨⟨fun | .safe => x1 | .partial => x2 | .unsafe => x3⟩, by rintro ⟨⟩ <;> assumption⟩

/-- The type checker's model of `env` at one safety level.  Checking a declaration
only requires the active safety level, together with projection-registry
coherence for every visible singleton family whose constructor is present, and
recursor and quotient coherence. -/
structure VEnvAt (env : Environment) (safety : DefinitionSafety) (venv : VEnv) : Prop where
  tr : TrEnv safety env venv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  projectionRegistry : ProjectionRegistryCoherent safety env.constants venv
  constructorOwners : VerifyInductive.ConstructorOwnersPresent env
  listedConstructors : VerifyInductive.ListedConstructorsCoherent env
  listedPresent : VerifyInductive.ListedConstructorsPresent env

/-- Recursor coherence of a single-level model, derived from its translation. -/
theorem VEnvAt.recursors (wf : VEnvAt env safety venv) :
    RecursorEnvCoherent safety env.constants venv :=
  wf.tr.recursorEnvCoherent

/-- Quotient coherence of a single-level model, derived from its translation. -/
theorem VEnvAt.quot (wf : VEnvAt env safety venv) (hq : env.quotInit = true) :
    QuotEnvCoherent env.constants venv :=
  wf.tr.quotEnvCoherent hq

theorem VEnvs.WFCore.toVEnvAt {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (safety : DefinitionSafety) : VEnvAt env safety (ves.venv safety) where
  tr := wf.tr
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  constructorOwners := wf.constructorOwners
  listedConstructors := wf.inductiveConstructorsCoherent.listed
  listedPresent := wf.inductiveConstructorsCoherent.present
  projectionRegistry := wf.projectionRegistryCoherent

namespace TypeChecker
open Inner

theorem Methods.withFuel.WF : ∀ {n}, (withFuel n).WF
  | 0 =>
    { isDefEqCore _ _ := .throw
      whnfCore _ := .throw
      whnf _ := .throw
      whnfCore_forallE _ := .throw
      whnf_forallE _ := .throw
      inferType _ _ := .throw
      whnfCore_levels _ := .throw
      whnf_levels _ := .throw
      inferType_levels _ _ := .throw
      whnfCore_paramUniform _ := .throw
      whnf_paramUniform _ := .throw
      inferType_paramUniform _ := .throw
      whnfCore_const := .throw
      whnf_forall_eq := .throw }
  | n + 1 =>
    have := withFuel.WF (n := n)
    { isDefEqCore h1 h2 := isDefEqCore'.WF h1 h2 _ this
      whnfCore h1 := (whnfCore'.WF h1 _ this).mono fun _ _ _ h => ⟨h.1, h.2.1⟩
      whnf h1 := (whnf'.WF h1 _ this).mono fun _ _ _ h => ⟨h.1, h.2.1⟩
      whnfCore_forallE h1 := (whnfCore'.WF h1 _ this).mono fun _ _ _ h => h.2.2 _ _ rfl
      whnf_forallE h1 := (whnf'.WF h1 _ this).mono fun _ _ _ h => h.2.2 _ _ rfl
      inferType h1 h2 := inferType'.WF h1 h2 _ this
      whnfCore_levels h1 := whnfCore'.WF_levels h1 _ this
      whnf_levels h1 := whnf'.WF_levels h1 _ this
      inferType_levels h1 h2 := inferType'.WF_levels h1 h2 _ this
      whnfCore_paramUniform h1 := whnfCore'.WF_paramUniform h1 _ this
      whnf_paramUniform h1 := whnf'.WF_paramUniform h1 _ this
      inferType_paramUniform h1 := inferType'.WF_paramUniform h1 _ this
      whnfCore_const := by intro _ _ cp _ _; exact whnfCore'.WF_const (cheapProj := cp) _ this
      whnf_forall_eq := whnf'.WF_forall _ this }

theorem RecM.WF.run {x : RecM α} (H : x.WF c s Q) : (RecM.run x).WF c s Q :=
  H _ Methods.withFuel.WF

def VContext.mkChecking {env : Environment} {venv : VEnv}
    (trenv : CheckingEnv safety env venv) (hasPrimitives : venv.HasPrimitives)
    (safePrimitives : ∀ {n ci}, env.find? n = some ci → Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (projectionRegistry : ProjectionRegistryCoherent safety env.constants venv)
    (recursors : RecursorEnvCoherent safety env.constants venv)
    (quot : env.quotInit = true → QuotEnvCoherent env.constants venv)
    (ctorTelescopes : CtorTelescopes safety env venv)
    (constructorOwners : VerifyInductive.ConstructorOwnersPresent env)
    (listedConstructors : VerifyInductive.ListedConstructorsCoherent env)
    (lparams : List Name := []) (fuel : FuelConfig := {}) : VContext where
  env; safety; lparams; fuel
  venv
  hasPrimitives
  safePrimitives
  trenv
  constructorOwners
  listedConstructors
  projectionRegistry
  recursors
  quot
  ctorTelescopes
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl

def VContext.mkCheckingValid {env : Environment} {venv : VEnv}
    (wf : CheckingEnv.Valid safety env venv)
    (lparams : List Name := []) (fuel : FuelConfig := {}) : VContext :=
  .mkChecking wf.tr wf.hasPrimitives wf.safePrimitives wf.projectionRegistry
    wf.recursors wf.quot wf.ctorTelescopes wf.constructorOwners wf.listedConstructors lparams fuel

def VContext.mkCheckingValidMLC {env : Environment} {venv : VEnv}
    (wf : CheckingEnv.Valid safety env venv)
    (mlctx : MLCtx) (mlctx_wf : mlctx.WF venv lparams)
    (fuel : FuelConfig := {}) : VContext where
  env; safety; lparams; fuel
  venv
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr
  constructorOwners := wf.constructorOwners
  listedConstructors := wf.listedConstructors
  projectionRegistry := wf.projectionRegistry
  recursors := wf.recursors
  quot := wf.quot
  ctorTelescopes := wf.ctorTelescopes
  mlctx
  mlctx_wf
  lctx := mlctx.lctx
  lctx_eq := rfl

def VContext.mk1 {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    (wf : VEnvAt env safety venv) (htels : CtorTelescopes safety env venv) (lparams : List Name := [])
    (fuel : FuelConfig := {}) : VContext where
  env; safety; lparams; fuel; venv
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  trenv := wf.tr.toChecking
  constructorOwners := wf.constructorOwners
  listedConstructors := wf.listedConstructors
  projectionRegistry := wf.projectionRegistry
  recursors := wf.recursors
  quot := wf.quot
  ctorTelescopes := htels
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl

def VContext.mk' {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (htels : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (safety : DefinitionSafety := .safe) (lparams : List Name := [])
    (fuel : FuelConfig := {}) : VContext := .mk1 (wf.toVEnvAt safety) (htels _) lparams fuel

theorem State.WF.empty1 {env : Environment} {safety : DefinitionSafety} {venv : VEnv}
    {wf : VEnvAt env safety venv} {htels : CtorTelescopes safety env venv} {lparams : List Name}
    {fuel : FuelConfig} :
    State.WF (.mk1 wf htels lparams fuel) {} where
  trctx := .nil
  ngen_wf := nofun
  ectx := .empty
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp
  inferTypeI_levels := .empty
  inferTypeC_levels := .empty
  whnfCore_levels := .empty
  whnf_levels := .empty
  whnfCore_paramUniform := .empty
  whnf_paramUniform := .empty
  inferTypeI_paramUniform := .empty

theorem State.WF.emptyChecking {env : Environment} {venv : VEnv}
    {trenv : CheckingEnv safety env venv} {hasPrimitives : venv.HasPrimitives}
    {safePrimitives : ∀ {n ci}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []}
    {projectionRegistry : ProjectionRegistryCoherent safety env.constants venv}
    {recursors : RecursorEnvCoherent safety env.constants venv}
    {quot : env.quotInit = true → QuotEnvCoherent env.constants venv}
    {ctorTelescopes : CtorTelescopes safety env venv}
    {constructorOwners : VerifyInductive.ConstructorOwnersPresent env}
    {listedConstructors : VerifyInductive.ListedConstructorsCoherent env}
    {lparams : List Name} {fuel : FuelConfig} :
    State.WF (.mkChecking trenv hasPrimitives safePrimitives projectionRegistry
      recursors quot ctorTelescopes constructorOwners listedConstructors lparams fuel) {} where
  trctx := .nil
  ngen_wf := nofun
  ectx := .empty
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp
  inferTypeI_levels := .empty
  inferTypeC_levels := .empty
  whnfCore_levels := .empty
  whnf_levels := .empty
  whnfCore_paramUniform := .empty
  whnf_paramUniform := .empty
  inferTypeI_paramUniform := .empty

theorem State.WF.emptyCheckingValidMLC {env : Environment} {venv : VEnv}
    {wf : CheckingEnv.Valid safety env venv}
    {mlctx : MLCtx} {mlctx_wf : mlctx.WF venv lparams}
    {fuel : FuelConfig}
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    State.WF (.mkCheckingValidMLC wf mlctx mlctx_wf fuel) {} where
  trctx := mlctx_wf.tr
  ngen_wf := hfresh
  ectx := .empty
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp
  inferTypeI_levels := .empty
  inferTypeC_levels := .empty
  whnfCore_levels := .empty
  whnf_levels := .empty
  whnfCore_paramUniform := .empty
  whnf_paramUniform := .empty
  inferTypeI_paramUniform := .empty

theorem State.WF.empty {env : Environment} {ves : VEnvs} {wf : ves.WFCore env}
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
    {htels : ∀ safety, CtorTelescopes safety env (ves.venv safety)} :
    State.WF (.mk' wf htels safety lparams fuel) {} := by
  unfold VContext.mk'; exact .empty1

theorem M.WF.run1 {env : Environment} {venv : VEnv} (wf : VEnvAt env safety venv)
    {htels : CtorTelescopes safety env venv}
    {x : M α} {Q} (H : x.WF (.mk1 wf htels lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq; rename_i eq
  let ⟨_, _, _, _, H⟩ := H .empty1 _ _ eq
  exact H

theorem M.WF.runChecking {env : Environment} {venv : VEnv}
    {trenv : CheckingEnv safety env venv} {hasPrimitives : venv.HasPrimitives}
    {safePrimitives : ∀ {n ci}, env.find? n = some ci → Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []}
    {projectionRegistry : ProjectionRegistryCoherent safety env.constants venv}
    {recursors : RecursorEnvCoherent safety env.constants venv}
    {quot : env.quotInit = true → QuotEnvCoherent env.constants venv}
    {ctorTelescopes : CtorTelescopes safety env venv}
    {constructorOwners : VerifyInductive.ConstructorOwnersPresent env}
    {listedConstructors : VerifyInductive.ListedConstructorsCoherent env}
    {x : M α} {Q}
    (H : x.WF (.mkChecking trenv hasPrimitives safePrimitives projectionRegistry
      recursors quot ctorTelescopes constructorOwners listedConstructors lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq
  rename_i eq
  let ⟨_, _, _, _, H⟩ := H .emptyChecking _ _ eq
  exact H

theorem M.WF.runCheckingValid {env : Environment} {venv : VEnv}
    {wf : CheckingEnv.Valid safety env venv}
    {x : M α} {Q}
    (H : x.WF (.mkCheckingValid wf lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q :=
  M.WF.runChecking (trenv := wf.tr) (hasPrimitives := wf.hasPrimitives)
    (safePrimitives := wf.safePrimitives) (projectionRegistry := wf.projectionRegistry)
    (recursors := wf.recursors) (quot := wf.quot) (ctorTelescopes := wf.ctorTelescopes)
    (constructorOwners := wf.constructorOwners)
    (listedConstructors := wf.listedConstructors) H

theorem M.WF.runCheckingValidMLC {env : Environment} {venv : VEnv}
    {wf : CheckingEnv.Valid safety env venv}
    {mlctx : MLCtx} {mlctx_wf : mlctx.WF venv lparams}
    {x : M α} {Q}
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (H : x.WF (.mkCheckingValidMLC wf mlctx mlctx_wf fuel) {} fun a _ => Q a) :
    (M.run env safety mlctx.lctx lparams fuel x).WF Q := by
  intro a eq
  simp [M.run, Functor.map, Except.map] at eq
  split at eq <;> cases eq
  rename_i eq
  let ⟨_, _, _, _, hQ⟩ := H (.emptyCheckingValidMLC hfresh) _ _ eq
  exact hQ

theorem M.WF.run {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    {htels : ∀ safety, CtorTelescopes safety env (ves.venv safety)}
    {x : M α} {Q} (H : x.WF (.mk' wf htels safety lparams fuel) {} fun a _ => Q a) :
    (M.run env safety {} lparams fuel x).WF Q := by
  unfold VContext.mk' at H; exact M.WF.run1 _ H

/-- Loop invariant rule for `for x in xs do ...`. `Inv` is indexed by the list still to be
processed, so the conclusion `Inv []` records that every element was handled. The body must
`yield`; a loop that can `break` is out of scope (none of the kernel's loops do). -/
theorem M.WF.forIn {c : VContext} {f : α → β → M (ForInStep β)}
    {Inv : List α → β → State → Prop}
    (H : ∀ v vs b s, Inv (v :: vs) b s →
      (f v b).WF c s fun r s' => ∃ b', r = .yield b' ∧ Inv vs b' s') :
    ∀ {vs : List α} {b : β} {s : State}, Inv vs b s →
      (forIn vs b f).WF c s fun b' s' => Inv [] b' s'
  | [], _, _, h => .pure h
  | v :: vs, b, s, h => by
    rw [List.forIn_cons]
    refine (H v vs b s h).bind fun r s' _ hr => ?_
    obtain ⟨b', rfl, hinv⟩ := hr
    exact M.WF.forIn H hinv

theorem M.WF.bindThrow {c : VContext} {s : State} {x : M α} {f : α → M β} {Q}
    (h : x.WF c s fun _ _ => False) : (x >>= f).WF c s Q :=
  h.bind fun _ _ _ hf => hf.elim

/-- Loop rule for `addMutual`'s header loop, whose accumulator is the set of names seen so
far: each iteration rejects a name already in the set, so the whole block is duplicate-free. -/
theorem M.WF.forInFresh {c : VContext} {Q : Lean.DefinitionVal → β → Prop}
    {f : Lean.DefinitionVal → NameSet → M (ForInStep NameSet)}
    (H : ∀ v found s, (f v found).WF c s fun r _ =>
      found.contains v.name = false ∧ (∃ b, Q v b) ∧ r = .yield (found.insert v.name)) :
    ∀ {vs : List Lean.DefinitionVal} {found : NameSet} {s : State},
      (ForIn.forIn vs found f).WF c s fun _ _ =>
        (∃ bs, List.Forall₂ Q vs bs) ∧ (vs.map (·.name)).Nodup ∧
          ∀ v ∈ vs, found.contains v.name = false
  | [], _, _ => .pure ⟨⟨[], .nil⟩, by simp, by simp⟩
  | v :: vs, found, s => by
    rw [List.forIn_cons]
    refine (H v found s).bind fun r s' _ h => ?_
    obtain ⟨hfresh, ⟨b, hb⟩, rfl⟩ := h
    refine (M.WF.forInFresh H (vs := vs) (found := found.insert v.name)).mono
      fun _ _ _ h => ?_
    obtain ⟨⟨bs, hbs⟩, hnd, hmem⟩ := h
    refine ⟨⟨b :: bs, .cons hb hbs⟩, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨w, hw, hwn⟩ := List.mem_map.1 hm
      have := hmem w hw
      rw [NameSet.contains_insert, hwn] at this
      simp at this
    · intro w hw
      cases hw with
      | head => exact hfresh
      | tail _ hw =>
        have := hmem w hw
        rw [NameSet.contains_insert] at this
        exact (by simpa using this : _ ∧ _).2

/-- Loop rule for a loop whose elements are already related to a list `cis`, so each iteration
may use the datum paired with the element it processes; each refines its `ci` to a `ci'`
related by `R`. -/
theorem M.WF.forInForall₂ {c : VContext} {f : α → Unit → M (ForInStep Unit)}
    {P : α → β → Prop} {R : β → β → Prop} {Q : α → β → Prop}
    (H : ∀ v ci s, P v ci → (f v ()).WF c s fun r _ =>
      (∃ ci', R ci ci' ∧ Q v ci') ∧ r = .yield ()) :
    ∀ {vs : List α} {cis : List β} {s : State}, List.Forall₂ P vs cis →
      (ForIn.forIn vs () f).WF c s fun _ _ =>
        ∃ cis', List.Forall₂ R cis cis' ∧ List.Forall₂ Q vs cis' := by
  intro vs cis s h
  induction h generalizing s with
  | nil => exact .pure ⟨[], .nil, .nil⟩
  | @cons v ci vs cis hd tl ih =>
    rw [List.forIn_cons]
    refine (H v ci s hd).bind fun r s' _ h => ?_
    obtain ⟨⟨ci', hR, hQ⟩, rfl⟩ := h
    refine (ih (s := s')).mono fun _ _ _ h => ?_
    obtain ⟨cis', h1, h2⟩ := h
    exact ⟨ci' :: cis', .cons hR h1, .cons hQ h2⟩

/-- The `FVarsBelow` is kept, not dropped: a caller that reduced a term living in some sub-context
needs to know the result still does, and reduction is the only step where that could fail. -/
nonrec theorem whnf.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := (whnf.WF he).run

nonrec theorem whnfCore.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (whnfCore e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  (whnfCore.WF he).run

/-- The `M`-level wrapper falls back to `e` itself when there is nothing to unfold, so unlike the
`RecM` form it always returns something definitionally equal to its input. -/
nonrec theorem unfoldDefinition.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (unfoldDefinition e) fun e₁ _ => c.TrExpr e₁ e' := by
  refine (unfoldDefinition.WF he).run.bind fun oe _ _ H => ?_
  cases oe with
  | some => exact .pure H.2
  | none => exact .pure (he.trExpr c.Ewf c.Δwf)

/-- In `inferOnly` mode the caller has to supply the translation, since that mode assumes the
term is already known to be well typed. -/
nonrec theorem inferType.WF' {c : VContext} {s : State}
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    M.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  (inferType.WF' h1 hinf).run

nonrec theorem inferType.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (inferType e inferOnly) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' :=
  (inferType.WF he).run

/-- `checkType` is `inferType` at `inferOnly := false`, where the obligation is vacuous. -/
theorem checkType.WF {c : VContext} {s : State} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := inferType.WF' h1 nofun

nonrec theorem isDefEq.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    M.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  (isDefEq.WF he₁ he₂).run

nonrec theorem isProp.WF {c : VContext} {s : State}
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ => b → c.HasType e' (.sort .zero) :=
  (isProp.WF he).run

theorem ensureSort.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (ensureSort e e₀) fun e1 _ => c.TrExpr e1 e' ∧ ∃ u, e1 = .sort u :=
  (ensureSortCore.WF he).run.mono fun _ _ _ h => ⟨h.2.1, h.1⟩

theorem ensureForall.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (ensureForall e) fun e1 _ =>
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  (ensureForallCore.WF he).run.mono fun _ _ _ h => h.2

/-- At `inferOnly := false` the translation is an *output* rather than an input, so this is how a
caller learns that a term it has not otherwise translated is a type -- which is what the primitive
checker's `ensureType` calls are for. -/
theorem ensureType.WF' {c : VContext} {s : State}
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    M.WF c s (ensureType e inferOnly) fun e1 _ => ∃ e', c.TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
      VLevel.ofLevel c.lparams u = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF' h1 hinf).bind fun _ _ _ ⟨_, _, _, a1, a2, a3⟩ => ?_
  refine (ensureSort.WF a2).mono fun _ _ _ ⟨⟨_, b1, b2⟩, b3⟩ => ?_
  obtain ⟨_, rfl⟩ := b3; let .sort b1 := b1
  exact ⟨_, a1, _, _, rfl, b1, a3.defeqU_r c.Ewf c.Δwf b2.symm⟩

theorem ensureType.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    M.WF c s (ensureType e inferOnly) fun e1 _ => ∃ e', c.TrExprS e e' ∧ ∃ u u', e1 = .sort u ∧
      VLevel.ofLevel c.lparams u = some u' ∧ c.HasType e' (.sort u') :=
  ensureType.WF' he.fvarsIn fun _ => ⟨_, he⟩

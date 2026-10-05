import Lean4Lean.Theory.Typing.AnchoredFamilyExposedBinder
import Lean4Lean.Theory.Typing.AnchoredFamilyAssignedSort
import Lean4Lean.Theory.Typing.AnchoredFunctionGradeView

/-! Isolated finite family-spine syntax for rigid-application adequacy.
The frozen function keys may demand arbitrary inputs. Terminal argument
requests need only raw equalities, so their profiles are empty at rank zero.
This prototype does not change the shared observation grammar. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

structure RigidFamilyArgument where
  domain : VExpr
  anchor : VExpr
  deriving DecidableEq

namespace RigidFamilyArgument

def rename (ρ : Lift) (argument : RigidFamilyArgument) : RigidFamilyArgument :=
  ⟨argument.domain.lift' ρ, argument.anchor.lift' ρ⟩

def request (argument : RigidFamilyArgument) : DataRequest (Profile 0) :=
  { domain := argument.domain, anchor := argument.anchor, input := .empty, support := .empty }

@[simp] theorem request_rename (ρ : Lift) (argument : RigidFamilyArgument) :
    (argument.rename ρ).request = argument.request.rename ρ := rfl

end RigidFamilyArgument

/-- Only finite syntax and frozen keys are stored. Self-admission of each key
is a separate finite well-formedness judgment, as for existing fn guards. -/
inductive RigidFamilySpine : Nat → Type where
  | terminal (relevant : Bool) : RigidFamilySpine 1
  | binder (key : Key n) (child : RigidFamilySpine n) : RigidFamilySpine (n+1)
  | pad (child : RigidFamilySpine n) : RigidFamilySpine (n+1)

namespace RigidFamilySpine

def atom (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    RigidFamilySpine n → Atom n
  | .terminal relevant =>
      .family ⟨name, levels, relevant, past.map RigidFamilyArgument.request⟩
  | .binder key child => .fn key (child.atom name levels (past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)]))
  | .pad child => .pad (child.atom name levels past)

def Ready (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (Γ : List VExpr) :
    RigidFamilySpine n → Prop
  | .terminal _ => True
  | .binder key child =>
      Admitted env U registry Γ key key.anchor key.anchor ∧ child.Ready env U registry Γ
  | .pad child => child.Ready env U registry Γ

def rename (ρ : Lift) : RigidFamilySpine n → RigidFamilySpine n
  | .terminal relevant => .terminal relevant
  | .binder key child => .binder (key.rename ρ) (child.rename ρ)
  | .pad child => .pad (child.rename ρ)

theorem atom_rename (plan : RigidFamilySpine n) (ρ : Lift)
    (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    (plan.rename ρ).atom name levels (past.map (RigidFamilyArgument.rename ρ)) =
      (plan.atom name levels past).rename ρ := by
  induction plan generalizing past with
  | terminal relevant =>
    have requests : (past.map (RigidFamilyArgument.rename ρ)).map RigidFamilyArgument.request =
        (past.map RigidFamilyArgument.request).map (DataRequest.map (fun e => e.lift' ρ) (Profile.rename ρ)) := by
      rw [List.map_map, List.map_map]
      apply congrArg (fun f => past.map f)
      funext argument
      rfl
    exact congrArg (fun requests => AtomData.family
      (P := Profile 0) ⟨name, levels, relevant, requests⟩) requests
  | binder key child ih =>
    simp only [rename, atom, Atom.rename_fn]
    congr 1
    have translated := ih (past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)])
    rw [List.map_append] at translated
    exact translated
  | pad child ih => exact congrArg AtomData.pad (ih past)

theorem ready_transport
    (plan : RigidFamilySpine n)
    (ready : plan.Ready env U registry Γ)
    (transport : ∀ {n} {key : Key n},
      Admitted env U registry Γ key key.anchor key.anchor →
      Admitted env U registry Δ (key.rename ρ)
        (key.anchor.lift' ρ) (key.anchor.lift' ρ)) :
    (plan.rename ρ).Ready env U registry Δ := by
  induction plan with
  | terminal => trivial
  | binder key child ih => exact ⟨transport ready.1, ih ready.2⟩
  | pad child ih => exact ih ready

/-- Key guards move along the same concrete mixed insertion as the code
witness, including its terminal context conversion. -/
theorem ready_rename
    (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (plan : RigidFamilySpine n)
    (ready : plan.Ready env U registry Γ) :
    (plan.rename ρ).Ready env U registry Δ :=
  plan.ready_transport ready (route.admitted henv)

/-- Runtime state retains a raw equality for each demanded argument. It does
not assert that the declaration header was a literal telescope. -/
def Arguments (env : VEnv) (U : Nat) (Γ : List VExpr)
    (past : List RigidFamilyArgument) (values : List VExpr) : Prop :=
  List.Forall₂ (fun argument value =>
    env.IsDefEq U Γ argument.anchor value argument.domain) past values

namespace Arguments

theorem transport
    (arguments : Arguments env U Γ past values)
    (move : ∀ {a b A}, env.IsDefEq U Γ a b A →
      env.IsDefEq U Δ (a.lift' ρ) (b.lift' ρ) (A.lift' ρ)) :
    Arguments env U Δ (past.map (RigidFamilyArgument.rename ρ))
      (values.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (move head) ih

theorem rename (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (arguments : Arguments env U Γ past values) :
    Arguments env U Δ (past.map (RigidFamilyArgument.rename ρ))
      (values.map (·.lift' ρ)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (route.eq henv head) ih

theorem left (arguments : Arguments env U Γ past values) :
    Arguments env U Γ past (past.map RigidFamilyArgument.anchor) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.hasType.1 ih

theorem append (arguments : Arguments env U Γ past values)
    (next : env.IsDefEq U Γ argument.anchor value argument.domain) :
    Arguments env U Γ (past ++ [argument]) (values ++ [value]) := by
  induction arguments with
  | nil => exact .cons next .nil
  | cons head tail ih => exact .cons head ih

/-- Empty terminal requests preserve the actual raw argument equalities; no
family or argument semantic answer is stored in the finite plan. -/
theorem requests (arguments : Arguments env U Γ past values) :
    RankedData.Arguments env U (relations env U registry 0) Γ
      (past.map RigidFamilyArgument.request)
      (past.map RigidFamilyArgument.anchor) values := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih =>
    refine .cons ⟨head.hasType.1, head,
      Profile.HasType.empty Profile.WF.empty,
      Profile.HasType.empty (Profile.WF.sort true), ?_, ?_, ?_⟩ ih
    · intro Δ ρ future atom member; cases member
    · intro atom member; cases member
    · intro atom member; cases member

end Arguments

private theorem lift_apps (ρ : Lift) (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a args ih => exact ih (.app fn a)

private theorem apps_append (fn : VExpr) (args : List VExpr) (a : VExpr) :
    mkApps fn (args ++ [a]) = .app (mkApps fn args) a := by
  simp only [mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Full finite binder induction at arbitrary assigned types. The only
semantic inputs are the existing key self-guards, raw prefix/argument state,
and the supplied assigned-code capability. In particular hidden Pi headers
and results that become sorts only after substitution are both admitted. -/
theorem supported
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (plan : RigidFamilySpine n)
    (ready : plan.Ready env U registry Γ)
    (formed : OnCtx Γ (env.IsType U))
    (inert : CanonicalDataHead.HeadInert registry name)
    (arguments : Arguments env U Γ past values)
    (raw : env.IsDefEq U Γ
      (mkApps (.const name levels) (past.map RigidFamilyArgument.anchor))
      (mkApps (.const name levels) values) assigned)
    (typed : (Profile.singleton (plan.atom name levels past)).HasType support)
    (code : TypeRelated env U registry Γ assigned assigned support) :
    Related env U registry Γ
      (mkApps (.const name levels) (past.map RigidFamilyArgument.anchor))
      (mkApps (.const name levels) values) assigned (.singleton (plan.atom name levels past)) support := by
  match n, plan with
  | 1, .terminal relevant =>
    exact Related.familyOfAssigned henv hscoped formed inert raw typed code arguments.requests
  | _+1, .binder key child =>
    apply Related.familyBinderOfAssigned henv hscoped formed typed code ready.1
    intro A B domain result rows member row resultTyped display Δ ρ future z admitted
    let insertion := display.leftExposure.insertion henv
    have hΔ := future.targetWF henv
    have rawPrefix := insertion.eq henv raw
    have exposed := display.leftExposure.sound.cast rawPrefix
    have exposed' := exposed.weak' henv future.weakening
    have rawArgument := admitted.1
    obtain ⟨_, _, _, _, domainPath, _⟩ := display.rowDomains key result row
    have argumentDomain := (domainPath.weak' henv future.weakening).cast (by
      simpa only [Key.rename, lift'_comp] using rawArgument)
    have nextRaw := VEnv.IsDefEq.appDF exposed' argumentDomain
    have nextLeftRaw := VEnv.IsDefEq.appDF exposed'.hasType.1 argumentDomain
    have seed : Admitted env U registry Δ (key.rename (display.map.comp ρ))
        (key.anchor.lift' (display.map.comp ρ))
        (key.anchor.lift' (display.map.comp ρ)) := by
      simpa only [Key.rename_comp, ← lift'_comp] using
        (insertion.admitted henv ready.1).future henv future
    have childCode := (display.rowBodies key result row Δ ρ future
      (key.anchor.lift' (display.map.comp ρ))
      (key.anchor.lift' (display.map.comp ρ)) seed).1
    let renamed := child.rename (display.map.comp ρ)
    have renamedReady := child.ready_transport (Δ := Δ) (ρ := display.map.comp ρ) ready.2 (fun {m k} seed => by
      have moved := (insertion.admitted henv seed).future henv future
      simpa only [Key.rename_comp, ← lift'_comp] using moved)
    have movedArgs := arguments.transport (ρ := display.map.comp ρ) (fun h => by
      simpa only [← lift'_comp] using (insertion.eq henv h).weak' henv future.weakening)
    have nextArgs : Arguments env U Δ
        ((past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)]).map (RigidFamilyArgument.rename (display.map.comp ρ)))
        (values.map (·.lift' (display.map.comp ρ)) ++ [z]) := by
      rw [List.map_append]
      exact movedArgs.append (argument := ⟨key.domain.lift' (display.map.comp ρ),
        key.anchor.lift' (display.map.comp ρ)⟩) rawArgument
    have nextLeftArgs : Arguments env U Δ
        ((past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)]).map (RigidFamilyArgument.rename (display.map.comp ρ)))
        ((past.map RigidFamilyArgument.anchor).map (·.lift' (display.map.comp ρ)) ++ [z]) := by
      rw [List.map_append]
      have result := movedArgs.left.append (argument := ⟨key.domain.lift' (display.map.comp ρ),
        key.anchor.lift' (display.map.comp ρ)⟩) rawArgument
      simpa only [List.map_map, List.map_cons, List.map_nil, Function.comp_def, RigidFamilyArgument.rename] using result
    have nextTyped : (Profile.singleton (renamed.atom name levels
        ((past ++ [(⟨key.domain, key.anchor⟩ : RigidFamilyArgument)]).map (RigidFamilyArgument.rename (display.map.comp ρ))))).HasType
        (Profile.rename (display.map.comp ρ) result) := by
      change (Profile.singleton ((child.rename (display.map.comp ρ)).atom name levels _)).HasType _
      rw [atom_rename]
      exact Profile.rename_hasType_iff.mpr resultTyped
    have pair := renamed.supported henv hscoped renamedReady hΔ inert nextArgs
      (by simpa only [List.map_append, List.map_cons, List.map_nil,
        List.map_map, Function.comp_def, RigidFamilyArgument.rename,
        apps_append, lift_apps, lift', lift'_comp] using nextRaw)
      nextTyped childCode
    have leftPair := renamed.supported henv hscoped renamedReady hΔ inert nextLeftArgs
      (by simpa only [List.map_append, List.map_cons, List.map_nil,
        List.map_map, Function.comp_def, RigidFamilyArgument.rename,
        apps_append, lift_apps, lift', lift'_comp] using nextLeftRaw)
      nextTyped childCode
    simp only [renamed, atom_rename] at pair leftPair
    constructor
    · simpa only [List.map_append, List.map_cons, List.map_nil,
        List.map_map, Function.comp_def, RigidFamilyArgument.rename,
        apps_append, lift_apps, lift', lift'_comp, lift'_inst_hi, atom_rename] using leftPair
    · simpa only [List.map_append, List.map_cons, List.map_nil,
        List.map_map, Function.comp_def, RigidFamilyArgument.rename,
        apps_append, lift_apps, lift', lift'_comp, lift'_inst_hi, atom_rename] using pair
  | _+1, .pad child =>
    change (Profile.singleton (child.atom name levels past)).pad.HasType support at typed
    exact ((child.supported henv hscoped ready formed inert arguments raw
      typed.pad_inv (code.down henv)).pad henv).retag henv typed code
termination_by n

/-- Exact outer padding, matching the rank chosen by the actual application
packer. No function-key commutation or alternate family demand is substituted. -/
def raise (plan : RigidFamilySpine n) : (N : Nat) → n ≤ N → RigidFamilySpine N
  | 0, bound => (show n = 0 by omega) ▸ plan
  | N+1, bound =>
    if equal : n = N+1 then equal ▸ plan
    else .pad (plan.raise N (by omega))

theorem atom_raise (plan : RigidFamilySpine n) (bound : n ≤ N)
    (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    (plan.raise N bound).atom name levels past =
      AnchoredSource.raiseAtom N bound (plan.atom name levels past) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n
      simp [raise, AnchoredSource.raiseAtom_self]
    · have small : n ≤ N := by omega
      simp only [raise, dif_neg equal, atom,
        AnchoredSource.raiseAtom_step small, ih small]

theorem ready_raise (plan : RigidFamilySpine n) (bound : n ≤ N)
    (ready : plan.Ready env U registry Γ) :
    (plan.raise N bound).Ready env U registry Γ := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ready
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n
      simpa [raise] using ready
    · have small : n ≤ N := by omega
      simp only [raise, dif_neg equal, Ready]
      exact ih small

theorem profile_raise (plan : RigidFamilySpine n) (bound : n ≤ N)
    (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    Profile.singleton ((plan.raise N bound).atom name levels past) =
      AnchoredSource.raiseProfile N bound (.singleton (plan.atom name levels past)) := by
  rw [atom_raise, AnchoredSource.raiseProfile_singleton]

end RigidFamilySpine
end Lean4Lean.AnchoredSemantics

import Lean4Lean.Theory.Typing.AnchoredViewInterpretation
import Lean4Lean.Theory.Typing.AnchoredFunctionShift

/-! A finite source-observation core. Required source resources are separate
from an available valuation. Frozen target keys and semantic guards contribute
no source-variable occurrences. Variable leaves retain their original requested demands and grades through
finite views. Binders package those leaves at a chosen common grade.

This file does not assert the fundamental theorem or substitution factoring.
In particular, source type-support views still require their paired producer.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def raiseProfile {n : Nat} : (N : Nat) → n ≤ N → Profile n → Profile N
  | 0, h, p => (show n = 0 by omega) ▸ p
  | N + 1, h, p =>
    if he : n = N + 1 then he ▸ p
    else (raiseProfile N (by omega) p).pad

@[simp] theorem raiseProfile_self (p : Profile n) : raiseProfile n (Nat.le_refl n) p = p := by
  cases n <;> simp [raiseProfile]

theorem raiseProfile_step {n N : Nat} (h : n ≤ N) (p : Profile n) :
    raiseProfile (N + 1) (Nat.le_succ_of_le h) p = (raiseProfile N h p).pad := by
  simp only [raiseProfile, dif_neg (show n ≠ N + 1 by omega)]

theorem raiseProfile_empty {n N : Nat} (h : n ≤ N) :
    raiseProfile N h (Profile.empty (n := n)) = .empty := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; exact raiseProfile_self _
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, ih hn, Profile.pad_empty]

theorem raiseProfile_union {n N : Nat} (h : n ≤ N) (p q : Profile n) :
    raiseProfile N h (p.union q) = (raiseProfile N h p).union (raiseProfile N h q) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simp only [raiseProfile_self]
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, raiseProfile_step hn, raiseProfile_step hn, ih hn, Profile.pad_union]

theorem raiseProfile_pad {n N : Nat} (h : n + 1 ≤ N) (p : Profile n) :
    raiseProfile N h p.pad = raiseProfile N (Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl n)) h) p := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : n = N
    · subst n
      rw [raiseProfile_self, raiseProfile_step (Nat.le_refl N), raiseProfile_self]
    · have hn : n + 1 ≤ N := by omega
      rw [raiseProfile_step hn, raiseProfile_step (show n ≤ N by omega), ih hn]

structure Need where
  rank : Nat
  profile : Profile rank

def Need.rename (ρ : Lift) (need : Need) : Need := ⟨need.rank, need.profile.rename ρ⟩

abbrev Footprint := List (Nat × Need)
abbrev Valuation := Nat → List Need

def Footprint.Available (required : Footprint) (available : Valuation) : Prop :=
  ∀ i need, (i, need) ∈ required → need ∈ available i

def Footprint.shift (required : Footprint) : Footprint :=
  required.map fun (i, need) => (i + 1, need)

def Footprint.rename (ρ : Lift) (required : Footprint) : Footprint :=
  required.map fun (i, need) => (i, need.rename ρ)

/-- The fallback is never used by the normalization theorem: its result
includes the grade bound for every leaf, including empty leaves. -/
def Need.atGrade (N : Nat) (need : Need) : Profile N :=
  if h : need.rank ≤ N then raiseProfile N h need.profile else .empty

def Footprint.atGrade (N : Nat) (footprint : Footprint) : Profile N :=
  footprint.flatMap fun entry => entry.2.atGrade N

theorem Footprint.atGrade_append (N : Nat) (first second : Footprint) :
    (first ++ second).atGrade N = (first.atGrade N).union (second.atGrade N) :=
  List.flatMap_append

theorem Footprint.rename_append (left right : Footprint) :
    Footprint.rename ρ (left ++ right) = Footprint.rename ρ left ++ Footprint.rename ρ right :=
  List.map_append

def Locals.push (locals : List Nat) : List Nat := 0 :: locals.map Nat.succ

theorem raiseProfile_rename {n N : Nat} (h : n ≤ N) (p : Profile n) (ρ : Lift) :
    (raiseProfile N h p).rename ρ = raiseProfile N h (p.rename ρ) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simp only [raiseProfile_self]
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, raiseProfile_step hn, Profile.rename_pad, ih hn]

theorem Need.atGrade_rename (need : Need) (N : Nat) (ρ : Lift) :
    (need.atGrade N).rename ρ = (need.rename ρ).atGrade N := by
  simp only [Need.atGrade, Need.rename]
  split
  · exact raiseProfile_rename _ _ _
  · exact Profile.rename_empty

/-- A binder packages every actual local leaf at its chosen grade. The
bound is retained even for empty leaf demands; external requirements are
unchanged. No transformed demand replaces an original lookup leaf. -/
inductive BinderPack (n : Nat) : Profile n → Footprint → Footprint → Prop where
  | nil : BinderPack n .empty [] []
  | local (need : Need) (bound : need.rank ≤ n)
      (rest : BinderPack n input required external) :
      BinderPack n ((need.atGrade n).union input) ((0, need) :: required) external
  | external (i : Nat) (need : Need) (rest : BinderPack n input required external) :
      BinderPack n input ((i + 1, need) :: required) ((i, need) :: external)

theorem BinderPack.rename {input : Profile n} {required outside : Footprint}
    (h : BinderPack n input required outside) (ρ : Lift) :
    BinderPack n (input.rename ρ) (Footprint.rename ρ required)
      (Footprint.rename ρ outside) := by
  induction h with
  | nil => exact .nil
  | «local» need bound rest ih =>
    simpa only [Profile.rename_union, Need.atGrade_rename, Footprint.rename,
      List.map_cons] using BinderPack.local (need.rename ρ) bound ih
  | external i need rest ih => exact .external i (need.rename ρ) ih

/-- This guard names the actual source annotation; it is not a freely chosen
source typing derivation. The domain certificate is a separate finite child. -/
structure LambdaGuard (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (σ : Subst) (annotation : VExpr) (key : Key n)
    (support : Profile n) : Prop where
  inputTyped : key.input.HasType support
  formed : support.HasType (.sort true)
  path : TypeConversion env U Γ key.domain (annotation.subst σ)
  domains : TypeRelated env U registry Γ key.domain (annotation.subst σ) support
  anchor : Admitted env U registry Γ key key.anchor key.anchor

theorem LambdaGuard.future {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (guard : LambdaGuard env U registry Γ σ annotation key support) :
    LambdaGuard env U registry Δ (σ.lift_r ρ) annotation (key.rename ρ) (support.rename ρ) := by
  refine ⟨Profile.rename_hasType_iff.mpr guard.inputTyped, ?_, ?_, ?_,
    Admitted.future henv W guard.anchor⟩
  · simpa only [Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr guard.formed
  · simpa only [lift'_subst, Key.rename] using guard.path.weak' henv W.weakening
  · simpa only [lift'_subst, Key.rename] using TypeRelated.future henv W guard.domains

/-- Raw frozen Pi prototypes are independent of the source realization.
Codomain evidence is in the actual source-domain context, matching PiWitness;
no semantic fact about a freely chosen prototype is a field of this guard. -/
structure PiGuard (env : VEnv) (U : Nat) (Γ : List VExpr)
    (σ : Subst) (A B prototypeDomain prototypeBody : VExpr) : Prop where
  domainPath : TypeConversion env U Γ (A.subst σ) prototypeDomain
  bodyPath : TypeConversion env U (A.subst σ :: Γ) (B.subst σ.lift) prototypeBody

theorem PiGuard.literal : PiGuard env U Γ σ A B (A.subst σ) (B.subst σ.lift) :=
  ⟨.refl, .refl⟩

theorem PiGuard.future {env : VEnv} {U : Nat}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (guard : PiGuard env U Γ σ A B prototypeDomain prototypeBody) :
    PiGuard env U Δ (σ.lift_r ρ) A B (prototypeDomain.lift' ρ)
      (prototypeBody.lift' ρ.cons) := by
  constructor
  · simpa only [lift'_subst] using guard.domainPath.weak' henv W.weakening
  · simpa only [lift'_subst, ← Subst.lift_r_lift] using
      guard.bodyPath.weak' henv W.weakening.cons

mutual
inductive Obs (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : (locals : List Nat) → Subst → VExpr →
      {n : Nat} → Profile n → Footprint → Type where
  | var (locals : List Nat) (σ : Subst) (i : Nat) (demand : Profile n) :
      Obs env U registry Γ locals σ (.bvar i) demand [(i, ⟨n, demand⟩)]
  | empty :
      Obs env U registry Γ locals σ expression (n := n) .empty []
  | sort (relevant : Relevant level flag) :
      Obs env U registry Γ locals σ (.sort level) (.sort (n := n) flag) []
  | app {key : Key n} {output : Atom n}
      (fn : Obs env U registry Γ locals σ f (Profile.fn key output) fnFootprint)
      (arg : Obs env U registry Γ locals σ a key.input argFootprint)
      (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)) :
      Obs env U registry Γ locals σ (.app f a) (.singleton output)
        (fnFootprint ++ argFootprint)
  | lam {key : Key n} {output : Atom n} {support : Profile n}
      (domain : CodeCert env U registry Γ locals σ annotation support domainFootprint)
      (guard : LambdaGuard env U registry Γ σ annotation key support)
      (body : Obs env U registry Γ (Locals.push locals) (σ.cons key.anchor) expression
        (.singleton output) bodyFootprint)
      (normal : BinderPack n key.input bodyFootprint externalFootprint) :
      Obs env U registry Γ locals σ (.lam annotation expression) (Profile.fn key output)
        (domainFootprint ++ externalFootprint)
  | pi {ambient : Profile n} {rows : List (Key n × Profile n)}
      {prototypeDomain prototypeBody : VExpr}
      (domain : CodeCert env U registry Γ locals σ A ambient domainFootprint)
      (guard : PiGuard env U Γ σ A B prototypeDomain prototypeBody)
      (bodies : PiRows env U registry Γ locals σ A B ambient rows rowFootprint) :
      Obs env U registry Γ locals σ (.forallE A B)
        (Profile.pi prototypeDomain prototypeBody ambient rows)
        (domainFootprint ++ rowFootprint)
  | union
      (left : Obs env U registry Γ locals σ expression leftDemand leftFootprint)
      (right : Obs env U registry Γ locals σ expression rightDemand rightFootprint) :
      Obs env U registry Γ locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | view
      (source : Obs env U registry Γ locals σ expression (.singleton oldAtom) footprint)
      (view : AtomView env U registry Γ oldAtom newAtom) :
      Obs env U registry Γ locals σ expression (.singleton newAtom) footprint
  | pad
      (source : Obs env U registry Γ locals σ expression demand footprint) :
      Obs env U registry Γ locals σ expression demand.pad footprint
  | unpad
      (source : Obs env U registry Γ locals σ expression demand.pad footprint) :
      Obs env U registry Γ locals σ expression demand footprint
  | rowShift
      (source : Obs env U registry Γ locals σ expression (Profile.fn key output) footprint) :
      Obs env U registry Γ locals σ expression (Profile.fn key.pad (.pad output)) footprint

inductive CodeCert (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : (locals : List Nat) → Subst → VExpr →
    {n : Nat} → Profile n → Footprint → Type where
  | seed (observation : Obs env U registry Γ locals σ expression profile footprint)
      (formed : profile.HasType (.sort true)) :
      CodeCert env U registry Γ locals σ expression profile footprint
  | union (left : CodeCert env U registry Γ locals σ expression leftDemand leftFootprint)
      (right : CodeCert env U registry Γ locals σ expression rightDemand rightFootprint) :
      CodeCert env U registry Γ locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | pad (source : CodeCert env U registry Γ locals σ expression profile footprint) :
      CodeCert env U registry Γ locals σ expression profile.pad footprint
  | unpad (source : CodeCert env U registry Γ locals σ expression profile.pad footprint) :
      CodeCert env U registry Γ locals σ expression profile footprint
  | down {profile : Profile (n + 1)}
      (source : CodeCert env U registry Γ locals σ expression profile footprint) :
      CodeCert env U registry Γ locals σ expression profile.down footprint
  | map {a b : Atom n} (view : AtomView env U registry Γ a b)
      (source : CodeCert env U registry Γ locals σ expression profile footprint) :
      CodeCert env U registry Γ locals σ expression (view.mapType profile) footprint
  | select {profile : Profile n} {atom : Atom n}
      (source : CodeCert env U registry Γ locals σ expression profile footprint)
      (member : atom ∈ profile.atoms) :
      CodeCert env U registry Γ locals σ expression (.singleton atom) footprint

/-- A Pi row uses the actual source codomain at its stored anchor. Its
certificate may need fewer local leaves than the function input: coverage
is literal atom membership, so it needs no semantic restriction oracle. -/
inductive PiRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) : (locals : List Nat) → Subst → VExpr → VExpr →
      {n : Nat} → Profile n → List (Key n × Profile n) → Footprint → Type where
  | nil : PiRows env U registry Γ locals σ A B ambient [] []
  | cons {key : Key n} {output packed ambient : Profile n}
      (guard : LambdaGuard env U registry Γ σ A key ambient)
      (body : CodeCert env U registry Γ (Locals.push locals) (σ.cons key.anchor)
        B output bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : PiRows env U registry Γ locals σ A B ambient rows tailFootprint) :
      PiRows env U registry Γ locals σ A B ambient ((key, output) :: rows)
        (externalFootprint ++ tailFootprint)

end

private theorem subst_cons_future (σ : Subst) (anchor : VExpr) (ρ : Lift) :
    (σ.cons anchor).lift_r ρ = (σ.lift_r ρ).cons (anchor.lift' ρ) := by
  funext i
  cases i <;> rfl


/- Target extension changes the realization and frozen target guards only.
Every source observation and every code-certificate leaf is retained. -/
mutual
noncomputable def Obs.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (observation : Obs env U registry Γ locals σ expression demand footprint) :
    Obs env U registry Δ locals (σ.lift_r ρ) expression (demand.rename ρ)
      (Footprint.rename ρ footprint) := by
  match observation with
  | .var locals σ i demand => exact .var locals _ i (demand.rename ρ)
  | .empty => exact .empty
  | .sort relevant => simpa only [Profile.rename_sort, Footprint.rename, List.map_nil] using Obs.sort relevant
  | .app fn arg admitted =>
    have ihfn := fn.future henv W
    have iharg := arg.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ihfn
    have admitted' := Admitted.future henv W admitted
    rw [lift'_subst] at admitted'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, lift'_subst] using Obs.app ihfn iharg admitted'
  | .lam domain guard body normal =>
    have ihdomain := domain.future henv W
    have ihbody := body.future henv W
    rw [subst_cons_future, Profile.rename_singleton] at ihbody
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append] using
      Obs.lam ihdomain (guard.future henv W) ihbody (normal.rename ρ)
  | .pi domain guard bodies =>
    have hd := domain.future henv W
    have hb := bodies.future henv W
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi,
      Footprint.rename_append] using Obs.pi hd (guard.future henv W) hb
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      Obs.union (left.future henv W) (right.future henv W)
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      Obs.view (source.future henv W) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using Obs.pad (source.future henv W)
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact Obs.unpad ih
  | .rowShift source =>
    have ih := source.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ih
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pad,
      Key.pad_rename] using Obs.rowShift ih
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

noncomputable def CodeCert.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {profile : Profile n}
    {footprint : Footprint} (cert : CodeCert env U registry Γ locals σ expression profile footprint) :
    CodeCert env U registry Δ locals (σ.lift_r ρ) expression (profile.rename ρ)
      (Footprint.rename ρ footprint) := by
  match cert with
  | .seed observation formed =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact .seed (observation.future henv W) hf
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      CodeCert.union (left.future henv W) (right.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using CodeCert.pad (source.future henv W)
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact CodeCert.unpad ih
  | .down source =>
    simpa only [Profile.down_rename] using CodeCert.down (source.future henv W)
  | .map view source =>
    have ih := source.future henv W
    simpa only [← AtomView.mapType_future] using
      CodeCert.map (view.future henv W) ih
  | .select source member =>
    simpa only [Profile.rename_singleton] using
      CodeCert.select (source.future henv W) (List.mem_map_of_mem (f := Atom.rename ρ) member)
termination_by sizeOf cert
decreasing_by all_goals simp_wf; omega
noncomputable def PiRows.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint) :
    PiRows env U registry Δ locals (σ.lift_r ρ) A B (ambient.rename ρ)
      (Rows.rename ρ rows) (Footprint.rename ρ footprint) := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    have hb := body.future henv W
    rw [subst_cons_future] at hb
    simpa only [Rows.rename, List.map_cons, Footprint.rename_append] using
      PiRows.cons (guard.future henv W) hb (normal.rename ρ)
        (by
          intro atom hm
          obtain ⟨old, hsource, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old hsource)) (tail.future henv W)
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega

end

/-- A nested output view under an arbitrary function binder is retained on
both eta sides. No local-variable exception changes the old function demand. -/
theorem Obs.variable_eta_view
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {i : Nat}
    {annotation : VExpr} {key : Key n} {output output' : Atom n}
    {support : Profile n} {domainFootprint : Footprint}
    (domain : CodeCert env U registry Γ locals σ annotation support domainFootprint)
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (view : AtomView env U registry Γ output output') :
    Nonempty (Obs env U registry Γ locals σ
      (.lam annotation (.app (.bvar (i + 1)) (.bvar 0))) (Profile.fn key output')
      (domainFootprint ++ [(i, ⟨n + 1, Profile.fn key output⟩)])) ∧
    Nonempty (Obs env U registry Γ locals σ (.bvar i) (Profile.fn key output')
      [(i, ⟨n + 1, Profile.fn key output⟩)]) := by
  have fn := Obs.var (env := env) (U := U) (registry := registry) (Γ := Γ)
    (Locals.push locals) (σ.cons key.anchor) (i + 1) (Profile.fn key output)
  have arg := Obs.var (env := env) (U := U) (registry := registry) (Γ := Γ)
    (Locals.push locals) (σ.cons key.anchor) 0 key.input
  have changed := Obs.view (Obs.app fn arg guard.anchor) view
  have normal : BinderPack n key.input
      ([(i + 1, ⟨n + 1, Profile.fn key output⟩)] ++ [(0, ⟨n, key.input⟩)])
      [(i, ⟨n + 1, Profile.fn key output⟩)] := by
    simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self,
      Profile.union, Profile.empty, Profile.mk, Profile.atoms, List.append_nil,
      List.cons_append, List.nil_append] using
      BinderPack.external i ⟨n + 1, Profile.fn key output⟩
        (BinderPack.local ⟨n, key.input⟩ (Nat.le_refl _) BinderPack.nil)
  exact ⟨⟨Obs.lam domain guard changed normal⟩,
    ⟨Obs.view (Obs.var locals σ i (Profile.fn key output)) (AtomView.fn key view)⟩⟩

end Lean4Lean.AnchoredSource

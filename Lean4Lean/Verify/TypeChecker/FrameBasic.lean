import Lean4Lean.Verify.TypeChecker.FrameDefs
import Lean4Lean.Verify.LocalContext

/-!
# Frame lemma: combinators

Monadic combinators for `M.Framed` and `RecM.Framed` (see `FrameDefs.lean`): bind, pure, throw,
state access, reads of the context, local-context lookups at non-ghosts, binders.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

/-! ### The relation between the contexts -/

theorem GhostRel.ctx_eq {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    c₁.env = c₂.env ∧ c₁.safety = c₂.safety ∧ c₁.eagerReduce = c₂.eagerReduce ∧
    c₁.lparams = c₂.lparams ∧ c₁.fuel = c₂.fuel := by
  have := h.eq; revert this; cases c₁; cases c₂; simp +contextual

theorem GhostRel.env_eq {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) : c₁.env = c₂.env :=
  h.ctx_eq.1

theorem GhostRel.withLCtx {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) {l₁ l₂ : LocalContext}
    (hf : ∀ ⦃fv⦄, ¬ G fv → (l₁.find? fv).map (·.setIndex 0) = (l₂.find? fv).map (·.setIndex 0))
    (hd : ∀ ⦃fv d⦄, l₂.find? fv = some d →
      GF G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GF G v)
    (hw₁ : l₁.fvarIdToDecl.WF) (hw₂ : l₂.fvarIdToDecl.WF) :
    GhostRel G { c₁ with lctx := l₁ } { c₂ with lctx := l₂ } where
  eq := by have := h.eq; revert this; cases c₁; cases c₂; simp +contextual
  find? := hf
  decls := hd
  wf₁ := hw₁
  wf₂ := hw₂
  env := h.env

theorem find?_mkLocalDecl' {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty : Expr}
    {bi : BinderInfo} {kind : LocalDeclKind} (hwf : l.fvarIdToDecl.WF) :
    (l.mkLocalDecl fv name ty bi kind).find? fv' =
      if fv == fv' then some (.cdecl l.decls.size fv name ty bi kind)
      else l.find? fv' := by
  simp only [LocalContext.mkLocalDecl, LocalContext.find?]
  exact hwf.find?_insert

theorem find?_mkLetDecl' {l : LocalContext} {fv fv' : FVarId} {name : Name} {ty val : Expr}
    {nonDep : Bool} {kind : LocalDeclKind} (hwf : l.fvarIdToDecl.WF) :
    (l.mkLetDecl fv name ty val nonDep kind).find? fv' =
      if fv == fv' then some (.ldecl l.decls.size fv name ty val nonDep kind)
      else l.find? fv' := by
  simp only [LocalContext.mkLetDecl, LocalContext.find?]
  exact hwf.find?_insert

theorem GhostRel.mkLocalDecl {c₁ c₂ : Context} {id : FVarId} (h : GhostRel G c₁ c₂)
    (hty : GF G ty) :
    GhostRel G { c₁ with lctx := c₁.lctx.mkLocalDecl id name ty bi }
      { c₂ with lctx := c₂.lctx.mkLocalDecl id name ty bi } := by
  refine h.withLCtx (fun fv hfv => ?_) (fun fv d hd => ?_)
    (by simp only [LocalContext.mkLocalDecl]; exact h.wf₁.insert)
    (by simp only [LocalContext.mkLocalDecl]; exact h.wf₂.insert)
  · rw [find?_mkLocalDecl' h.wf₁, find?_mkLocalDecl' h.wf₂]
    split
    · simp [LocalDecl.setIndex]
    · exact h.find? hfv
  · rw [find?_mkLocalDecl' h.wf₂] at hd
    split at hd
    · cases hd; exact ⟨hty, by simp [LocalDecl.value?]⟩
    · exact h.decls hd

theorem GhostRel.mkLetDecl {c₁ c₂ : Context} {id : FVarId} (h : GhostRel G c₁ c₂)
    (hty : GF G ty) (hval : GF G val) :
    GhostRel G { c₁ with lctx := c₁.lctx.mkLetDecl id name ty val }
      { c₂ with lctx := c₂.lctx.mkLetDecl id name ty val } := by
  refine h.withLCtx (fun fv hfv => ?_) (fun fv d hd => ?_)
    (by simp only [LocalContext.mkLetDecl]; exact h.wf₁.insert)
    (by simp only [LocalContext.mkLetDecl]; exact h.wf₂.insert)
  · rw [find?_mkLetDecl' h.wf₁, find?_mkLetDecl' h.wf₂]
    split
    · simp [LocalDecl.setIndex]
    · exact h.find? hfv
  · rw [find?_mkLetDecl' h.wf₂] at hd
    split at hd
    · cases hd; exact ⟨hty, by simp [LocalDecl.value?]; exact hval⟩
    · exact h.decls hd

theorem GhostRel.eager {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    GhostRel G { c₁ with eagerReduce := true } { c₂ with eagerReduce := true } where
  eq := by have := h.eq; revert this; cases c₁; cases c₂; simp +contextual
  find? := h.find?
  decls := h.decls
  wf₁ := h.wf₁
  wf₂ := h.wf₂
  env := h.env

/-! ### `M.Framed` -/

theorem M.Framed.bind {x : M α} {f : α → M β} {P Q}
    (h1 : M.Framed G x P) (h2 : ∀ a, P a → M.Framed G (f a) Q) : M.Framed G (x >>= f) Q := by
  intro c₁ c₂ s b s' hr hs e
  simp only [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind] at e ⊢
  cases ex : x c₁ s with
  | error => rw [ex] at e; cases e
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [ex] at e
    obtain ⟨h1a, h1b, h1c, h1d⟩ := h1 hr hs ex
    rw [h1a]
    obtain ⟨h2a, h2b, h2c, h2d⟩ := h2 a h1b hr h1c e
    exact ⟨h2a, h2b, h2c, h1d.trans h2d⟩

theorem M.Framed.pure {a : α} {R} (h : R a) : M.Framed G (pure a) R := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, h, hs, .rfl⟩

theorem M.Framed.throw {R} : M.Framed G (throw e : M α) R := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩

theorem M.Framed.mono {x : M α} {R R'} (h : M.Framed G x R) (H : ∀ a, R a → R' a) :
    M.Framed G x R' := fun _ _ _ _ _ hr hs e =>
  let ⟨h1, h2, h3, h4⟩ := h hr hs e; ⟨h1, H _ h2, h3, h4⟩

theorem M.Framed.map {x : M α} {f : α → β} {R R'} (h : M.Framed G x R)
    (H : ∀ a, R a → R' (f a)) : M.Framed G (f <$> x) R' := by
  rw [map_eq_pure_bind]; exact h.bind fun a ha => .pure (H a ha)

theorem M.Framed.getEnv : M.Framed G TypeChecker.getEnv fun _ => True := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨by rw [hr.env_eq]; rfl, trivial, hs, .rfl⟩

theorem M.Framed.getEnv' : M.Framed G TypeChecker.getEnv (EnvGF G) := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨by rw [hr.env_eq]; rfl, hr.env_eq ▸ hr.env, hs, .rfl⟩

theorem M.Framed.getLCtx_throw {f : LocalContext → Exception} {R} :
    M.Framed G (getLCtx >>= fun l => (MonadExcept.throw (f l) : M α)) R := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩

/-- A read of the context whose continuation does not depend on the local context. -/
theorem M.Framed.read {f : Context → M α} {R}
    (hf : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → f c₁ = f c₂)
    (H : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → M.Framed G (f c₂) R) :
    M.Framed G (MonadReader.read >>= f) R := by
  intro c₁ c₂ s b s' hr hs e
  change f c₁ c₁ s = _ at e
  have : (MonadReader.read >>= f) c₂ s = f c₂ c₂ s := rfl
  rw [this]; rw [hf hr] at e; exact H hr hr hs e

theorem M.Framed.get : M.Framed G (MonadState.get : M State) (GFState G) := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, hs, hs, .rfl⟩

theorem M.Framed.modify {f : State → State}
    (hf : ∀ s, GFState G s → GFState G (f s) ∧ s.ngen ≤ (f s).ngen) :
    M.Framed G (modify f : M Unit) fun _ => True := by
  rintro c₁ c₂ s b s' hr hs ⟨⟩; exact ⟨rfl, trivial, (hf s hs).1, (hf s hs).2⟩

theorem M.Framed.modifyGet {f : State → β × State}
    (hf : ∀ s, GFState G s → GFState G (f s).2 ∧ s.ngen ≤ (f s).2.ngen) :
    M.Framed G (modifyGet f : M β) fun _ => True := by
  intro c₁ c₂ s b s' hr hs e
  have h1 : f s = (b, s') := Except.ok.inj e
  have h2 : (f s).2 = s' := by rw [h1]
  exact ⟨e, trivial, h2 ▸ (hf s hs).1, h2 ▸ (hf s hs).2⟩

theorem M.Framed.liftExcept {x : Except Exception α} {R} (h : ∀ a, x = .ok a → R a) :
    M.Framed G (liftM x : M α) R := by
  intro c₁ c₂ s b s' hr hs e
  cases x with
  | error => cases e
  | ok a => cases e; exact ⟨rfl, h _ rfl, hs, .rfl⟩

/-- A read of the local context at a non-ghost. -/
theorem M.Framed.getLCtx_find {id : FVarId} (hid : ¬ G id) {f : LocalContext → M α} {R}
    (hf : ∀ ⦃l₁ l₂ : LocalContext⦄,
      (l₁.find? id).map (·.setIndex 0) = (l₂.find? id).map (·.setIndex 0) → f l₁ = f l₂)
    (H : ∀ l : LocalContext, (∀ ⦃d⦄, l.find? id = some d →
      GF G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GF G v) → M.Framed G (f l) R) :
    M.Framed G (getLCtx >>= f) R := by
  intro c₁ c₂ s b s' hr hs e
  change f c₁.lctx c₁ s = _ at e
  have : (getLCtx >>= f) c₂ s = f c₂.lctx c₂ s := rfl
  rw [this]
  rw [hf (hr.find? hid)] at e
  exact H _ (fun _ hd => hr.decls hd) hr hs e

/-! ### Binders -/

theorem withFreshId_eq' {α} (x : Name → M α) (c : Context) (s : State) :
    (withFreshId x : M α) c s =
      (x s.ngen.curr c { s with ngen := s.ngen.next }).map fun p => (p.1, s.leaveScope p.2) := by
  unfold withFreshId instMonadLocalNameGeneratorM
  simp only [bind, ReaderT.bind, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, liftM, monadLift, MonadLift.monadLift, Except.bind, pure, Except.pure,
    ReaderT.pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    mkFreshId, getNGen, setNGen]
  cases x s.ngen.curr c { s with ngen := s.ngen.next } <;> rfl

theorem GFState.next {s : State} (h : GFState G s) : GFState G { s with ngen := s.ngen.next } :=
  { h with reserved := fun _ hg => (h.reserved hg).mono NameGenerator.LE.next }

theorem GFState.leaveScope {saved s : State} (h₁ : GFState G saved) (h₂ : GFState G s) :
    GFState G (saved.leaveScope s) :=
  { h₁ with unfold := h₂.unfold, reserved := h₂.reserved }

theorem M.Framed.withFreshId {x : Name → M α} {R}
    (H : ∀ (n : Name) (s : State) (c₁ c₂ : Context), GhostRel G c₁ c₂ → GFState G s →
      ¬ G ⟨n⟩ → ∀ a s', x n c₁ s = .ok (a, s') →
        x n c₂ s = .ok (a, s') ∧ R a ∧ GFState G s' ∧ s.ngen ≤ s'.ngen) :
    M.Framed G (withFreshId x) R := by
  intro c₁ c₂ s b s' hr hs e
  rw [withFreshId_eq'] at e ⊢
  have hfresh : ¬ G ⟨s.ngen.curr⟩ := fun hg =>
    NameGenerator.not_reserves_self (hs.reserved hg)
  cases ex : x s.ngen.curr c₁ { s with ngen := s.ngen.next } with
  | error => rw [ex] at e; cases e
  | ok p =>
    obtain ⟨a, s1⟩ := p
    rw [ex] at e; cases e
    obtain ⟨h1, h2, h3, h4⟩ := H _ _ _ _ hr hs.next hfresh _ _ ex
    rw [h1]
    exact ⟨rfl, h2, hs.leaveScope h3, NameGenerator.LE.next.trans h4⟩

theorem M.Framed.withLocalDecl {f : Expr → M α} {R} (hty : GF G ty)
    (H : ∀ id, ¬ G id → M.Framed G (f (.fvar id)) R) :
    M.Framed G (withLocalDecl name bi ty f) R := by
  refine .withFreshId fun n s c₁ c₂ hr hs hn a s' e => ?_
  exact H _ hn (hr.mkLocalDecl hty) hs e

theorem M.Framed.withLetDecl {f : Expr → M α} {R} (hty : GF G ty) (hval : GF G val)
    (H : ∀ id, ¬ G id → M.Framed G (f (.fvar id)) R) :
    M.Framed G (withLetDecl name ty val f) R := by
  refine .withFreshId fun n s c₁ c₂ hr hs hn a s' e => ?_
  exact H _ hn (hr.mkLetDecl hty hval) hs e

theorem M.Framed.withEager {x : M α} {R} (h : M.Framed G x R) :
    M.Framed G (withTheReader Context (fun s => { s with eagerReduce := true }) x) R :=
  fun _ _ _ _ _ hr hs e => h hr.eager hs e

/-! ### `RecM.Framed` -/

theorem RecM.Framed.bind {x : RecM α} {f : α → RecM β} {P Q}
    (h1 : RecM.Framed G x P) (h2 : ∀ a, P a → RecM.Framed G (f a) Q) :
    RecM.Framed G (x >>= f) Q :=
  fun _ hm => M.Framed.bind (h1 hm) fun a ha => h2 a ha hm

theorem RecM.Framed.pure {a : α} {R} (h : R a) : RecM.Framed G (pure a) R :=
  fun _ _ => .pure h

theorem RecM.Framed.throw {R} : RecM.Framed G (throw e : RecM α) R := fun _ _ => .throw

theorem RecM.Framed.throw_bind {f : α → RecM β} {R} :
    RecM.Framed G (MonadExcept.throw e >>= f) R :=
  RecM.Framed.bind (P := fun _ => False) .throw nofun

theorem RecM.Framed.panic [Inhabited α] {R : α → Prop} (h : R default) :
    RecM.Framed G (panicWithPosWithDecl m d l c msg : RecM α) R := by
  simp only [panicWithPosWithDecl]; exact RecM.Framed.pure h

theorem RecM.Framed.mono {x : RecM α} {R R'} (h : RecM.Framed G x R) (H : ∀ a, R a → R' a) :
    RecM.Framed G x R' := fun _ hm => (h hm).mono H

theorem RecM.Framed.map {x : RecM α} {f : α → β} {R R'} (h : RecM.Framed G x R)
    (H : ∀ a, R a → R' (f a)) : RecM.Framed G (f <$> x) R' := by
  rw [map_eq_pure_bind]; exact h.bind fun a ha => .pure (H a ha)

theorem RecM.Framed.lift {x : M α} {R} (h : M.Framed G x R) : RecM.Framed G (liftM x) R :=
  fun _ _ => h

theorem RecM.Framed.getEnv : RecM.Framed G (liftM TypeChecker.getEnv) fun _ => True := .lift .getEnv

theorem RecM.Framed.getEnv' : RecM.Framed G (liftM TypeChecker.getEnv) (EnvGF G) := .lift .getEnv'

theorem RecM.Framed.getLCtx_throw {f : LocalContext → Exception} {R} :
    RecM.Framed G (getLCtx >>= fun l => (MonadExcept.throw (f l) : RecM α)) R := by
  rintro _ _ c₁ c₂ s b s' hr hs ⟨⟩

theorem RecM.Framed.getLCtx_throw_bind {f : LocalContext → Exception}
    {g : LocalContext → α → RecM β} {R} :
    RecM.Framed G (getLCtx >>= fun l => (MonadExcept.throw (f l) : RecM α) >>= g l) R := by
  rintro _ _ c₁ c₂ s b s' hr hs ⟨⟩

theorem RecM.Framed.read {f : Context → RecM α} {R}
    (hf : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → f c₁ = f c₂)
    (H : ∀ ⦃c₁ c₂⦄, GhostRel G c₁ c₂ → RecM.Framed G (f c₂) R) :
    RecM.Framed G (readThe Context >>= f) R :=
  fun m hm => M.Framed.read (f := fun c => f c m) (fun _ _ h => by rw [hf h])
    fun _ _ hc => H hc hm

theorem RecM.Framed.get : RecM.Framed G (MonadState.get : RecM State) (GFState G) :=
  fun _ _ => .get

theorem RecM.Framed.modify {f : State → State}
    (hf : ∀ s, GFState G s → GFState G (f s) ∧ s.ngen ≤ (f s).ngen) :
    RecM.Framed G (modify f : RecM Unit) fun _ => True := fun _ _ => .modify hf

theorem RecM.Framed.modifyGet {f : State → β × State}
    (hf : ∀ s, GFState G s → GFState G (f s).2 ∧ s.ngen ≤ (f s).2.ngen) :
    RecM.Framed G (modifyGet f : RecM β) fun _ => True := fun _ _ => .modifyGet hf

theorem RecM.Framed.liftExcept {x : Except Exception α} {R} (h : ∀ a, x = .ok a → R a) :
    RecM.Framed G (liftM x : RecM α) R := fun _ _ => .liftExcept h

theorem RecM.Framed.getLCtx_find {id : FVarId} (hid : ¬ G id) {f : LocalContext → RecM α} {R}
    (hf : ∀ ⦃l₁ l₂ : LocalContext⦄,
      (l₁.find? id).map (·.setIndex 0) = (l₂.find? id).map (·.setIndex 0) → f l₁ = f l₂)
    (H : ∀ l : LocalContext, (∀ ⦃d⦄, l.find? id = some d →
      GF G d.type ∧ ∀ ⦃v⦄, d.value? true = some v → GF G v) → RecM.Framed G (f l) R) :
    RecM.Framed G (getLCtx >>= f) R :=
  fun m hm => M.Framed.getLCtx_find (f := fun l => f l m) hid
    (fun _ _ h => by rw [hf h]) fun l hl => H l hl hm

theorem RecM.Framed.withLocalDecl {f : Expr → RecM α} {R} (hty : GF G ty)
    (H : ∀ id, ¬ G id → RecM.Framed G (f (.fvar id)) R) :
    RecM.Framed G (withLocalDecl name bi ty f) R :=
  fun m hm => M.Framed.withLocalDecl (f := fun e => f e m) hty fun id hid => H id hid hm

theorem RecM.Framed.withLetDecl {f : Expr → RecM α} {R} (hty : GF G ty) (hval : GF G val)
    (H : ∀ id, ¬ G id → RecM.Framed G (f (.fvar id)) R) :
    RecM.Framed G (withLetDecl name ty val f) R :=
  fun m hm => M.Framed.withLetDecl (f := fun e => f e m) hty hval fun id hid => H id hid hm

theorem RecM.Framed.withEager {x : RecM α} {R} (h : RecM.Framed G x R) :
    RecM.Framed G (withTheReader Context (fun s => { s with eagerReduce := true }) x) R :=
  fun _ hm => (h hm).withEager

/-! ### Methods -/

theorem RecM.Framed.whnf (h : GF G e) : RecM.Framed G (Inner.whnf e) (GF G) :=
  fun _ hm => hm.whnf h

theorem RecM.Framed.whnfCore (h : GF G e) : RecM.Framed G (Inner.whnfCore e cheapProj) (GF G) :=
  fun _ hm => hm.whnfCore cheapProj h

theorem RecM.Framed.inferType (h : GF G e) :
    RecM.Framed G (Inner.inferType e inferOnly) (GF G) :=
  fun _ hm => hm.inferType inferOnly h

theorem RecM.Framed.isDefEqCore (h₁ : GF G t) (h₂ : GF G s) :
    RecM.Framed G (Inner.isDefEqCore t s) fun _ => True :=
  fun _ hm => hm.isDefEqCore h₁ h₂

theorem RecM.Framed.isDefEq (h₁ : GF G t) (h₂ : GF G s) :
    RecM.Framed G (Inner.isDefEq t s) fun _ => True := by
  unfold Inner.isDefEq
  refine (RecM.Framed.isDefEqCore h₁ h₂).bind fun r _ => ?_
  split
  · refine RecM.Framed.bind (RecM.Framed.modify ?_) fun _ _ => .pure trivial
    intro s hs
    exact ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6⟩, .rfl⟩
  · exact .pure trivial

end Lean4Lean.TypeChecker

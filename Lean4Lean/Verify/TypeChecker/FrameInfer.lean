import Lean4Lean.Verify.TypeChecker.FrameExpr

/-!
# Frame lemma: type inference
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

namespace Inner

theorem ensureSortCore.framed (he : GF G e) : RecM.Framed G (ensureSortCore e s) (GF G) := by
  unfold ensureSortCore
  split
  · exact .pure he
  refine (RecM.Framed.whnf he).bind fun e he => ?_
  split
  · exact .pure he
  exact RecM.Framed.getEnv.bind fun _ _ => .getLCtx_throw

theorem ensureForallCore.framed (he : GF G e) : RecM.Framed G (ensureForallCore e s) (GF G) := by
  unfold ensureForallCore
  split
  · exact .pure he
  refine (RecM.Framed.whnf he).bind fun e he => ?_
  split
  · exact .pure he
  exact RecM.Framed.getEnv.bind fun _ _ => .getLCtx_throw

theorem inferLambda.loop.framed :
    ∀ (fvars : Array Expr) (e : Expr), FVArr G fvars → GF G e →
      RecM.Framed G (inferLambda.loop inferOnly fvars e) (GF G) := by
  intro fvars e hfv he
  induction e generalizing fvars with
  | lam name dom body bi _ ih =>
    unfold inferLambda.loop
    have hd : GF G (dom.instantiateRev fvars) := he.1.instantiateRev hfv.gfArr
    have k : RecM.Framed G (withLocalDecl name bi (dom.instantiateRev fvars) fun fv =>
        inferLambda.loop inferOnly (fvars.push fv) body) (GF G) :=
      .withLocalDecl hd fun id hid => ih _ (hfv.push hid) he.2
    split
    · exact (RecM.Framed.inferType hd).bind fun _ h => (ensureSortCore.framed h).bind
        fun _ _ => k
    · exact k
  | _ =>
    unfold inferLambda.loop
    refine (RecM.Framed.inferType (he.instantiateRev hfv.gfArr)).bind fun r hr => ?_
    exact .getLCtx_mkForall hfv hr.cheapBetaReduce

theorem inferForall.loop.framed :
    ∀ (fvars : Array Expr) (us : Array Level) (e : Expr), FVArr G fvars →
      (∀ u ∈ us, u.hasMVar' = false) → GF G e →
      RecM.Framed G (inferForall.loop inferOnly fvars us e) (GF G) := by
  intro fvars us e hfv hus he
  induction e generalizing fvars us with
  | forallE name dom body bi _ ih =>
    unfold inferForall.loop
    have hd : GF G (dom.instantiateRev fvars) := he.1.instantiateRev hfv.gfArr
    refine (RecM.Framed.inferType hd).bind fun _ h => (ensureSortCore.framed h).bind
      fun t1 ht1 => ?_
    refine .withLocalDecl hd fun id hid => ih _ _ (hfv.push hid) ?_ he.2
    intro u hu; rcases Array.mem_push.1 hu with hu | rfl
    · exact hus u hu
    · exact ht1.sortLevel!
  | _ =>
    unfold inferForall.loop
    refine (RecM.Framed.inferType (he.instantiateRev hfv.gfArr)).bind fun r hr => ?_
    refine (ensureSortCore.framed hr).bind fun s hs => .pure ?_
    show Level.hasMVar' _ = false
    rw [← Array.foldr_toList]
    have : ∀ u ∈ us.toList, u.hasMVar' = false := fun u hu => hus u (Array.mem_toList_iff.1 hu)
    generalize us.toList = l at this
    induction l with
    | nil => exact hs.sortLevel!
    | cons u l ih =>
      simp only [List.foldr_cons]
      exact Level.mkLevelIMax'_hasMVar_false _ _ (this u (.head _))
        (ih fun u hu => this u (.tail _ hu))

theorem inferApp.framed (he : GF G e) : RecM.Framed G (inferApp e) (GF G) := by
  unfold inferApp
  rw [Expr.withApp_eq]
  have hargs := he.getAppArgs
  refine (RecM.Framed.inferType he.getAppFn).bind fun fType hf => ?_
  suffices ∀ fType j i, GF G fType → RecM.Framed G (inferApp.loop e e.getAppArgs fType j i) (GF G)
    from this _ _ _ hf
  intro fType j i hf
  induction fType, j, i using inferApp.loop.induct (args := e.getAppArgs) with
  | case1 i hi _ _ body _ j ih => unfold inferApp.loop; rw [if_pos hi]; exact ih hf.2
  | case2 fType i hi j hne ih =>
    unfold inferApp.loop; rw [if_pos hi]; split
    · exact absurd rfl (hne _ _ _ _)
    · exact (ensureForallCore.framed (hf.instantiateRevRange hargs)).bind fun _ h =>
        ih _ h.bindingBody!
  | case3 fType j i hi =>
    unfold inferApp.loop; rw [if_neg hi]; exact .pure (hf.instantiateRevRange hargs)

theorem inferLet.loop.framed :
    ∀ (fvars : Array Expr) (e : Expr), FVArr G fvars → GF G e →
      RecM.Framed G (inferLet.loop inferOnly fvars e) (GF G) := by
  intro fvars e hfv he
  induction e generalizing fvars with
  | letE name type val body _ _ _ ih =>
    unfold inferLet.loop
    have ht : GF G (type.instantiateRev fvars) := he.1.instantiateRev hfv.gfArr
    have hv : GF G (val.instantiateRev fvars) := he.2.1.instantiateRev hfv.gfArr
    extract_lets type' val' jp
    have k : RecM.Framed G (jp ()) (GF G) :=
      .withLetDecl ht hv fun id hid => ih _ (hfv.push hid) he.2.2
    split
    · refine (RecM.Framed.inferType ht).bind fun _ h => (ensureSortCore.framed h).bind
        fun _ _ => (RecM.Framed.inferType hv).bind fun _ h => ?_
      refine (RecM.Framed.isDefEq h ht).bind fun _ _ => ?_
      split
      · exact RecM.Framed.getEnv.bind fun _ _ => .getLCtx_throw
      · exact k
    · exact k
  | _ =>
    unfold inferLet.loop
    refine (RecM.Framed.inferType (he.instantiateRev hfv.gfArr)).bind fun r hr => ?_
    exact .getLCtx_mkForall hfv hr.cheapBetaReduce

theorem getSortLevel.framed (he : GF G e) : RecM.Framed G (getSortLevel e) fun _ => True := by
  unfold getSortLevel
  refine (RecM.Framed.inferType he).bind fun _ h => (ensureSortCore.framed h).bind fun _ _ => ?_
  split
  · exact .pure trivial
  · exact .panic trivial

theorem isProp.framed (he : GF G e) : RecM.Framed G (isProp e) fun _ => True :=
  (getSortLevel.framed he).bind fun _ _ => .pure trivial

/-- An optional result is ghost-free. -/
def OGF (G : FVarId → Prop) (o : Option Expr) : Prop := ∀ ⦃e⦄, o = some e → GF G e

theorem OGF.none : OGF G none := nofun
theorem OGF.some (h : GF G e) : OGF G (some e) := by rintro _ ⟨⟩; exact h

theorem instantiateProjectionParameters.framed {args : Array Expr} (hargs : GFArr G args) :
    ∀ (type : Expr) (pos rem : Nat), GF G type →
      RecM.Framed G (instantiateProjectionParameters type args pos rem) (OGF G) := by
  intro type pos rem ht
  induction rem generalizing type pos with
  | zero => unfold instantiateProjectionParameters; exact .pure (.some ht)
  | succ rem ih =>
    unfold instantiateProjectionParameters
    refine (RecM.Framed.whnf ht).bind fun t ht => ?_
    split
    · split
      · rename_i a ha
        exact ih _ _ (GF.instantiate1 ht.2 (hargs.getElem? ha))
      · exact .pure OGF.none
    · exact .pure OGF.none

theorem instantiateProjectionFields.framed (hs : GF G struct) :
    ∀ (type : Expr) (pos rem : Nat), GF G type →
      RecM.Framed G (instantiateProjectionFields typeName struct mp type pos rem) (OGF G) := by
  intro type pos rem ht
  induction rem generalizing type pos with
  | zero => unfold instantiateProjectionFields; exact .pure (.some ht)
  | succ rem ih =>
    unfold instantiateProjectionFields
    refine (RecM.Framed.whnf ht).bind fun t ht => ?_
    split
    · have k := ih _ (pos + 1) (GF.instantiate1 ht.2 (a := .proj typeName pos struct) hs)
      split
      · split
        · refine (isProp.framed ht.1).bind fun _ _ => ?_
          split
          · exact k
          · exact .pure OGF.none
        · exact k
      · exact ih _ _ ht.2
    · exact .pure OGF.none

theorem envGet_gf {env : Environment} (henv : EnvGF G env) :
    (env.get n).WF fun ci => env.find? n = some ci ∧ ConstGF G ci := by
  simp [Kernel.Environment.get]; split <;> [refine .pure ⟨‹_›, henv ‹_›⟩; exact .throw]

theorem inferConstant_congr {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    inferConstant c₁ n ls io = inferConstant c₂ n ls io := by
  rw [h.eq]; rfl

theorem inferConstant_gf {tc : Context} (henv : EnvGF G tc.env)
    (hls : ∀ l ∈ ls, l.hasMVar' = false) :
    (inferConstant tc n ls io).WF (GF G) := by
  simp [inferConstant]; refine (envGet_gf henv).bind fun ci ⟨_, hci⟩ => ?_
  have hres : GF G (ci.instantiateTypeLevelParams ls) := hci.type.instantiateLevelParams hls
  have hret {β} {x : Except Exception β} :
      ((fun _ => ci.instantiateTypeLevelParams ls) <$> x).WF (GF G) :=
    Except.WF.map (h1 := fun _ _ => trivial) fun _ _ => hres
  split <;> [skip; exact .throw]
  split
  · split <;> [exact .throw; skip]
    split <;> [skip; exact hret]
    split <;> [exact .throw; exact hret]
  · exact .pure hres

theorem inferFVar_congr {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) (hn : ¬ G n) :
    inferFVar c₁ n = inferFVar c₂ n := by
  have := h.find? hn
  unfold inferFVar
  revert this
  cases c₁.lctx.find? n with
  | none => cases c₂.lctx.find? n <;> simp
  | some d₁ =>
    cases c₂.lctx.find? n with
    | none => simp
    | some d₂ =>
      cases d₁ <;> cases d₂ <;> simp [LocalDecl.setIndex] <;> intros <;> subst_vars <;> rfl

theorem inferFVar_gf {c₁ c₂ : Context} (h : GhostRel G c₁ c₂) :
    (inferFVar c₂ n).WF (GF G) := by
  unfold inferFVar; split
  · rename_i d hd; exact .pure (h.decls hd).1
  · exact .throw

theorem RecM.Framed.inferFVar (hn : ¬ G n) {f : Expr → RecM α} {R}
    (hf : ∀ a, GF G a → RecM.Framed G (f a) R) :
    RecM.Framed G (readThe Context >>= fun c => liftM (inferFVar c n) >>= f) R := by
  refine RecM.Framed.read (fun _ _ h => by rw [inferFVar_congr h hn]) fun _ _ h => ?_
  exact (RecM.Framed.liftExcept (inferFVar_gf h)).bind hf

theorem RecM.Framed.inferConstant (hls : ∀ l ∈ ls, l.hasMVar' = false) {f : Expr → RecM α} {R}
    (hf : ∀ a, GF G a → RecM.Framed G (f a) R) :
    RecM.Framed G (readThe Context >>= fun c => liftM (inferConstant c n ls io) >>= f) R := by
  refine RecM.Framed.read (fun _ _ h => by rw [inferConstant_congr h]) fun _ _ h => ?_
  exact (RecM.Framed.liftExcept (inferConstant_gf h.env hls)).bind hf

theorem RecM.Framed.checkLevel {f : Unit → RecM α} {R} (hf : RecM.Framed G (f ()) R) :
    RecM.Framed G (readThe Context >>= fun c => liftM (checkLevel c l) >>= f) R := by
  refine RecM.Framed.read (fun _ _ h => by rw [h.eq]; rfl) fun _ _ h => ?_
  exact (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => hf

theorem inferProj.framed (hs : GF G struct) (hst : GF G structType) :
    RecM.Framed G (inferProj typeName idx struct structType) (GF G) := by
  unfold inferProj
  refine (RecM.Framed.whnf hst).bind fun type htype => ?_
  rw [Expr.withApp_eq]
  have hargs := htype.getAppArgs
  refine RecM.Framed.getEnv'.bind fun env henv => ?_
  extract_lets fail
  have hfail {β} {R : β → Prop} : RecM.Framed G (@fail β) R := RecM.Framed.getLCtx_throw
  have hfailb {β γ} {f : β → RecM γ} {R} : RecM.Framed G (fail >>= f) R :=
    (hfail (R := fun _ => False)).bind nofun
  split <;> [skip; exact hfail]
  rename_i I_name I_levels hI
  have hIl : ∀ l ∈ I_levels, l.hasMVar' = false := by
    have := htype.getAppFn; rw [hI] at this; exact this
  extract_lets jp1
  split <;> try exact hfailb
  dsimp only [jp1]
  refine (RecM.Framed.liftExcept (envGet_gf henv)).bind fun _ _ => ?_
  split <;> [skip; exact hfail]
  rename_i I_val
  split <;> [skip; exact hfail]
  rename_i c
  split <;> try exact hfailb
  refine (RecM.Framed.liftExcept (envGet_gf henv)).bind fun c_info ⟨_, hc⟩ => ?_
  split <;> [skip; exact hfail]
  rename_i c_val
  split <;> try exact hfailb
  refine (instantiateProjectionParameters.framed hargs _ _ _
    (hc.type.instantiateLevelParams hIl)).bind fun _ h => ?_
  split <;> [skip; exact hfail]
  rename_i ap
  refine (getSortLevel.framed htype).bind fun _ _ => ?_
  refine (instantiateProjectionFields.framed hs _ _ _ (h rfl)).bind fun _ h => ?_
  split <;> [skip; exact hfail]
  rename_i sel
  refine (RecM.Framed.whnf (h rfl)).bind fun _ h => ?_
  split <;> [skip; exact hfail]
  rename_i _ dom _ _
  have hdom : GF G dom := h.1
  split
  · refine (isProp.framed hdom).bind fun _ _ => ?_
    split <;> [exact hfailb; exact .pure hdom]
  · exact .pure hdom

theorem inferLambda.framed (he : GF G e) : RecM.Framed G (inferLambda e inferOnly) (GF G) :=
  inferLambda.loop.framed _ _ FVArr.empty he

theorem inferForall.framed (he : GF G e) : RecM.Framed G (inferForall e inferOnly) (GF G) :=
  inferForall.loop.framed _ _ _ FVArr.empty nofun he

theorem inferLet.framed (he : GF G e) : RecM.Framed G (inferLet e inferOnly) (GF G) :=
  inferLet.loop.framed _ _ FVArr.empty he

theorem inferType'.framed : ∀ {e : Expr} (inferOnly : Bool), GF G e →
    RecM.Framed G (inferType' e inferOnly) (GF G)
  | e, inferOnly, he => by
    unfold inferType'
    extract_lets jp2 jp
    have hjp2 : ∀ r, GF G r → RecM.Framed G (jp2 r) (GF G) := by
      intro r hr
      refine RecM.Framed.bind (RecM.Framed.modify ?_) fun _ _ => .pure hr
      intro s hs
      cases inferOnly <;> simp only [cond_false, cond_true]
      · refine ⟨⟨hs.1, ?_, hs.3, hs.4, hs.5, hs.6⟩, .rfl⟩
        intro a b h
        simp only [Std.HashMap.getElem?_insert] at h; split at h
        · cases h; exact hr
        · exact hs.2 h
      · refine ⟨⟨?_, hs.2, hs.3, hs.4, hs.5, hs.6⟩, .rfl⟩
        intro a b h
        simp only [Std.HashMap.getElem?_insert] at h; split at h
        · cases h; exact hr
        · exact hs.1 h
    split
    · exact RecM.Framed.throw_bind
    rename_i hlb
    dsimp only [jp]
    refine RecM.Framed.get.bind fun st hst => ?_
    split
    · rename_i r hr
      refine .pure ?_
      cases inferOnly
      · exact hst.inferTypeC hr
      · exact hst.inferTypeI hr
    split
    · rename_i l _
      have hjp3 := (RecM.Framed.pure (R := GF G) (a := mkConst l.typeName)
        (by intro _ h; cases h)).bind hjp2
      split
      · split
        · exact RecM.Framed.getEnv.bind fun _ _ =>
            (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => hjp3
        · exact RecM.Framed.getEnv.bind fun _ _ =>
            (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ =>
            RecM.Framed.getEnv.bind fun _ _ =>
            (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => hjp3
      · exact hjp3
    · rename_i _ e' _
      exact (inferType'.framed (e := e') inferOnly he).bind hjp2
    · rename_i _ _ e' _
      exact (inferType'.framed (e := e') inferOnly he).bind fun _ h =>
        (inferProj.framed (struct := e') he h).bind hjp2
    · exact RecM.Framed.inferFVar he hjp2
    · exact RecM.Framed.throw_bind
    · simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at hlb
    · rename_i l _
      have hjp3 := (RecM.Framed.pure (R := GF G) (a := .sort l.succ) (by exact he)).bind hjp2
      split
      · exact RecM.Framed.checkLevel hjp3
      · exact hjp3
    · exact RecM.Framed.inferConstant he hjp2
    · exact (inferLambda.framed he).bind hjp2
    · exact (inferForall.framed he).bind hjp2
    · rename_i f a _
      split
      · exact (inferApp.framed he).bind hjp2
      · refine (inferType'.framed (e := f) inferOnly he.1).bind fun _ h =>
          (ensureForallCore.framed h).bind fun fType hf =>
          (inferType'.framed (e := a) inferOnly he.2).bind fun aType ha => ?_
        have hjp4 := (RecM.Framed.pure (R := GF G)
          (GF.instantiate1 (a := a) hf.bindingBody! he.2)).bind hjp2
        split
        · refine (RecM.Framed.withEager (RecM.Framed.isDefEq hf.bindingDomain! ha)).bind
            fun ok _ => ?_
          split
          · exact RecM.Framed.getEnv.bind fun _ _ => RecM.Framed.getLCtx_throw_bind
          · exact hjp4
        · refine (RecM.Framed.isDefEq hf.bindingDomain! ha).bind fun ok _ => ?_
          split
          · exact RecM.Framed.getEnv.bind fun _ _ => RecM.Framed.getLCtx_throw_bind
          · exact hjp4
    · exact (inferLet.framed he).bind hjp2

end Inner
end Lean4Lean.TypeChecker

import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Theory.Typing.ProjectionLemmas

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem reduceNative.WF :
    (reduceNative env e).WF fun oe => ∀ e₁, oe = some e₁ → False := by
  unfold reduceNative; split <;> [skip; exact .pure nofun]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure nofun]

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

def reduceBinNatOpG (guard : Nat → Nat → Prop) [DecidableRel guard]
    (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if guard v1 v2 then return none
  return some <| .lit <| .natVal <| f v1 v2

theorem reduceBinNatOpG.WF {guard} [DecidableRel guard] {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (reduceBinNatOpG guard f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOpG
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  split <;> [exact .pure nofun; rename_i h]
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatPred.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f) :
    RecM.WF c s (reduceBinNatPred f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := (heval ⟨_, h1⟩).2 v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun guard {g fc G} [DecidableRel guard] (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOpG guard g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOpG.WF he (hprims.2 hprim) heval
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natAdd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natSub
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMul
    apply hfun _ (by simp [prims]) c.hasPrimitives.natPow
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natGcd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMod
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natDiv
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLAnd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLOr
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natXor
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftLeft
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftRight
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.eqv_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩

theorem reduceProjCoreCont.WF (hc : c.TrExprS c₁ c')
    (hproj : c.HasType (.proj n i c') F) :
    RecM.WF c s (reduceProjCoreCont n i c₁) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow c₁ e₁ ∧ c.TrExpr e₁ (.proj n i c') := by
  unfold reduceProjCoreCont
  rw [Expr.withApp_eq]
  split <;> [rename_i mkC ls hmk; exact .pure nofun]
  refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hci => ?_
  split <;> [rename_i mkInfo; exact .pure nofun]
  split <;> [rename_i structInfo hfind; exact .pure nofun]
  split <;> [rename_i hsingle; exact .pure nofun]
  split <;> [rename_i harity; exact .pure nofun]
  refine .pure fun e₁ heq => ?_
  have hsingle := beq_iff_eq.1 hsingle
  have harity := beq_iff_eq.1 harity
  -- the constructor application spine
  have hc₁ : c.TrExprS ((Expr.const mkC ls).mkAppList c₁.getAppArgsList) c' := by
    rw [← hmk, c₁.mkAppList_getAppArgsList]; exact hc
  have ⟨fn', stk⟩ := AppStack.build hc₁
  have ⟨args', hargs, hc₁'⟩ := stk.translatedArguments
  have .const hfc hls hlen := stk.tr
  have hceq := hc₁.uniq c.Ewf (.refl c.Ewf c.Δwf) hc₁'
  -- the projection typing at the spine
  obtain ⟨info, ls₀, P₀, idx₀, sm, F', fl, hinfo, hls₀, huv₀, hP₀, hidx₀, hfield, hFty, hsm,
    hclosed, hguard⟩ := VEnv.HasType.proj_inv c.Ewf.ordered c.Δwf.toCtx hproj
  have hproj' : c.venv.IsDefEq c.lparams.length c.vlctx.toCtx (.proj n i c')
      (.proj n i (VExpr.mkApps (.const mkC _) args')) F' :=
    .projDF hinfo hls₀ huv₀ hP₀ hidx₀ hfield hFty hsm (hsm.transU_l c.Ewf c.Δwf.toCtx hceq)
      hclosed hguard
  have ⟨info', hinfo', hname, decl, doms, result, hwf, hctor, hshape, hvalid, hhead, hdn, hdu, hle,
    hnp, hnf, _⟩ := VContext.registryShape hfind hsingle hci
  obtain rfl := c.Ewf.ordered.projections_unique hinfo hinfo'
  subst hname
  -- the selected argument
  have hlenArgs : args'.length = doms.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hargs, ← Expr.getAppArgs_toList, Array.length_toList,
      harity, hnp, hnf]
    omega
  obtain ⟨e₁', hk', he₁'⟩ : ∃ e₁', args'[info.nparams + i]? = some e₁' ∧ c.TrExprS e₁ e₁' := by
    have hget : c₁.getAppArgsList[mkInfo.numParams + i]? = some e₁ := by
      rw [← Expr.getAppArgs_toList]; simpa [Array.getElem?_toList] using heq
    obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.1 hget
    refine ⟨args'[mkInfo.numParams + i]'(by rwa [← Lean4Lean.List.Forall₂.length_eq hargs]), ?_, ?_⟩
    · rw [← hnp]; exact List.getElem?_eq_getElem _
    · exact Lean4Lean.List.forall₂_getElem hargs _ h1 _
  -- typing of the field
  have hfieldTy := VEnv.VProjectionInfo.field_typing_of_ctorApp c.Ewf c.Δwf.toCtx hinfo hwf hctor
    hshape hvalid hhead hdn hdu hle i hproj'.hasType.2 hlenArgs hk'
  have hiota := VEnv.IsDefEq.projIota hinfo hproj'.hasType.2 hk' hfieldTy
  refine ⟨?_, e₁', he₁', ⟨_, (hproj'.trans hiota).symm⟩⟩
  -- the argument is a subterm of the constructor application
  intro P hP hfv
  have := (FVarsIn.mkAppList.1 (c₁.mkAppList_getAppArgsList ▸ hfv)).2
  exact this _ (List.mem_of_getElem? (by rw [← Expr.getAppArgs_toList]; simpa [Array.getElem?_toList] using heq))

theorem reduceProjCore.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProjCore n i e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  have .proj (e' := s') hs' hproj := he
  cases hproj with | direct majorWF targetWF
  obtain ⟨F, hF⟩ := targetWF
  -- retype the projection at the reduced structure
  obtain ⟨info, ls₀, P₀, idx₀, sm, F', fl, hinfo, hls₀, huv₀, hP₀, hidx₀, hfield, hFty, hsm,
    hclosed, hguard⟩ := VEnv.HasType.proj_inv c.Ewf.ordered c.Δwf.toCtx hF
  have main : ∀ {s : VState} (c₁ : Expr) (c₁' : VExpr), c.TrExprS c₁ c₁' → c.FVarsBelow e c₁ →
      c.IsDefEqU c₁' s' → RecM.WF c s (reduceProjCoreCont n i c₁) fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ (.proj n i s') := by
    intro s c₁ c₁' hc₁ h1 hdefeq
    have hproj' : c.venv.IsDefEq c.lparams.length c.vlctx.toCtx (.proj n i s') (.proj n i c₁') F' :=
      .projDF hinfo hls₀ huv₀ hP₀ hidx₀ hfield hFty hsm (hsm.transU_l c.Ewf c.Δwf.toCtx hdefeq.symm)
        hclosed hguard
    refine (reduceProjCoreCont.WF hc₁ hproj'.hasType.2).mono fun _ _ _ H e₁ heq => ?_
    have ⟨h2, h3⟩ := H e₁ heq
    exact ⟨fun P hP hfv => h2 P hP (h1 P hP hfv), h3.defeq c.Ewf c.Δwf ⟨_, hproj'.symm⟩⟩
  unfold reduceProjCore
  extract_lets jp
  split
  · have .lit _ hlit := hs'
    exact (whnf.WF hlit).bind fun c₁ _ _ ⟨h1, _, hc₁, hdefeq⟩ =>
      main c₁ _ hc₁ (FVarsBelow.trans (fun _ _ _ => FVarsIn.strLitToConstructor) h1) hdefeq
  · exact (RecM.WF.pure (Q := fun c₁ _ => c.FVarsBelow e c₁ ∧ c.TrExpr c₁ s')
      ⟨.rfl, hs'.trExpr c.Ewf c.Δwf⟩).bind fun c₁ _ _ ⟨h1, _, hc₁, hdefeq⟩ => main c₁ _ hc₁ h1 hdefeq

theorem reduceProj.WF (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj n i e cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceProj
  have .proj (e' := s) a1 a2 := he
  refine .bind (Q := fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ s) ?_ fun _ _ _ ⟨h1, h2⟩ => ?_
  · split <;> [exact whnfCore.WF a1; exact whnf.WF a1]
  have ⟨_, b1, b2⟩ := h2.proj c.Ewf c.Δwf a2
  refine (reduceProjCore.WF b1).mono fun _ _ _ H _ eq => ?_
  have ⟨c1, c2⟩ := H _ eq; exact ⟨h1.trans c1, c2.defeq c.Ewf c.Δwf b2⟩

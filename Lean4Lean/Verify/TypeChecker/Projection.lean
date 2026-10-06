import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.Typing.LevelEquiv

/-!
# The projection telescope walk

`inferProj` walks the constructor telescope of a structure, instantiating the parameter binders
with the parameters of the structure type and the field binders with projections of the major.
The lemmas here refine both executable walks by the syntactic instantiation
`VProjectionInfo.instantiateProjectionParameters` of the translated telescope: the executable
residual translates to the abstract residual. A field binder whose body has no loose bound
variables is kept without substitution by the executable; its translation is a lift, so the
substitution is a no-op on the abstract side.
-/

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

/-- The projections of `e'` at indices `position, …, position + m - 1`. -/
def projs (st : Name) (e' : VExpr) (position m : Nat) : List VExpr :=
  (List.range m).map fun j => .proj st (position + j) e'

@[simp] theorem projs_zero : projs st e' position 0 = [] := rfl

@[simp] theorem projs_length : (projs st e' position m).length = m := by simp [projs]

theorem projs_succ :
    projs st e' position (m + 1) = .proj st position e' :: projs st e' (position + 1) m := by
  simp only [projs, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 2
  funext j; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem instantiateProjectionParameters.WF_all {c : VContext} {args : Array Expr} :
    ∀ {remaining : Nat} {s : VState} {type : Expr} {ds : List VExpr} {b : VExpr} {position : Nat}
      {xs' : List VExpr},
    c.TrExprS type (VExpr.wrapForalls ds b) → ∀ (hle : remaining ≤ ds.length)
      (hlen : xs'.length = remaining),
    (∀ k (_hk : k < remaining), ∃ a, args[position + k]? = some a ∧
      c.TrExprS a (xs'[k]'(by omega))) →
    (∀ k (hk : k < remaining), ∃ D', VExpr.LEquiv c.lparams.length
      ((ds[k]'(by omega)).instOuter (xs'.take k)) D' ∧ c.HasType (xs'[k]'(by omega)) D') →
    (instantiateProjectionParameters type args position remaining).WF c s fun r _ =>
      ∀ t, r = some t → ((∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b) xs' = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type →
        (∀ k (hk : k < remaining) a, args[position + k]? = some a → FVarsIn P a) →
        FVarsIn P t) ∧
      ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        (∀ k (hk : k < remaining) a, args[position + k]? = some a →
          a.levelParamsIn Us = true ∧ FVarsIn P a) →
        t.levelParamsIn Us = true := by
  intro remaining
  induction remaining with
  | zero =>
    intro s type ds b position xs' hT _ hlen _ _
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact .pure fun t ht => by
      cases ht; exact ⟨⟨⟨_, rfl, hT⟩, fun _ _ h _ => h⟩, fun _ _ _ h _ _ => h⟩
  | succ remaining ih =>
    intro s type ds b position xs' hT hle hlen hargs hty
    cases ds with | nil => simp at hle | cons d ds' => ?_
    cases xs' with | nil => cases hlen | cons a' xs'' => ?_
    have hT' : c.TrExprS type (.forallE d (VExpr.wrapForalls ds' b)) := hT
    unfold instantiateProjectionParameters
    refine (whnf.WF_below' hT').bind fun e₁ _ _ H₁ => ?_
    obtain ⟨⟨hbe, -, hs⟩, hle₁⟩ := H₁
    have h₁ := hs _ _ rfl
    split <;> [skip; exact .pure nofun]
    rename_i n d₁ body bi
    let .forallE hd hW hd₁ hbody := h₁
    split <;> [skip; exact .pure nofun]
    rename_i a ha
    have ⟨a₀, ha₀, ha₀'⟩ := hargs 0 (Nat.succ_pos _)
    simp only [Nat.add_zero] at ha₀
    rw [ha] at ha₀; cases ha₀
    have ⟨D', hL, hD'⟩ := hty 0 (Nat.succ_pos _)
    simp only [List.take_zero, VExpr.instOuter_nil, List.getElem_cons_zero] at hL hD'
    have ⟨_, hd'⟩ := hd
    have hda : c.HasType a' d :=
      hD'.defeqU_r c.Ewf c.Δwf (hL.defeq c.Ewf c.Δwf.toCtx ⟨_, hd'⟩).symm
    have hinst := hbody.inst c.Ewf.ordered hda ha₀'
    rw [Expr.instantiate1_eq]
    have hT'' : c.TrExprS (body.instantiate1' a)
        (VExpr.wrapForalls (VExpr.instDomains ds' a' 0) (b.inst a' (0 + ds'.length))) := by
      rw [← VExpr.wrapForalls_inst]; exact hinst
    refine (ih hT'' (by simpa using Nat.le_of_succ_le_succ hle) (by simpa using hlen) ?_ ?_).mono
      fun r _ _ H t ht => ?_
    · intro k hk
      have ⟨a₁, h1, h2⟩ := hargs (k + 1) (Nat.succ_lt_succ hk)
      exact ⟨a₁, by rw [← h1]; congr 1; omega, h2⟩
    · intro k hk
      have ⟨D', h1, h2⟩ := hty (k + 1) (Nat.succ_lt_succ hk)
      refine ⟨D', ?_, h2⟩
      have hk' : k < xs''.length := by simp at hlen; omega
      rw [VExpr.instDomains_getElem _ _ _ _ (by simp at hle; omega), Nat.zero_add]
      simp only [List.getElem_cons_succ, List.take_succ_cons, VExpr.instOuter_cons,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt hk')] at h1
      exact h1
    · obtain ⟨⟨⟨R, hR, hR'⟩, hfv⟩, hlv⟩ := H t ht
      refine ⟨⟨⟨R, ?_, hR'⟩, fun P hP hfvt hfva => ?_⟩, fun Us P hsc hlt hfvt hla => ?_⟩
      · show VProjectionInfo.instantiateProjectionParameters
          (.forallE d (VExpr.wrapForalls ds' b)) (a' :: xs'') = some R
        simp only [VProjectionInfo.instantiateProjectionParameters, VExpr.wrapForalls_inst]
        exact hR
      · refine hfv P hP (FVarsIn.instantiate1 (hbe P hP hfvt).2 (hfva 0 (Nat.succ_pos _) a ?_))
          fun k hk a₁ h => hfva (k + 1) (Nat.succ_lt_succ hk) a₁ (by rw [← h]; congr 1; omega)
        simpa using ha
      · have ha0 := hla 0 (Nat.succ_pos _) a (by simpa using ha)
        have hb₁ := hle₁ Us P hsc hlt hfvt
        simp only [Expr.levelParamsIn, Bool.and_eq_true] at hb₁
        refine hlv Us P hsc (Expr.levelParamsIn_instantiate1 hb₁.2 ha0.1)
          (FVarsIn.instantiate1 (hbe P hsc.1 hfvt).2 ha0.2)
          fun k hk a₁ h => hla (k + 1) (Nat.succ_lt_succ hk) a₁ (by rw [← h]; congr 1; omega)

theorem instantiateProjectionParameters.WF {c : VContext} {args : Array Expr}
    {remaining : Nat} {s : VState} {type : Expr} {ds : List VExpr} {b : VExpr} {position : Nat}
    {xs' : List VExpr}
    (hT : c.TrExprS type (VExpr.wrapForalls ds b)) (hle : remaining ≤ ds.length)
    (hlen : xs'.length = remaining)
    (hargs : ∀ k (_hk : k < remaining), ∃ a, args[position + k]? = some a ∧
      c.TrExprS a (xs'[k]'(by omega)))
    (hty : ∀ k (hk : k < remaining), ∃ D', VExpr.LEquiv c.lparams.length
      ((ds[k]'(by omega)).instOuter (xs'.take k)) D' ∧ c.HasType (xs'[k]'(by omega)) D') :
    (instantiateProjectionParameters type args position remaining).WF c s fun r _ =>
      ∀ t, r = some t → (∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b) xs' = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type →
        (∀ k (hk : k < remaining) a, args[position + k]? = some a → FVarsIn P a) →
        FVarsIn P t :=
  (instantiateProjectionParameters.WF_all hT hle hlen hargs hty).mono
    fun _ _ _ H t ht => (H t ht).1

theorem instantiateProjectionFields.WF_all {c : VContext} {G : VLevel → Prop}
    (he : c.TrExprS struct e') (hmaj : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx e')
    (hG0 : G .zero) (hG : maybePropType = false → ∀ u, G u) :
    ∀ {remaining : Nat} {s : VState} {type : Expr} {ds : List VExpr} {b : VExpr} {position : Nat},
    c.TrExprS type (VExpr.wrapForalls ds b) → ∀ (hle : remaining ≤ ds.length),
    (∀ m (hm : m < remaining) u,
      c.HasType ((ds[m]'(by omega)).instOuter (projs st e' position m)) (.sort u) → G u →
      c.HasType (.proj st (position + m) e')
        ((ds[m]'(by omega)).instOuter (projs st e' position m))) →
    (instantiateProjectionFields st struct maybePropType type position remaining).WF c s
      fun r _ => ∀ t, r = some t → ((∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b)
          (projs st e' position remaining) = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
      ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        struct.levelParamsIn Us = true → FVarsIn P struct → t.levelParamsIn Us = true := by
  intro remaining
  induction remaining with
  | zero =>
    intro s type ds b position hT _ _
    exact .pure fun t ht => by
      cases ht; exact ⟨⟨⟨_, rfl, hT⟩, fun _ _ h _ => h⟩, fun _ _ _ h _ _ _ => h⟩
  | succ remaining ih =>
    intro s type ds b position hT hle hproj
    cases ds with | nil => simp at hle | cons d ds' => ?_
    have hT' : c.TrExprS type (.forallE d (VExpr.wrapForalls ds' b)) := hT
    unfold instantiateProjectionFields
    refine (whnf.WF_below' hT').bind fun e₁ _ _ H₁ => ?_
    obtain ⟨⟨hbe, -, hs⟩, hle₁⟩ := H₁
    have h₁ := hs _ _ rfl
    split <;> [skip; exact .pure nofun]
    rename_i n d₁ body bi
    let .forallE hd hW hd₁ hbody := h₁
    have hbl : ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
        d₁.levelParamsIn Us = true ∧ body.levelParamsIn Us = true := fun Us P hsc hlt hfvt => by
      have := hle₁ Us P hsc hlt hfvt
      simpa only [Expr.levelParamsIn, Bool.and_eq_true] using this
    -- the continuation: the walk on the rest of the telescope
    have cont : ∀ {s : VState} (type' : Expr),
        c.TrExprS type' ((VExpr.wrapForalls ds' b).inst (.proj st position e')) →
        (∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P type') →
        (∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
          struct.levelParamsIn Us = true → FVarsIn P struct → type'.levelParamsIn Us = true) →
        RecM.WF c s (instantiateProjectionFields st struct maybePropType type' (position + 1)
          remaining) fun r _ => ∀ t, r = some t → ((∃ R,
          VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls (d :: ds') b)
            (projs st e' position (remaining + 1)) = some R ∧ c.TrExprS t R) ∧
          ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
          ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
            struct.levelParamsIn Us = true → FVarsIn P struct → t.levelParamsIn Us = true := by
      intro s type' hT'' hfv' hlv'
      rw [VExpr.wrapForalls_inst] at hT''
      refine (ih hT'' (by simpa using Nat.le_of_succ_le_succ hle) ?_).mono fun r _ _ H t ht => ?_
      · intro m hm u
        have hm' : m < ds'.length := by simp at hle; omega
        have E : ((VExpr.instDomains ds' (.proj st position e') 0)[m]'(by simpa using hm')).instOuter
              (projs st e' (position + 1) m) =
            (ds'[m]'hm').instOuter (projs st e' position (m + 1)) := by
          rw [VExpr.instDomains_getElem _ _ _ _ hm', projs_succ,
            VExpr.instOuter_cons, projs_length, Nat.zero_add]
        rw [E, show position + 1 + m = position + (m + 1) by omega]
        exact hproj (m + 1) (Nat.succ_lt_succ hm) u
      · obtain ⟨⟨⟨R, hR, hR'⟩, hfv⟩, hlv⟩ := H t ht
        refine ⟨⟨⟨R, ?_, hR'⟩, fun P hP hfvt hfvs => hfv P hP (hfv' P hP hfvt hfvs) hfvs⟩,
          fun Us P hsc hlt hfvt hls hfvs =>
            hlv Us P hsc (hlv' Us P hsc hlt hfvt hls hfvs) (hfv' P hsc.1 hfvt hfvs) hls hfvs⟩
        rw [projs_succ]
        show VProjectionInfo.instantiateProjectionParameters (.forallE d (VExpr.wrapForalls ds' b))
          (_ :: _) = some R
        simp only [VProjectionInfo.instantiateProjectionParameters, VExpr.wrapForalls_inst]
        exact hR
    -- typing of the projection at the current binder, from the sort of the domain
    have hp0 : ∀ u, c.HasType d (.sort u) → G u → c.HasType (.proj st position e') d := by
      intro u hu hGu
      have := hproj 0 (Nat.succ_pos _) u (by simpa using hu) hGu
      simpa using this
    split
    · -- the body depends on the field: substitute the projection
      have main {s : VState} (hp : c.HasType (.proj st position e') d) :
          RecM.WF c s (instantiateProjectionFields st struct maybePropType
            (body.instantiate1 (.proj st position struct)) (position + 1) remaining)
            fun r _ => ∀ t, r = some t → ((∃ R,
              VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls (d :: ds') b)
                (projs st e' position (remaining + 1)) = some R ∧ c.TrExprS t R) ∧
              ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t) ∧
              ∀ Us P, c.UniverseScope Us P → type.levelParamsIn Us = true → FVarsIn P type →
                struct.levelParamsIn Us = true → FVarsIn P struct →
                t.levelParamsIn Us = true := by
        have hp_tr : c.TrExprS (.proj st position struct) (.proj st position e') :=
          .proj he (.direct hmaj ⟨_, hp⟩)
        rw [Expr.instantiate1_eq]
        exact cont _ (hbody.inst c.Ewf.ordered hp hp_tr)
          (fun P hP hfvt hfvs => FVarsIn.instantiate1 (hbe P hP hfvt).2 hfvs)
          fun Us P hsc hlt hfvt hls _ =>
            Expr.levelParamsIn_instantiate1 (hbl Us P hsc hlt hfvt).2 hls
      split
      · rename_i hmp
        refine (isProp.WF hd₁).bind fun bp _ _ hbp => ?_
        split <;> [skip; exact .pure nofun]
        rename_i hbp'
        exact main (hp0 .zero (hbp (by simpa using hbp')) hG0)
      · rename_i hmp
        have ⟨u, hu⟩ := hd
        exact main (hp0 u hu (hG (by simpa using hmp) u))
    · -- the body does not depend on the field: its translation is a lift
      rename_i hnl
      have hc : Closed body := by
        refine Closed.of_closed_looseBVarRange hbody.closed ?_
        simpa [Expr.hasLooseBVars] using hnl
      obtain ⟨b₀, hb₀, hWeq⟩ := hbody.weakBV_inv₁ c.Ewf ⟨c.Δwf, nofun, hd⟩ hc
      refine cont _ ?_ (fun P hP hfvt _ => (hbe P hP hfvt).2)
        fun Us P hsc hlt hfvt _ _ => (hbl Us P hsc hlt hfvt).2
      rw [hWeq, VExpr.inst_lift]; exact hb₀

theorem instantiateProjectionFields.WF {c : VContext} {G : VLevel → Prop}
    (he : c.TrExprS struct e') (hmaj : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx e')
    (hG0 : G .zero) (hG : maybePropType = false → ∀ u, G u)
    {remaining : Nat} {s : VState} {type : Expr} {ds : List VExpr} {b : VExpr} {position : Nat}
    (hT : c.TrExprS type (VExpr.wrapForalls ds b)) (hle : remaining ≤ ds.length)
    (hproj : ∀ m (hm : m < remaining) u,
      c.HasType ((ds[m]'(by omega)).instOuter (projs st e' position m)) (.sort u) → G u →
      c.HasType (.proj st (position + m) e')
        ((ds[m]'(by omega)).instOuter (projs st e' position m))) :
    (instantiateProjectionFields st struct maybePropType type position remaining).WF c s
      fun r _ => ∀ t, r = some t → (∃ R,
        VProjectionInfo.instantiateProjectionParameters (VExpr.wrapForalls ds b)
          (projs st e' position remaining) = some R ∧
        c.TrExprS t R) ∧
      ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P type → FVarsIn P struct → FVarsIn P t :=
  (instantiateProjectionFields.WF_all he hmaj hG0 hG hT hle hproj).mono
    fun _ _ _ H t ht => (H t ht).1

end Lean4Lean.TypeChecker.Inner

import Lean4Lean.Verify.Typing.Telescope

/-! # Translation context lemmas

Lemmas about `VLCtx`: keys, free variables, lambda-only contexts, context conversion
(`VLCtx.IsDefEq`) and universe instantiation.
-/

namespace Lean4Lean
open Lean hiding Environment Exception

theorem VLCtx.WF.instL_id (H : VLCtx.WF env U Δ) :
    Δ.instL (VLevel.params U) = Δ := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    have hctx := OnCtx.levelWF_of_isType H.1.toCtx
    have htail := ih H.1
    cases d with
    | vlam ty =>
      obtain ⟨level, htype⟩ := H.2.2
      have hlevels := (htype.levelWF hctx).1
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.instL_id]
    | vlet ty value =>
      have hlevels := H.2.2.levelWF hctx
      simp [VLCtx.instL, VLocalDecl.instL, htail, hlevels.1.instL_id, hlevels.2.2.instL_id]

theorem VLCtx.instL_instL {Δ : VLCtx} :
    (Δ.instL ls).instL ls' = Δ.instL (ls.map (VLevel.inst ls')) := by
  induction Δ with
  | nil => rfl
  | cons entry Δ ih =>
    obtain ⟨ofv, d⟩ := entry
    cases d <;> simp [VLCtx.instL, VLocalDecl.instL, ih, VExpr.instL_instL]

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

section ScopeAlignment
variable {env : VEnv} {Us : List Name} {scope chk : VLCtx}

/-- Extend an alignment by a free-variable binder whose two domains are
definitionally equal. -/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.consAligned
    (h : VLCtx.IsDefEq env Us.length scope chk)
    (hfresh : fv ∉ scope.fvars) (hdeps : deps ⊆ scope.fvars)
    (hA : env.IsDefEq Us.length scope.toCtx A A₀ (.sort u)) :
    VLCtx.IsDefEq env Us.length ((some (fv, deps), .vlam A) :: scope)
      ((some (fv, deps), .vlam A₀) :: chk) :=
  .cons h (by rintro _ _ ⟨⟩; exact ⟨hfresh, hdeps⟩) (.vlam hA)

end ScopeAlignment

/-- The checker-context normal form of an opened body, read back in a scope
aligned with the checker context: the scope translation of the source body
is definitionally equal to it. -/
theorem _root_.Lean4Lean.VLCtx.IsDefEq.openedNormalForm {env : VEnv} {Us : List Name}
    {scope chk : VLCtx} (henv : env.WF)
    (halign : VLCtx.IsDefEq env Us.length scope chk)
    {indexType consumed₀ : VExpr} {u : VLevel}
    (hindex : env.IsDefEq Us.length scope.toCtx indexType consumed₀ (.sort u))
    (hfresh : ∀ fv deps, ofv = some (fv, deps) → fv ∉ scope.fvars ∧ deps ⊆ scope.fvars)
    {body : Expr} {narrowBody consumedBody₀ : VExpr}
    (hbodyNarrow : TrExprS env Us ((none, .vlam indexType) :: scope) body narrowBody)
    (hbodyConsumed₀ : TrExprS env Us ((none, .vlam consumed₀) :: chk) body consumedBody₀)
    {normalized : Expr} {normalizedC : VExpr}
    (hnormalizedC : TrExprS env Us ((ofv, .vlam consumed₀) :: chk) normalized normalizedC)
    (hnormalizedCEq : env.IsDefEqU Us.length (consumed₀ :: chk.toCtx)
      normalizedC consumedBody₀) :
    ∃ normalizedNarrow,
      TrExprS env Us ((ofv, .vlam indexType) :: scope) normalized normalizedNarrow ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx) narrowBody normalizedNarrow := by
  have halign' : VLCtx.IsDefEq env Us.length ((ofv, .vlam indexType) :: scope)
      ((ofv, .vlam consumed₀) :: chk) := .cons halign hfresh (.vlam hindex)
  obtain ⟨normalizedNarrow, hnormalizedNarrow⟩ :=
    hnormalizedC.defeqDFC henv (halign'.symm henv.orderedStrong)
  have hnn := hnormalizedNarrow.uniq henv halign' hnormalizedC
  have hctxB : VLCtx.IsDefEq env Us.length ((none, .vlam indexType) :: scope)
      ((none, .vlam consumed₀) :: chk) := .cons halign nofun (.vlam hindex)
  have hbodyU := hbodyNarrow.uniq henv hctxB hbodyConsumed₀
  have hnormC : env.IsDefEqU Us.length (indexType :: scope.toCtx)
      normalizedC consumedBody₀ :=
    hnormalizedCEq.defeqDFC henv.ordered (hctxB.symm henv.orderedStrong).defeqCtx
  have hΓ' : OnCtx (indexType :: scope.toCtx) (env.IsType Us.length) :=
    ⟨halign.wf.toCtx, _, hindex.hasType.1⟩
  have h1 : env.IsDefEqU Us.length (indexType :: scope.toCtx)
      normalizedNarrow normalizedC := hnn
  exact ⟨normalizedNarrow, hnormalizedNarrow,
    hbodyU.trans henv hΓ' (hnormC.symm.trans henv hΓ' h1.symm)⟩

end VerifyInductive

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem VLCtx.instL_abstractForallContext_nil (domains : List VExpr) (levels : List VLevel) :
    (abstractForallContext domains []).instL levels =
      abstractForallContext (domains.map (VExpr.instL levels)) [] := by
  rw [VLCtx.instL_abstractForallContext]
  rfl

end Lean4Lean.VerifyInductive

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Two lambda contexts with the same binder keys and definitionally equal
domains are aligned. -/
theorem VLCtx.IsDefEq.ofKeysCtx {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : VLCtx}, Δ₁.map Prod.fst = Δ₂.map Prod.fst →
      (∀ e ∈ Δ₁, ∃ k d, e = (k, .vlam d)) →
      (∀ e ∈ Δ₂, ∃ k d, e = (k, .vlam d)) →
      VLCtx.WF env U Δ₁ →
      VEnv.IsDefEqCtx env U [] Δ₁.toCtx Δ₂.toCtx →
      VLCtx.IsDefEq env U Δ₁ Δ₂
  | [], [], _, _, _, _, _ => .nil
  | [], _ :: _, h, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _ => by simp at h
  | e₁ :: t₁, e₂ :: t₂, hk, h1, h2, hwf, hctx => by
    obtain ⟨k₁, a, rfl⟩ := h1 e₁ (by simp)
    obtain ⟨k₂, b, rfl⟩ := h2 e₂ (by simp)
    simp only [List.map_cons, List.cons.injEq] at hk
    obtain ⟨rfl, hk'⟩ := hk
    have hctx' : VEnv.IsDefEqCtx env U [] (a :: VLCtx.toCtx t₁) (b :: VLCtx.toCtx t₂) := by
      simpa [VLCtx.toCtx] using hctx
    cases hctx' with
    | succ htail hab =>
      exact .cons (VLCtx.IsDefEq.ofKeysCtx hk'
        (fun e he => h1 e (by simp [he])) (fun e he => h2 e (by simp [he]))
        hwf.1 htail) hwf.2.1 (.vlam hab)

theorem VLCtx.IsDefEq.keys_eq {env : VEnv} {U : Nat} :
    ∀ {Δ₁ Δ₂ : VLCtx}, VLCtx.IsDefEq env U Δ₁ Δ₂ → Δ₁.map Prod.fst = Δ₂.map Prod.fst
  | _, _, .nil => rfl
  | _, _, .cons h _ _ => by simp [VLCtx.IsDefEq.keys_eq h]

theorem VLCtx.FVLift'.keys_sublist {Δ Δ' : VLCtx} {dk k : Nat} {n : Lift}
    (W : VLCtx.FVLift' Δ Δ' dk n k) : Δ.map Prod.fst <+ Δ'.map Prod.fst := by
  induction W with
  | refl => exact .refl _
  | skip_fvar _ _ _ ih => exact .cons _ ih
  | cons_fvar _ _ _ _ ih => exact .cons_cons _ ih
  | cons_bvar _ _ ih => exact .cons_cons _ ih

theorem VLCtx.mem_fvars_of_key : ∀ {L : VLCtx} {fv : FVarId} {d : List FVarId},
    some (fv, d) ∈ L.map Prod.fst → fv ∈ L.fvars
  | [], _, _, h => by simp at h
  | (none, _) :: L, _, _, h => by
    simp only [List.map_cons, List.mem_cons, reduceCtorEq, false_or] at h
    exact VLCtx.mem_fvars_of_key (L := L) h
  | (some (fv', d'), _) :: L, fv, d, h => by
    simp only [List.map_cons, List.mem_cons, Option.some.injEq, Prod.mk.injEq] at h
    simp only [VLCtx.fvars_cons_some, List.mem_cons]
    rcases h with ⟨rfl, _⟩ | h
    · exact Or.inl rfl
    · exact Or.inr (VLCtx.mem_fvars_of_key h)

/-- In a context with distinct free variables, a free variable determines
its declaration key. -/
theorem VLCtx.key_unique : ∀ {L : VLCtx}, L.fvars.Nodup →
    ∀ {fv : FVarId} {d₁ d₂ : List FVarId},
      some (fv, d₁) ∈ L.map Prod.fst → some (fv, d₂) ∈ L.map Prod.fst → d₁ = d₂
  | [], _, _, _, _, h, _ => by simp at h
  | (none, _) :: L, hnd, _, _, _, h1, h2 => by
    simp only [List.map_cons, List.mem_cons, reduceCtorEq, false_or] at h1 h2
    exact VLCtx.key_unique (L := L) hnd h1 h2
  | (some (fv', d'), _) :: L, hnd, fv, d₁, d₂, h1, h2 => by
    simp only [VLCtx.fvars_cons_some, List.nodup_cons] at hnd
    simp only [List.map_cons, List.mem_cons, Option.some.injEq, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨h2a, rfl⟩ | h2
    · rfl
    · exact absurd (VLCtx.mem_fvars_of_key h2) hnd.1
    · exact absurd (h2a ▸ VLCtx.mem_fvars_of_key h1) hnd.1
    · exact VLCtx.key_unique hnd.2 h1 h2

/-- Two selections of free-variable keys from one context agree when they
select the same free variables. -/
theorem VLCtx.keys_eq_of_fvars {L : VLCtx} (hnd : L.fvars.Nodup) :
    ∀ {A B : List (Option (FVarId × List FVarId))},
      (∀ x ∈ A, x ∈ L.map Prod.fst) → (∀ x ∈ B, x ∈ L.map Prod.fst) →
      (∀ x ∈ A, x.isSome) → (∀ x ∈ B, x.isSome) →
      A.map (Option.map Prod.fst) = B.map (Option.map Prod.fst) → A = B
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | a :: A, b :: B, hA, hB, sA, sB, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hab, hrest⟩ := h
    have ha := sA a (by simp)
    have hb := sB b (by simp)
    obtain ⟨⟨fa, da⟩, rfl⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨⟨fb, db⟩, rfl⟩ := Option.isSome_iff_exists.mp hb
    simp only [Option.map_some, Option.some.injEq] at hab
    subst hab
    have hd : da = db :=
      VLCtx.key_unique hnd (hA (some (fa, da)) (by simp)) (hB (some (fa, db)) (by simp))
    subst hd
    congr 1
    exact VLCtx.keys_eq_of_fvars hnd (fun x hx => hA x (by simp [hx]))
      (fun x hx => hB x (by simp [hx])) (fun x hx => sA x (by simp [hx]))
      (fun x hx => sB x (by simp [hx])) hrest

theorem VLCtx.lams_of_declarations {fvs : List FVarId} {L : VLCtx}
    (H : List.Forall₂ (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), VLocalDecl.vlam type)) fvs L) :
    ∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d) := by
  induction H with
  | nil => simp
  | cons h _ ih =>
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · obtain ⟨deps, type, rfl⟩ := h
      exact ⟨_, _, rfl⟩
    · exact ih e he

theorem VLCtx.fvars_drop_of_lams : ∀ {L : VLCtx} (m : Nat),
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      VLCtx.fvars (L.drop m) = L.fvars.drop m
  | [], m, _ => by simp
  | _ :: _, 0, _ => rfl
  | e :: L, m + 1, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp only [List.drop_succ_cons, VLCtx.fvars_cons_some]
    exact VLCtx.fvars_drop_of_lams m (fun x hx => h x (by simp [hx]))

theorem VLCtx.toCtx_length_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      L.toCtx.length = L.length
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.toCtx, VLCtx.toCtx_length_of_lams (L := L)
      (fun x hx => h x (by simp [hx]))]

theorem VLCtx.fvars_length_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      L.fvars.length = L.length
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.fvars_length_of_lams (L := L) (fun x hx => h x (by simp [hx]))]

theorem VLCtx.keys_fvars_of_lams : ∀ {L : VLCtx},
    (∀ e ∈ L, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      (L.map Prod.fst).map (Option.map Prod.fst) = L.fvars.map some
  | [], _ => rfl
  | e :: L, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    simp [VLCtx.keys_fvars_of_lams (L := L) (fun x hx => h x (by simp [hx]))]

theorem VLCtx.FVLift.of_append_lams : ∀ (X : VLCtx) {Q : VLCtx},
    (∀ e ∈ X, ∃ k d, e = (some k, VLocalDecl.vlam d)) →
      VLCtx.FVLift Q (X ++ Q) 0 X.length 0
  | [], _, _ => .refl
  | e :: X, Q, h => by
    obtain ⟨k, d, rfl⟩ := h e (by simp)
    have W := VLCtx.FVLift.of_append_lams X (Q := Q)
      (fun x hx => h x (by simp [hx]))
    exact .skip_fvar k (.vlam d) W

end VerifyInductive

end Lean4Lean

import Lean4Lean.Theory.Typing.NativePrefixArity
import Lean4Lean.Theory.Typing.NativeSingletonProgram

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

def prefixArguments (data : NativeRecursorData) (args : List VExpr) : List VExpr :=
  let remaining := data.majorOffset + 1 - args.length
  args.map (·.liftN remaining) ++ vars remaining 0

/-- The fields reconstructed by the singleton program at the supplied arguments. -/
noncomputable def singletonFields (data : NativeRecursorData) (S : CastSpec) (E : PropElim)
    (levels : List VLevel) (args : List VExpr) : List VExpr :=
  (PropElim.occ S (data.propParams levels) E ((data.prefixArguments args).take data.numParams)
    (((data.prefixArguments args).drop data.indexOffset).take data.numIndices) (.bvar 0)
    S.fields.length).2

theorem singletonProgram_layout {data : NativeRecursorData} {env : VEnv}
    (H : data.singletonProgram env U levels args = some program) :
    ∃ S E, data.castSpec env levels = some S ∧ data.propElim levels = some E ∧
      program.domains.length = data.majorOffset + 1 - args.length ∧
      program.constructor = VExpr.mkApps E.ctor
        ((data.prefixArguments args).take data.numParams ++ data.singletonFields S E levels args) ∧
      program.captures = (data.prefixArguments args).take data.indexOffset ++
        data.singletonFields S E levels args := by
  unfold singletonProgram at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, residual, _, ⟨domains, result⟩, htake,
    ⟨ctor, fields⟩, hrecon, equation, heq, body, hbody, H⟩ := H
  split at H <;> try contradiction
  cases H
  unfold singletonRecon at hrecon
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hrecon
  obtain ⟨S, hS, E, hE, hctor, hfields⟩ := hrecon
  refine ⟨S, E, hS, hE, takeForalls_length htake, ?_, ?_⟩
  · rw [← hctor, ← hfields]; rfl
  · rw [← hfields]; rfl

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem mkApps_arguments_wf (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    VExpr.WF env U Γ fn ∧ ∀ arg ∈ args, VExpr.WF env U Γ arg := by
  induction args generalizing fn with
  | nil => exact ⟨H, by simp⟩
  | cons a args ih =>
    obtain ⟨hf, hargs⟩ := ih H
    obtain ⟨_, _, hf', ha⟩ := hf.app_inv henv.ordered hΓ
    refine ⟨⟨_, hf'⟩, ?_⟩
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact hargs arg hm

private theorem rel_getD_typed {R : VExpr → VExpr → Prop} {l l' : List VExpr} {P : VExpr → Prop}
    (H : List.Forall₂ R l l') (hd : P default → R default default) (k : Nat)
    (hp : P (l.getD k default)) : R (l.getD k default) (l'.getD k default) := by
  induction H generalizing k with
  | nil => exact hd hp
  | cons h _ ih => cases k with
    | zero => exact h
    | succ k => exact ih k hp

private theorem forall₂_of_cond {R : VExpr → VExpr → Prop} {P : VExpr → Prop} {l l' : List VExpr}
    (H : List.Forall₂ (fun e e' => P e → R e e') l l') (hp : ∀ e ∈ l, P e) :
    List.Forall₂ R l l' := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h (hp _ (by simp))) (ih fun e he => hp e (by simp [he]))

private theorem rel_take' {R : VExpr → VExpr → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.take n) (b.take n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

private theorem rel_drop' {R : VExpr → VExpr → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.drop n) (b.drop n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .cons h hs
    | succ n => exact ih n

private theorem rel_append' {R : VExpr → VExpr → Prop} (H : List.Forall₂ R a b)
    (H' : List.Forall₂ R a' b') : List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h _ ih => exact .cons h ih

/-- The singleton reconstruction transports along any relation of its arguments
that is a typed congruence: every reconstructed term that is typed is related. -/
theorem occ_rel {R : VExpr → VExpr → Prop} (henv : env.WF) (hΔ : OnCtx Δ (env.IsType U))
    (refl : ∀ {e A}, HasType env U Δ e A → R e e)
    (mkApps : ∀ {f f' as as' T}, R f f' → List.Forall₂ R as as' →
      HasType env U Δ (VExpr.mkApps f as) T → R (VExpr.mkApps f as) (VExpr.mkApps f' as'))
    (inst : ∀ {cs cs' e T}, List.Forall₂ R cs cs' →
      HasType env U Δ (instantiateParams e cs) T → R (instantiateParams e cs) (instantiateParams e cs'))
    (hps : List.Forall₂ R ps ps') (hidx : List.Forall₂ R idx idx') :
    ∀ i, List.Forall₂ (fun e e' => VExpr.WF env U Δ e → R e e')
        (PropElim.occ S P E ps idx m i).1 (PropElim.occ S P E ps' idx' m i).1 ∧
      List.Forall₂ (fun e e' => VExpr.WF env U Δ e → R e e')
        (PropElim.occ S P E ps idx m i).2 (PropElim.occ S P E ps' idx' m i).2 := by
  intro i
  induction i with
  | zero => exact ⟨.nil, .nil⟩
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [PropElim.occ]
    split
    · rename_i k _
      refine ⟨rel_append' ih1 (.cons ?_ .nil), rel_append' ih2 (.cons ?_ .nil)⟩
      · rintro ⟨_, ht⟩
        have hw := mkApps_arguments_wf (fn := .const ``Eq.refl _) (args := [_, _]) henv hΔ ⟨_, ht.hasType.1⟩
        obtain ⟨_, hhead⟩ := hw.1
        obtain ⟨_, hα⟩ := hw.2 _ (List.mem_cons_self ..)
        obtain ⟨_, hX⟩ := hw.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        refine mkApps (f := .const ``Eq.refl _) (as := [_, _]) (refl hhead.hasType.1)
          (.cons (refl hα.hasType.1) (.cons ?_ .nil)) ht.hasType.1
        have hX' := hX.hasType.1
        rw [← instantiateParams_eq_instOuter] at hX' ⊢
        rw [← instantiateParams_eq_instOuter]
        exact inst (rel_append' hps (rel_take' hidx k)) hX'
      · intro hw
        exact rel_getD_typed (P := VExpr.WF env U Δ) hidx
          (fun ⟨_, h⟩ => refl h.hasType.1) k hw
    · have hnew : (fun e e' => VExpr.WF env U Δ e → R e e')
          (VExpr.mkApps (PropElim.value S P E i) (ps ++ idx ++ [m] ++ (PropElim.occ S P E ps idx m i).1))
          (VExpr.mkApps (PropElim.value S P E i) (ps' ++ idx' ++ [m] ++ (PropElim.occ S P E ps' idx' m i).1)) := by
        rintro ⟨_, ht⟩
        have hw := mkApps_arguments_wf henv hΔ ⟨_, ht.hasType.1⟩
        refine mkApps (refl hw.1.choose_spec.hasType.1) ?_ ht.hasType.1
        refine rel_append' (rel_append' (rel_append' hps hidx)
          (.cons (refl (hw.2 m (by simp)).choose_spec.hasType.1) .nil)) ?_
        exact forall₂_of_cond ih1 fun e he => hw.2 e (by simp [he])
      exact ⟨rel_append' ih1 (.cons hnew .nil), rel_append' ih2 (.cons hnew .nil)⟩


open NativeRecursorData in
/-- Related supplied arguments give related singleton captures and constructors,
for any typed congruence relation closed under weakening. -/
theorem NativePrefixReplay.singleton_rel_components {R : List VExpr → VExpr → VExpr → Prop}
    (refl : ∀ {Γ e A}, OnCtx Γ (env.IsType U) → HasType env U Γ e A → R Γ e e)
    (weakN : ∀ {n k Γ Γ' a b}, Ctx.LiftN n k Γ Γ' → R Γ a b → R Γ' (a.liftN n k) (b.liftN n k))
    (mkApps : ∀ {Γ f f' as as' T}, OnCtx Γ (env.IsType U) → R Γ f f' →
      List.Forall₂ (R Γ) as as' → HasType env U Γ (VExpr.mkApps f as) T →
      R Γ (VExpr.mkApps f as) (VExpr.mkApps f' as'))
    (inst : ∀ {Γ cs cs' e T}, OnCtx Γ (env.IsType U) →
      List.Forall₂ (R Γ) cs cs' → HasType env U Γ (instantiateParams e cs) T →
      R Γ (instantiateParams e cs) (instantiateParams e cs'))
    {data : NativeRecursorData} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : NativePrefixReplay env U Γ (VExpr.mkApps (.const data.name levels) args) program)
    (hg : data.singletonProgram env U levels args = some program)
    (hg' : data.singletonProgram env U levels args' = some program')
    (ha : List.Forall₂ (R Γ) args args') :
    List.Forall₂ (R (program.domains.reverse ++ Γ)) program.captures program'.captures ∧
      R (program.domains.reverse ++ Γ) program.constructor program'.constructor := by
  obtain ⟨S, E, hS, hE, hlen, hctor, hcapture⟩ := singletonProgram_layout hg
  obtain ⟨S', E', hS', hE', hlen', hctor', hcapture'⟩ := singletonProgram_layout hg'
  cases hS.symm.trans hS'
  cases hE.symm.trans hE'
  have halen := Lean4Lean.List.Forall₂.length_eq ha
  have hctx := (IsType.wrapForalls_inv henv hΓ (H.source_typed.isType henv hΓ)).1
  have W : Ctx.LiftN (data.majorOffset + 1 - args.length) 0 Γ (program.domains.reverse ++ Γ) :=
    .zero _ (by simpa only [List.length_reverse] using hlen)
  have hall : List.Forall₂ (R (program.domains.reverse ++ Γ))
      (data.prefixArguments args) (data.prefixArguments args') := by
    unfold prefixArguments
    rw [← halen]
    apply rel_append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.imp (fun _ _ h => weakN W h) ha
    · apply Lean4Lean.List.Forall₂.rfl
      intro e he
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      have hi' : 0 + i < (program.domains.reverse ++ Γ).length := by
        simp only [List.length_append, List.length_reverse]; omega
      exact refl hctx (.bvar (Lookup.ofLt hi').2)
  have hdrop : ∀ n, List.Forall₂ (R (program.domains.reverse ++ Γ))
      ((data.prefixArguments args).drop n) ((data.prefixArguments args').drop n) :=
    fun n => rel_drop' hall n
  have hocc := occ_rel (R := R (program.domains.reverse ++ Γ)) (P := data.propParams levels)
    (S := S) (E := E) (m := .bvar 0) henv hctx (refl hctx) (mkApps hctx) (inst hctx)
    (rel_take' hall data.numParams) (rel_take' (hdrop data.indexOffset) data.numIndices)
    S.fields.length
  have hfieldsTyped : ∀ e ∈ data.singletonFields S E levels args,
      VExpr.WF env U (program.domains.reverse ++ Γ) e := by
    intro e he
    have hmem : e ∈ program.captures := by rw [hcapture]; exact List.mem_append_right _ he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    exact ⟨_, H.captures_typed i hi (by rw [← H.captures_length]; exact hi)⟩
  have hfields : List.Forall₂ (R (program.domains.reverse ++ Γ))
      (data.singletonFields S E levels args) (data.singletonFields S E levels args') :=
    forall₂_of_cond hocc.2 hfieldsTyped
  constructor
  · rw [hcapture, hcapture']
    exact rel_append' (rel_take' hall _) hfields
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    rw [hctor] at hc
    rw [hctor, hctor']
    have hw := mkApps_arguments_wf henv hctx ⟨_, hc⟩
    exact mkApps hctx (refl hctx hw.1.choose_spec.hasType.1)
      (rel_append' (rel_take' hall _) hfields) hc

end Lean4Lean.VEnv

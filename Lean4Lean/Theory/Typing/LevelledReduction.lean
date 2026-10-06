import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.LevelledConfluence

/-! # Levelled parallel relations for the full presentation

The full step relation is split into four parallel relations, ordered by
level for the decreasing-diagram criterion of `Lean4Lean.Levelled`:

0. normal equality without eta (`NormalEq₀`): structural, universe levels and
   proof irrelevance;
1. parallel reduction (`ParRed`): beta, native and registered schema patterns;
2. `DeltaPar`: parallel native prefix unfolding, quotient prefix unfolding and
   projection of constructor applications;
3. `EtaPar`: parallel function and structure eta expansion.

Eta expansion sits above beta. An expansion in the function position of a
redex blocks that redex, and the other side of the peak can only recover it by
a beta step followed by the original contraction, so the expansion side must
be allowed any number of lower steps.
-/

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2

/-- The structure eta expansion of `e` at the given structure. -/
def structExpand (family : Name) (info : VProjectionInfo) (levels : List VLevel)
    (params : List VExpr) (e : VExpr) : VExpr :=
  VExpr.mkApps (.const info.ctorName levels)
    (params ++ (List.range info.numFields).map fun index => .proj family index e)

/-- Parallel contraction of native prefix unfoldings, quotient prefix
unfoldings and projections of constructor applications. Arguments are
developed before the redex is contracted. -/
inductive DeltaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : DeltaPar Γ (.bvar i) (.bvar i)
  | sort : DeltaPar Γ (.sort u) (.sort u)
  | const : DeltaPar Γ (.const c ls) (.const c ls)
  | elim : DeltaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : DeltaPar Γ f f' → DeltaPar Γ a a' → DeltaPar Γ (.app f a) (.app f' a')
  | proj : DeltaPar Γ major major' →
      DeltaPar Γ (.proj family index major) (.proj family index major')
  | lam : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.lam A body) (.lam A' body')
  | forallE : DeltaPar Γ A A' → DeltaPar (A :: Γ) body body' →
      DeltaPar Γ (.forallE A body) (.forallE A' body')
  | delta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      NativeDeltaRule env univs recursorData Γ name levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const name levels) args) rhs
  | quotDelta {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      QuotDeltaRule env univs Γ levels args' rhs →
      DeltaPar Γ (VExpr.mkApps (.const ``Quot.lift levels) args) rhs
  | projIota {args args' : List VExpr} (hlen : args.length = args'.length) :
      (∀ i (hi : i < args.length) (hi' : i < args'.length), DeltaPar Γ args[i] args'[i]) →
      env.projections family info →
      Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName levels) args') : fieldType →
      args'[info.nparams + index]? = some field → Γ ⊢ field : fieldType →
      DeltaPar Γ (.proj family index (VExpr.mkApps (.const info.ctorName levels) args)) field

/-- Parallel function and structure eta expansion. The expanded term is
developed before it is expanded. -/
inductive EtaPar : List VExpr → VExpr → VExpr → Prop where
  | bvar : EtaPar Γ (.bvar i) (.bvar i)
  | sort : EtaPar Γ (.sort u) (.sort u)
  | const : EtaPar Γ (.const c ls) (.const c ls)
  | elim : EtaPar Γ (.elim block owner ls) (.elim block owner ls)
  | app : EtaPar Γ f f' → EtaPar Γ a a' → EtaPar Γ (.app f a) (.app f' a')
  | proj : EtaPar Γ major major' →
      EtaPar Γ (.proj family index major) (.proj family index major')
  | lam : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.lam A body) (.lam A' body')
  | forallE : EtaPar Γ A A' → EtaPar (A :: Γ) body body' →
      EtaPar Γ (.forallE A body) (.forallE A' body')
  | funEta : EtaPar Γ e e' → Γ ⊢ e : .forallE A B →
      EtaPar Γ e (.lam A (.app e'.lift (.bvar 0)))
  | structEta : EtaPar Γ e e' → env.projections family info →
      params.length = info.nparams → info.nindices = 0 →
      Γ ⊢ e : VExpr.mkApps (.const family levels) params →
      Γ ⊢ structExpand family info levels params e : VExpr.mkApps (.const family levels) params →
      EtaPar Γ e (structExpand family info levels params e')

section Basic

omit [Params] in
theorem forall₂_of_getElem {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i]) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hlen, H =>
    .cons (H 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using hlen) fun i hi hi' => H (i + 1) (by simpa using hi)
        (by simpa using hi'))
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

omit [Params] in
theorem getElem_of_forall₂ {R : α → β → Prop} {l : List α} {l' : List β}
    (H : List.Forall₂ R l l') : l.length = l'.length ∧
      ∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i] :=
  ⟨Lean4Lean.List.Forall₂.length_eq H, fun _ hi hi' => case_forall₂_get H hi hi'⟩

protected theorem DeltaPar.rfl : ∀ {e}, DeltaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app DeltaPar.rfl DeltaPar.rfl
  | .proj .. => .proj DeltaPar.rfl
  | .lam .. => .lam DeltaPar.rfl DeltaPar.rfl
  | .forallE .. => .forallE DeltaPar.rfl DeltaPar.rfl

protected theorem EtaPar.rfl : ∀ {e}, EtaPar Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .elim .. => .elim
  | .app .. => .app EtaPar.rfl EtaPar.rfl
  | .proj .. => .proj EtaPar.rfl
  | .lam .. => .lam EtaPar.rfl EtaPar.rfl
  | .forallE .. => .forallE EtaPar.rfl EtaPar.rfl

theorem FullReduction.mkApps_args (H : List.Forall₂ (FullReduction Γ) args args') :
    FullReduction Γ (VExpr.mkApps fn args) (VExpr.mkApps fn args') :=
  FullReduction.mkApps .rfl H

theorem DeltaPar.full (H : DeltaPar Γ e e') : FullReduction Γ e e' := by
  induction H with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 => exact ih1.app ih2
  | proj _ ih => exact ih.proj
  | lam _ _ ih1 ih2 => exact ih1.lam ih2
  | forallE _ _ ih1 ih2 => exact ih1.forallE ih2
  | delta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).tail (.delta hr)
  | quotDelta hlen _ hr ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).tail (.quotDelta hr)
  | projIota hlen _ hl hs hi ht ih =>
    exact (FullReduction.mkApps_args (forall₂_of_getElem hlen ih)).proj.tail
      (.projIota hl hs hi ht)

theorem FullReduction.structExpand (H : FullReduction Γ e e') :
    FullReduction Γ (structExpand family info levels params e)
      (structExpand family info levels params e') := by
  refine FullReduction.mkApps_args (case_forall₂_append ?_ ?_)
  · exact List.Forall₂.rfl fun _ _ => .rfl
  · induction (List.range info.numFields) with
    | nil => exact .nil
    | cons _ _ ih => exact .cons H.proj ih

theorem EtaPar.full (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaPar Γ e e')
    (he : Γ ⊢ e : T) : FullReduction Γ e e' := by
  induction H generalizing T with
  | bvar | sort | const | elim => exact .rfl
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, h1, h2⟩ := he.app_inv henv hΓ
    exact (ih1 hΓ h1).app (ih2 hΓ h2)
  | proj _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    exact (ih hΓ hm.hasType.2).proj
  | lam _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.lam_inv henv hΓ
    exact (ih1 hΓ h1).lam (ih2 ⟨hΓ, _, h1⟩ h2)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨⟨_, h1⟩, _, h2⟩ := he.forallE_inv henv
    exact (ih1 hΓ h1).forallE (ih2 ⟨hΓ, _, h1⟩ h2)
  | funEta _ ht ih =>
    have h := ih hΓ ht
    exact h.tail (.funEta (h.hasType hΓ ht))
  | structEta _ hl hp hi hs hc ih =>
    have h := ih hΓ hs
    exact h.tail (.structEta hl hp hi (h.hasType hΓ hs) ((FullReduction.structExpand h).hasType hΓ hc))

end Basic

section Levels

/-- The untyped level relations. -/
def LevelStep (Γ : List VExpr) : Nat → VExpr → VExpr → Prop
  | 0 => NormalEq₀ Γ
  | 1 => ParRed Γ
  | 2 => DeltaPar Γ
  | 3 => EtaPar Γ
  | _ + 4 => fun _ _ => False

/-- Some step below level `n`. -/
def Below (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop := ∃ k, k < n ∧ LevelStep Γ k a b

/-- The level relations restricted to typed sources, for the abstract criterion. -/
def LevelRel (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop :=
  (∃ A, Γ ⊢ a : A) ∧ LevelStep Γ n a b

theorem LevelStep.full (hΓ : OnCtx Γ (env.IsType univs)) (hn : 0 < n)
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : FullReduction Γ a b := by
  match n, H with
  | 1, H => exact .tail .rfl (.core H)
  | 2, H => exact DeltaPar.full H
  | 3, H => exact EtaPar.full hΓ H ha

theorem LevelStep.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : LevelStep Γ n a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  match n, H with
  | 0, H => exact ((NormalEqF.defeq hΓ H).of_l henv hΓ ha).hasType.2
  | n + 1, H => exact (LevelStep.full hΓ (Nat.succ_pos _) H ha).hasType hΓ ha

theorem Below.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) : Γ ⊢ b : A := by
  induction H with
  | rfl => exact ha
  | tail _ h ih => obtain ⟨_, _, h⟩ := h; exact h.hasType hΓ ih

theorem Below.loStar (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    Levelled.LoStar (LevelRel Γ) n a b := by
  induction H with
  | rfl => exact .rfl
  | tail h₁ h ih =>
    obtain ⟨k, hk, h⟩ := h
    exact .tail ih ⟨k, hk, ⟨_, Below.hasType hΓ h₁ ha⟩, h⟩

theorem Below.ofLoStar (H : Levelled.LoStar (LevelRel Γ) n a b) :
    ReflTransGen (Below Γ n) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => obtain ⟨k, hk, _, h⟩ := h; exact .tail ih ⟨k, hk, h⟩

theorem Below.mono (h : n ≤ m) (H : ReflTransGen (Below Γ n) a b) :
    ReflTransGen (Below Γ m) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h' ih => obtain ⟨k, hk, h'⟩ := h'; exact .tail ih ⟨k, by omega, h'⟩

theorem Below.single (hk : k < n) (H : LevelStep Γ k a b) : ReflTransGen (Below Γ n) a b :=
  .tail .rfl ⟨k, hk, H⟩

/-- Pushing the normal equalities of a levelled reduction to its end. -/
theorem Below.full (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (Below Γ n) a b) (ha : Γ ⊢ a : A) :
    ∃ a', FullReduction Γ a a' ∧ NormalEq Γ a' b := by
  induction H with
  | rfl => exact ⟨_, .rfl, .refl ha⟩
  | tail h₁ h ih =>
    obtain ⟨a', hr, he⟩ := ih
    obtain ⟨k, _, h⟩ := h
    have hm := Below.hasType hΓ h₁ ha
    cases k with
    | zero => exact ⟨a', hr, he.trans hΓ (NormalEqF.toNormalEq h)⟩
    | succ k =>
      obtain ⟨out, h1, h2⟩ := he.fullReduction hΓ (h.full hΓ (Nat.succ_pos _) hm)
      exact ⟨out, hr.trans h1, h2⟩

/-! ### Local diagrams -/

theorem levelZero_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (LevelRel Γ 0) := by
  have key : ∀ {a b}, ReflTransGen (LevelRel Γ 0) a b → a = b ∨ NormalEq₀ Γ a b := by
    intro a b H
    induction H with
    | rfl => exact .inl rfl
    | tail _ h ih =>
      obtain ⟨_, h⟩ := h
      rcases ih with rfl | ih
      · exact .inr h
      · exact .inr (ih.trans hΓ h)
  intro a b c hb hc
  rcases key hb with rfl | hb'
  · exact ⟨c, hc, .rfl⟩
  have ⟨_, hab⟩ := NormalEqF.defeq hΓ hb'
  rcases key hc with rfl | hc'
  · exact ⟨b, .rfl, .tail .rfl ⟨⟨_, hab.hasType.1⟩, hb'⟩⟩
  · exact ⟨c, .tail .rfl ⟨⟨_, hab.hasType.2⟩, (hb'.symm hΓ).trans hΓ hc'⟩, .rfl⟩

theorem ParRed.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : ParRed Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', ParRed Γ c c' ∧ NormalEq₀ Γ c' b := sorry

theorem DeltaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', DeltaPar Γ c c' ∧ NormalEq₀ Γ c' b := sorry

theorem EtaPar.normalEq₀_mirror (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaPar Γ a b) (hc : NormalEq₀ Γ c a) (ha : Γ ⊢ a : A) :
    ∃ c', EtaPar Γ c c' ∧ NormalEq₀ Γ c' b := sorry

theorem DeltaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, DeltaPar Γ b b₁ ∧ ReflTransGen (Below Γ 2) b₁ d) ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) := sorry

theorem DeltaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : DeltaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 2) b d ∧
      (∃ c₁, DeltaPar Γ c c₁ ∧ ReflTransGen (Below Γ 2) c₁ d) := sorry

theorem EtaPar.peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : EtaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, (∃ b₁, EtaPar Γ b b₁ ∧ ReflTransGen (Below Γ 3) b₁ d) ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

theorem EtaPar.parRed_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : ParRed Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

theorem EtaPar.deltaPar_peak (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaPar Γ a b) (H2 : DeltaPar Γ a c) (ha : Γ ⊢ a : A) :
    ∃ d, ReflTransGen (Below Γ 3) b d ∧
      (∃ c₁, EtaPar Γ c c₁ ∧ ReflTransGen (Below Γ 3) c₁ d) := sorry

/-! ### Assembly -/

theorem levelled_mac (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.Mac (LevelRel Γ) n b d :=
  ⟨b, b₁, .rfl, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_optLo (hΓ : OnCtx Γ (env.IsType univs)) (hb : Γ ⊢ b : A)
    (H1 : LevelStep Γ n b b₁) (H2 : ReflTransGen (Below Γ n) b₁ d) :
    Levelled.OptLo (LevelRel Γ) n b d :=
  ⟨b₁, .inr ⟨⟨_, hb⟩, H1⟩, Below.loStar hΓ H2 (H1.hasType hΓ hb)⟩

theorem levelled_peak₁ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → LevelRel Γ n a c →
      ∃ d, Levelled.Mac (LevelRel Γ) n b d ∧ Levelled.Mac (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨_, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  match n, H1, H2 with
  | 1, H1, H2 =>
    obtain ⟨b₁, c₁, h1, h2, h3⟩ := ParRed.church_rosser (η := false) hΓ ha H1 H2
    exact ⟨b₁, levelled_mac hΓ hb (n := 1) h1 .rfl,
      levelled_mac hΓ hc (n := 1) h2 (Below.single (k := 0) (by decide) (h3.symm hΓ))⟩
  | 2, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := DeltaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_mac hΓ hb (n := 2) h1 h2, levelled_mac hΓ hc (n := 2) h3 h4⟩
  | 3, H1, H2 =>
    obtain ⟨d, ⟨b₁, h1, h2⟩, ⟨c₁, h3, h4⟩⟩ := EtaPar.peak hΓ H1 H2 ha
    exact ⟨d, levelled_mac hΓ hb (n := 3) h1 h2, levelled_mac hΓ hc (n := 3) h3 h4⟩
  | n + 4, H1, _ => exact H1.elim

theorem levelled_peak₂ (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, LevelRel Γ n a b → Levelled.Lo (LevelRel Γ) n a c →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨k, hk, _, H2⟩
  have hb := H1.hasType hΓ ha
  have hc := H2.hasType hΓ ha
  have mirror : ∀ {c'}, LevelStep Γ n c c' → NormalEq₀ Γ c' b →
      ∃ d, Levelled.LoStar (LevelRel Γ) n b d ∧ Levelled.OptLo (LevelRel Γ) n c d :=
    fun h1 h2 => ⟨b, .rfl, levelled_optLo hΓ hc h1 (Below.single (k := 0) hn h2)⟩
  match n, k, hk, H1, H2 with
  | 1, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 3, 0, _, H1, H2 =>
    obtain ⟨c', h1, h2⟩ := H1.normalEq₀_mirror hΓ ((NormalEqF.symm hΓ H2)) ha
    exact mirror h1 h2
  | 2, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := DeltaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 2) h2 h3⟩
  | 3, 1, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.parRed_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | 3, 2, _, H1, H2 =>
    obtain ⟨d, h1, c₁, h2, h3⟩ := EtaPar.deltaPar_peak hΓ H1 H2 ha
    exact ⟨d, Below.loStar hΓ h1 hb, levelled_optLo hΓ hc (n := 3) h2 h3⟩
  | n + 4, _, _, H1, _ => exact H1.elim

theorem levelled_joinable (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (Levelled.Lo (LevelRel Γ) 4) :=
  Levelled.joinable (levelZero_joinable hΓ) (levelled_peak₁ hΓ) (levelled_peak₂ hΓ) 3

end Levels

section Strip

/-- Union of the three reducing level relations. -/
def UpStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  ParRed Γ a b ∨ DeltaPar Γ a b ∨ EtaPar Γ a b

theorem UpStep.below (H : ReflTransGen (UpStep Γ) a b) : ReflTransGen (Below Γ 4) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih =>
    refine .tail ih ?_
    rcases h with h | h | h
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩

theorem UpStep.congr {f : VExpr → VExpr} {g : List VExpr → List VExpr}
    (hf : ∀ {a b}, UpStep (g Γ) a b → UpStep Γ (f a) (f b))
    (H : ReflTransGen (UpStep (g Γ)) a b) : ReflTransGen (UpStep Γ) (f a) (f b) := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact .tail ih (hf h)

theorem FullStep.upStep (H : FullStep Γ e e') : ReflTransGen (UpStep Γ) e e' := by
  induction H with
  | core h => exact .tail .rfl (.inl h)
  | delta h => exact .tail .rfl (.inr (.inl (.delta rfl (fun _ _ _ => .rfl) h)))
  | quotDelta h => exact .tail .rfl (.inr (.inl (.quotDelta rfl (fun _ _ _ => .rfl) h)))
  | projIota hl hs hi ht =>
    exact .tail .rfl (.inr (.inl (.projIota rfl (fun _ _ _ => .rfl) hl hs hi ht)))
  | structEta hl hp hi hs ht =>
    exact .tail .rfl (.inr (.inr (.structEta .rfl hl hp hi hs ht)))
  | funEta ht => exact .tail .rfl (.inr (.inr (.funEta .rfl ht)))
  | @app _ f f' a a' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := id) (f := (VExpr.app · a)) ?_ ih1).trans
      (UpStep.congr (g := id) (f := VExpr.app f') ?_ ih2)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app h .rfl)
        | exact .inr (.inl (.app h .rfl))
        | exact .inr (.inr (.app h .rfl))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.app .rfl h)
        | exact .inr (.inl (.app .rfl h))
        | exact .inr (.inr (.app .rfl h))
  | proj _ ih =>
    refine UpStep.congr (g := id) ?_ ih
    rintro _ _ (h | h | h) <;> first
      | exact .inl (.proj h)
      | exact .inr (.inl (.proj h))
      | exact .inr (.inr (.proj h))
  | @lam _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.lam d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.lam · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam .rfl h)
        | exact .inr (.inl (.lam .rfl h))
        | exact .inr (.inr (.lam .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.lam h .rfl)
        | exact .inr (.inl (.lam h .rfl))
        | exact .inr (.inr (.lam h .rfl))
  | @forallE _ d d' b b' _ _ ih1 ih2 =>
    refine (UpStep.congr (g := (d :: ·)) (f := VExpr.forallE d) ?_ ih2).trans
      (UpStep.congr (g := id) (f := (VExpr.forallE · b')) ?_ ih1)
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE .rfl h)
        | exact .inr (.inl (.forallE .rfl h))
        | exact .inr (.inr (.forallE .rfl h))
    · rintro _ _ (h | h | h) <;> first
        | exact .inl (.forallE h .rfl)
        | exact .inr (.inl (.forallE h .rfl))
        | exact .inr (.inr (.forallE h .rfl))

theorem FullReduction.below (H : FullReduction Γ e e') : ReflTransGen (Below Γ 4) e e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.trans (UpStep.below h.upStep)

/-- The required global strip property: one full step commutes with an entire
finite development, up to normal equality. -/
theorem FullStep.strip (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (step : FullStep Γ source left) (development : FullReduction Γ source right) :
    ∃ left' right', FullReduction Γ left left' ∧ FullReduction Γ right right' ∧
      NormalEq Γ left' right' := by
  have hl := UpStep.below step.upStep
  have hr := development.below
  obtain ⟨d, h1, h2⟩ := levelled_joinable hΓ source left right
    (Below.loStar hΓ hl ht) (Below.loStar hΓ hr ht)
  obtain ⟨l', a1, a2⟩ := Below.full hΓ (Below.ofLoStar h1) (step.hasType hΓ ht)
  obtain ⟨r', b1, b2⟩ := Below.full hΓ (Below.ofLoStar h2) (development.hasType hΓ ht)
  exact ⟨l', r', a1, b1, a2.trans hΓ (b2.symm hΓ)⟩

/-- Full confluence follows from the global strip property and transport
through normal equality. -/
theorem FullReduction.church_rosser (hΓ : OnCtx Γ (env.IsType univs))
    (ht : HasType env univs Γ source type)
    (left : FullReduction Γ source l) (right : FullReduction Γ source r) :
    ∃ l' r', FullReduction Γ l l' ∧ FullReduction Γ r r' ∧ NormalEq Γ l' r' := by
  induction left with
  | rfl => exact ⟨_, _, right, .rfl, .refl (right.hasType hΓ ht)⟩
  | tail before step ih =>
    obtain ⟨l', r', hl, hr, heq⟩ := ih
    obtain ⟨l'', r'', hl'', hr'', heq'⟩ := step.strip hΓ (FullReduction.hasType hΓ before ht) hl
    obtain ⟨out, hout, heqOut⟩ := (heq.symm hΓ).fullReduction hΓ hr''
    exact ⟨l'', out, hl'', hr.trans hout, heq'.trans hΓ (heqOut.symm hΓ)⟩

end Strip

end Lean4Lean.VEnv

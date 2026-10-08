import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas

/-!
# Projections of an arbitrary major as constructor fields, up to proof irrelevance

Let `c args'` be a typed application of the constructor of a registered structure `S`, and `M`
an arbitrary major of type `S PA`, where `PA` agrees with the parameters of `args'` and `S` is not
a type at every universe instantiation. Then every projection of `M` that occurs in a well-formed
term is a proof, and it is definitionally equal to the corresponding field argument of `c args'`
by proof irrelevance. This is how the data-free part of a projection walk over `M` is transported
to the fields of a generic constructor application, without context strengthening.
-/

namespace Lean4Lean.VEnv
open VExpr

variable {env : VEnv} {U : Nat}

theorem forall₂_weakU {Γ Γ' : List VExpr} (W : Ctx.LiftN n 0 Γ Γ') (henv : env.Ordered) :
    ∀ {l l' : List VExpr}, List.Forall₂ (env.IsDefEqU U Γ) l l' →
      List.Forall₂ (env.IsDefEqU U Γ') (l.map (·.liftN n)) (l'.map (·.liftN n))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (h.weakN henv W) (forall₂_weakU W henv t)

theorem forall₂_transU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {a b c : List VExpr}, List.Forall₂ (env.IsDefEqU U Γ) a b →
      List.Forall₂ (env.IsDefEqU U Γ) b c → List.Forall₂ (env.IsDefEqU U Γ) a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (h.trans henv hΓ h') (forall₂_transU henv hΓ t t')

theorem forall₂_equiv_trans :
    ∀ {a b c : List VLevel}, List.Forall₂ (· ≈ ·) a b → List.Forall₂ (· ≈ ·) b c →
      List.Forall₂ (· ≈ ·) a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (Eq.trans h h') (forall₂_equiv_trans t t')

theorem wrapForalls_closed_dom : ∀ {doms : List VExpr} {body : VExpr} {n : Nat},
    (VExpr.wrapForalls doms body).ClosedN n → ∀ i (h : i < doms.length), (doms[i]).ClosedN (n + i)
  | [], _, _, _, i, h => by simp at h
  | d :: ds, body, n, h, i, hi => by
    obtain ⟨hd, hb⟩ := h
    cases i with
    | zero => simpa using hd
    | succ i =>
      have := wrapForalls_closed_dom (doms := ds) (n := n + 1) hb i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

end Lean4Lean.VEnv

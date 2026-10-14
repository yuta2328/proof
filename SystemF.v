From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import ZArith.
From Stdlib Require Import Ensembles.
From Autosubst Require Import Autosubst.
Import ListNotations.

Module Syntax.
  Module TypeTerm.
    (* De Bruijn types *)
    Inductive t: Type :=
    | TVar : var -> t                     (* α *)
    | TArrow : t -> t -> t                (* S -> U *)
    | TAll : { bind t } -> t.                      (* Λ. T *)

    #[global] Instance Ids_t: Ids t. derive. Defined.
    #[global] Instance Rename_t: Rename t. derive. Defined.
    #[global] Instance Subst_t: Subst t. derive. Defined.
    #[global] Instance SubstLemmas_t: SubstLemmas t. derive. Qed.
  End TypeTerm.

  Module Term.
    (* De Bruijn terms *)
    Inductive t: Type :=
    | Var : var -> t                                 
    | Abs : TypeTerm.t -> { bind t} -> t
    | App : t -> t -> t                              
    | TAbs : { bind TypeTerm.t in t} -> t
    | TApp : t -> TypeTerm.t -> t.                   

    #[global] Instance Ids_t: Ids t. derive. Defined.
    #[global] Instance Rename_t: Rename t. derive. Defined.
    #[global] Instance HSubst_t : HSubst TypeTerm.t t. derive. Defined.
    #[global] Instance Subst_t: Subst t. derive. Defined.
    #[global] Instance HSubstLemmas_t : HSubstLemmas TypeTerm.t t. derive. Qed.
    
    Inductive value: t -> Prop :=
    | VAbs: ∀ T M, value (Abs T M)
    | VTAbs: ∀ M, value (TAbs M).
  End Term.

  Module TypingContext.
    Definition t: Type := nat -> TypeTerm.t.

    Definition empty: t := ren id.

    Definition bind: t -> TypeTerm.t -> t := λ Γ T, T .: Γ.

    Definition lookup: t -> var -> TypeTerm.t := λ Γ x, Γ x.

    Definition shift: t -> t := λ Γ, (+ 1) >>> Γ.

    Definition closed: Term.t -> Prop := λ M, forall Γ, (M.[Γ]) = M.

    Lemma var_not_closed: ∀ x, ~ closed (Term.Var x).
    Proof.
      intros x H. unfold closed in H. specialize (H (ren (+1))). asimpl in H; inversion H. lia.
    Qed.
  End TypingContext.
End Syntax.

Module Semantics.
  Import Syntax.

  Inductive eval: Term.t -> Term.t -> Prop :=
  | EApp1 : ∀ M M' N, eval M M' -> eval (Term.App M N) (Term.App M' N)
  | EApp2 : ∀ V N N', Term.value V -> eval N N' -> eval (Term.App V N) (Term.App V N')
  | EAppAbs : ∀ T M V, Term.value V -> eval (Term.App (Term.Abs T M) V) (M.[ V /])
  | ETApp : ∀ M M' T, eval M M' -> eval (Term.TApp M T) (Term.TApp M' T)
  | ETAppTAbs : ∀ M T, eval (Term.TApp (Term.TAbs M) T) (M..[ T /]).
End Semantics.

Module Typing.
  Import Syntax.
  Import Semantics.

  Inductive has_type: TypingContext.t -> Term.t -> TypeTerm.t -> Prop :=
  | TRVar : ∀ Γ x T, TypingContext.lookup Γ x = T -> has_type Γ (Term.Var x) T
  | TRAbs : ∀ Γ T M U,
      has_type (TypingContext.bind Γ T) M U ->
      has_type Γ (Term.Abs T M) (TypeTerm.TArrow T U)
  | TRApp : ∀ Γ M N T U,
      has_type Γ M (TypeTerm.TArrow T U) ->
      has_type Γ N T ->
      has_type Γ (Term.App M N) U
  | TRTAbs : ∀ Γ M T,
      has_type Γ M T -> has_type Γ (Term.TAbs M) (TypeTerm.TAll T)
  | TRTApp : ∀ Γ M T U,
      has_type Γ M (TypeTerm.TAll T) ->
      has_type Γ (Term.TApp M U) U.[T/].

  Notation "Γ ⊢ M : T" := (has_type Γ M T) (at level 40, M at level 0, T at level 0).

  Lemma renaming: ∀ Γ M T, Γ ⊢ M : T -> ∀ ξ Γ', (∀ x, TypingContext.lookup Γ x = TypingContext.lookup Γ' (ξ x)) -> Γ' ⊢ (M.[ren ξ]) : T.
  Proof.
    intros Γ M T Hty. induction Hty; intros ξ Γ' Hren.
    - apply TRVar. rewrite <- Hren. trivial.
    - apply TRAbs. replace (up (ren ξ)) with (ren (upren ξ)) by autosubst. apply IHHty. intros [|x]; [reflexivity | apply Hren].
    - assert (E: (Term.App M N).[ren ξ] = Term.App (M.[ren ξ]) (N.[ren ξ])) by reflexivity. rewrite E. eapply TRApp. apply IHHty1. trivial. apply IHHty2. trivial.
    - assert (E: (Term.TAbs M).[ren ξ] = Term.TAbs (M.[ren ξ])) by reflexivity. rewrite E. apply TRTAbs. apply IHHty. trivial.
    - assert (E: (Term.TApp M U).[ren ξ] = Term.TApp (M.[ren ξ]) U) by reflexivity. rewrite E. eapply TRTApp. apply IHHty. trivial.
  Qed.

  Lemma weakening: ∀ Γ M T T', Γ ⊢ M : T -> TypingContext.bind Γ T' ⊢ (M.[ren (+1)]) : T.
  Proof.
    intros. eapply renaming; eauto. 
  Qed.

End Typing.

Import Syntax.
Import Semantics.
Import Typing.

Lemma canonical_arrow : ∀ M T1 T2,
  Term.value M ->
  (TypingContext.empty ⊢ M : (TypeTerm.TArrow T1 T2)) ->
  exists N, M = Term.Abs T1 N.
Proof.
  intros. inversion H0; subst.
  - inversion H.
  - exists M0. reflexivity.
  - inversion H.
  - inversion H.
Qed.

Lemma canonical_all : ∀ M S,
  Term.value M ->
  (TypingContext.empty ⊢ M : (TypeTerm.TAll S)) ->
  exists N, M = Term.TAbs N.
Proof.
  intros. inversion H0.
  - inversion H1.
  - rewrite <- H4 in H. inversion H.
  - exists M0. reflexivity.
  - rewrite <- H3 in H. inversion H.
Qed.

Theorem progress: ∀ Γ M T, (Γ ⊢ M : T) -> TypingContext.closed M -> Term.value M \/ exists M', eval M M'.
Proof.
  intros Γ M T Hty. induction Hty; intros Closed.
  - apply TypingContext.var_not_closed in Closed. contradiction.
  - left. apply Term.VAbs.
  - right.
    assert (ClosedM: TypingContext.closed M).
    { intros σ. specialize (Closed σ). simpl in Closed. inversion Closed. rewrite H0. trivial. }
    assert (ClosedN: TypingContext.closed N).
    { intros σ. specialize (Closed σ). simpl in Closed. inversion Closed. rewrite H1. trivial. }
    destruct (IHHty1 ClosedM) as [HVal1 | [M' HEval1]].
    + destruct (IHHty2 ClosedN) as [HVal2 | [N' HEval2]].
      * destruct HVal1 as [T' M0 | M0].
        -- exists (M0.[N/]). apply EAppAbs. trivial.
        -- inversion Hty1.
      * exists (Term.App M N'). apply EApp2; trivial.
    + exists (Term.App M' N). apply EApp1. trivial.
  - left. apply Term.VTAbs.
  - right.
    assert (ClosedM: TypingContext.closed M).
    { intros σ. specialize (Closed σ). simpl in Closed. inversion Closed. rewrite H0. trivial. }
    destruct (IHHty ClosedM) as [HVal | [M' HEval]].
    + destruct HVal as [T' M0 | M0].
      * inversion Hty.
      * exists (M0..[U/]). apply ETAppTAbs.
    + exists (Term.TApp M' U). apply ETApp. trivial.
Qed.

Lemma substitution: ∀ Γ M T, Γ ⊢ M : T -> ∀ σ Γ', (∀ x, Γ' ⊢ (σ x) : (TypingContext.lookup Γ x)) -> Γ' ⊢ (M.[σ]) : T.
Proof.
  intros Γ M T Hty. induction Hty; intros σ Γ' Hsbt.
  - assert (E: (Term.Var x).[σ] = σ x) by reflexivity. rewrite E. rewrite <- H. apply Hsbt.
  - assert (Hren: ∀ N ξ τ, (∀ y, τ y = ids (ξ y)) -> rename ξ N = N.[τ]).
    { induction N; intros ξ τ Hτ; simpl.
      - rewrite Hτ. reflexivity.
      - f_equal. apply IHN. intros [|y]; simpl; [reflexivity | unfold up; simpl; rewrite Hτ; reflexivity].
      - f_equal; [apply IHN1 | apply IHN2]; assumption.
      - f_equal. apply IHN. intros y. unfold hcomp, funcomp. rewrite Hτ. reflexivity.
      - f_equal. apply IHN. assumption. }
    assert (E: (Term.Abs T M).[σ] = Term.Abs T (M.[up σ])) by reflexivity. rewrite E.
    apply TRAbs. apply IHHty. intros [|x].
    + apply TRVar. reflexivity.
    + assert (E2: up σ (S x) = (σ x).[ren (+1)]). { unfold up. simpl. apply Hren. reflexivity. }
      rewrite E2. apply weakening. apply Hsbt.
  - assert (E: (Term.App M N).[σ] = Term.App (M.[σ]) (N.[σ])) by reflexivity. rewrite E.
    eapply TRApp; [apply IHHty1 | apply IHHty2]; assumption.
  - assert (E: (Term.TAbs M).[σ] = Term.TAbs (M.[σ >>| ren (+1)])) by reflexivity. rewrite E.
    apply TRTAbs. apply IHHty. intros x.
    (* Unprovable: TRTAbs does not shift Γ, so (σ x).|[ren (+1)] need not have type Γ x. *)
    admit.
  - assert (E: (Term.TApp M U).[σ] = Term.TApp (M.[σ]) U) by reflexivity. rewrite E.
    eapply TRTApp. apply IHHty. assumption.
Admitted.

Theorem subject_reduction : ∀ Γ M N T, Γ ⊢ M : T -> eval M N -> Γ ⊢ N : T.
Proof.
  Admitted.
Qed.


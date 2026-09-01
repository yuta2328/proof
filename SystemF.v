From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import ZArith.
From Stdlib Require Import Ensembles.
Import ListNotations.

Module Syntax.
  Module TypeTerm.
    (* De Bruijn types *)
    Inductive t: Type :=
    | TVar : nat -> t                     (* α *)
    | TArrow : t -> t -> t                (* S -> U *)
    | TAll : t -> t.                      (* Λ. T *)

    Fixpoint shift_ty (c: nat) (d: Z) (T: t) : t :=
      match T with
      | TVar k => if k <? c then TVar k else TVar (Z.to_nat (Z.of_nat k + d))
      | TArrow T1 T2 => TArrow (shift_ty c d T1) (shift_ty c d T2)
      | TAll T1 => TAll (shift_ty (S c) d T1)
      end.

    Fixpoint subst_ty (k: nat) (U: t) (T: t) : t :=
      match T with
      | TVar j => if j =? k then U else TVar j
      | TArrow T1 T2 => TArrow (subst_ty k U T1) (subst_ty k U T2)
      | TAll T1 => TAll (subst_ty (S k) (shift_ty 0 1 U) T1)
      end.

    Definition subst_ty_top (U T : t) : t := shift_ty 0 (-1) (subst_ty 0 (shift_ty 0 1 U) T).
    
    Inductive closed_under: nat -> t -> Prop :=
    | ClosedTVar: ∀ n α, α < n -> closed_under n (TVar α)
    | ClosedTArrow: ∀ n T1 T2, closed_under n T1 -> closed_under n T2 -> closed_under n (TArrow T1 T2)
    | ClosedTAll: ∀ n T, closed_under (S n) T -> closed_under n (TAll T).

    Lemma closed_under_shift : forall n T c,
      closed_under n T -> c <= n ->
      closed_under (S n) (shift_ty c 1 T).
    Proof.
      intros n T c Hclosed. generalize dependent c.
      induction Hclosed; intros c Hc; simpl.
      - destruct (Nat.ltb_spec α c).
        + apply ClosedTVar. lia.
        + apply ClosedTVar. replace (Z.to_nat (Z.of_nat α + 1)) with (S α) by lia. lia.
      - apply ClosedTArrow; [apply IHHclosed1 | apply IHHclosed2]; assumption.
      - apply ClosedTAll. apply IHHclosed. lia.
    Qed.

    Lemma closed_under_shift_cancel : forall n T c k,
      closed_under n T -> c <= k -> k <= n ->
      closed_under n (shift_ty k (-1) (shift_ty c 1 T)).
    Proof.
      intros n T c k Hclosed. generalize dependent k. generalize dependent c.
      induction Hclosed; intros c k Hck Hkn; simpl.
      - destruct (Nat.ltb_spec α c); simpl.
        + rewrite (proj2 (Nat.ltb_lt α k)) by lia. apply ClosedTVar. lia.
        + replace (Z.to_nat (Z.of_nat α + 1)) with (S α) by lia.
          destruct (Nat.ltb_spec (S α) k).
          * apply ClosedTVar. lia.
          * apply ClosedTVar. replace (Z.to_nat (Z.of_nat (S α) + -1)) with α by lia. assumption.
      - apply ClosedTArrow; [apply IHHclosed1 | apply IHHclosed2]; assumption.
      - apply ClosedTAll. apply IHHclosed; lia.
    Qed.

    Lemma closed_under_subst_at : forall n k T U,
      k <= n -> closed_under (S n) T -> closed_under n U ->
      closed_under n
        (shift_ty k (-1) (subst_ty k (shift_ty 0 1 U) T)).
    Proof.
      intros n k T U Hkn HT HU.
      generalize dependent n. generalize dependent k. generalize dependent U.
      induction T; intros U k scope Hkn HT HU; inversion HT; subst; simpl.
      - destruct (Nat.eqb_spec n k); subst.
        + eapply closed_under_shift_cancel; [exact HU | lia | lia].
        + destruct (Nat.ltb_spec n k).
          * simpl. rewrite (proj2 (Nat.ltb_lt n k)) by assumption.
            apply ClosedTVar. lia.
          * simpl. rewrite (proj2 (Nat.ltb_ge n k)) by lia. apply ClosedTVar.
            replace (Z.to_nat (Z.of_nat n + -1)) with (Nat.pred n) by lia.
            lia.
      - apply ClosedTArrow.
        + eapply IHT1; eassumption.
        + eapply IHT2; eassumption.
      - apply ClosedTAll.
        apply IHT with (n := S scope) (k := S k) (U := shift_ty 0 1 U).
        + lia.
        + assumption.
        + apply closed_under_shift with (c := 0); [assumption | lia].
    Qed.

    Lemma closed_under_subst_top : forall n T U,
      closed_under (S n) T -> closed_under n U ->
      closed_under n (subst_ty_top U T).
    Proof.
      intros n T U HT HU. unfold subst_ty_top.
      apply closed_under_subst_at; [lia | assumption | assumption].
    Qed.

  End TypeTerm.

  Module Term.
    (* De Bruijn terms *)
    Inductive t: Type :=
    | Var : nat -> t                                 (* x *)
    | Abs : TypeTerm.t -> t -> t                     (* λ:T. M *)
    | App : t -> t -> t                              (* M N *)
    | TAbs : t -> t                                  (* Λ. M *)
    | TApp : t -> TypeTerm.t -> t.                   (* M[T] *)

    Fixpoint shift_ty (c: nat) (d: Z) (M: t) : t :=
      match M with
      | Var x => Var x
      | Abs T M1 => Abs (TypeTerm.shift_ty c d T) (shift_ty c d M1)
      | App M1 M2 => App (shift_ty c d M1) (shift_ty c d M2)
      | TAbs M1 => TAbs (shift_ty (S c) d M1)
      | TApp M1 T => TApp (shift_ty c d M1) (TypeTerm.shift_ty c d T)
      end.

    Fixpoint subst_ty (k: nat) (A: TypeTerm.t) (M: t) : t :=
      match M with
      | Var x => Var x
      | Abs T M1 => Abs (TypeTerm.subst_ty k A T) (subst_ty k A M1)
      | App M1 M2 => App (subst_ty k A M1) (subst_ty k A M2)
      | TAbs M1 => TAbs (subst_ty (S k) (TypeTerm.shift_ty 0 1 A) M1)
      | TApp M1 T => TApp (subst_ty k A M1) (TypeTerm.subst_ty k A T)
      end.

    Definition subst_ty_top (T: TypeTerm.t) (M : t) : t := shift_ty 0 (-1) (subst_ty 0 (TypeTerm.shift_ty 0 1 T) M).

    Fixpoint shift_tm (c: nat) (d: Z) (M: t) : t :=
      match M with
      | Var k => if k <? c then Var k else Var (Z.to_nat (Z.of_nat k + d))
      | Abs T M1 => Abs T (shift_tm (S c) d M1)
      | App M1 M2 => App (shift_tm c d M1) (shift_tm c d M2)
      | TAbs M1 => TAbs (shift_tm c d M1)
      | TApp M1 T => TApp (shift_tm c d M1) T
      end.

    Fixpoint subst_tm (k: nat) (L: t) (M: t) : t :=
      match M with
      | Var j => if j =? k then L else Var j
      | Abs T M1 => Abs T (subst_tm (S k) (shift_tm 0 1 L) M1)
      | App M1 M2 => App (subst_tm k L M1) (subst_tm k L M2)
      | TAbs M1 => TAbs (subst_tm k (shift_ty 0 1 L) M1)
      | TApp M1 T => TApp (subst_tm k L M1) T
      end.

    Definition subst_tm_top (L M: t) : t := shift_tm 0 (-1) (subst_tm 0 (shift_tm 0 1 L) M).

    Inductive value: t -> Prop :=
    | VAbs: ∀ T M, value (Abs T M)
    | VTAbs: ∀ M, value (TAbs M).
  End Term.

  Module TypeVarContext.
    Definition t := nat.

    Definition empty: t := 0.

    Definition wf_type (Δ: t) (T: TypeTerm.t) : Prop := TypeTerm.closed_under Δ T.
  End TypeVarContext.

  Module TypingContext.
    Definition t: Type := list TypeTerm.t.

    Fixpoint lookup (Γ: t) (d: nat): option TypeTerm.t :=
      match Γ with
      | [] => None
      | T :: Γ' => if d =? 0 then Some T else lookup Γ' (pred d)
      end.

    Definition wf (Δ: TypeVarContext.t) (Γ: t): Prop := Forall (TypeVarContext.wf_type Δ) Γ.
      
    Definition shift_ty (c: nat) (d: Z) (Γ: t) : t := map (TypeTerm.shift_ty c d) Γ.

    Definition subst_ty (k: nat) (T: TypeTerm.t) (Γ: t) : t := map (TypeTerm.subst_ty k T) Γ.

    Lemma wf_shift : forall Δ Γ,
      wf Δ Γ -> wf (S Δ) (shift_ty 0 1 Γ).
    Proof.
      intros Δ Γ Hwf. induction Hwf; simpl.
      - constructor.
      - constructor.
        + apply TypeTerm.closed_under_shift with (c := 0); [assumption | lia].
        + assumption.
    Qed.
  End TypingContext.
End Syntax.

Module Semantics.
  Import Syntax.

  Inductive eval: Term.t -> Term.t -> Prop :=
  | EApp1 : ∀ M M' N, eval M M' -> eval (Term.App M N) (Term.App M' N)
  | EApp2 : ∀ V N N', Term.value V -> eval N N' -> eval (Term.App V N) (Term.App V N')
  | EAppAbs : ∀ T M V, Term.value V -> eval (Term.App (Term.Abs T M) V) (Term.subst_tm_top V M)
  | ETApp : ∀ M M' T, eval M M' -> eval (Term.TApp M T) (Term.TApp M' T)
  | ETAppTAbs : ∀ M U, eval (Term.TApp (Term.TAbs M) U) (Term.subst_ty_top U M).

  Definition nf (M: Term.t) : Prop := ~ exists N, eval M N.

  Lemma value_is_nf: ∀ M, Term.value M -> nf M.
  Proof.
    intros M Hv [N Hstep]. inversion Hv; subst; inversion Hstep.
  Qed.
End Semantics.

Module Typing.
  Import Syntax.
  Import Semantics.

  Inductive typing_rule: TypeVarContext.t -> TypingContext.t -> Term.t -> TypeTerm.t -> Prop :=
  | TRVar : ∀ Δ Γ x T, TypingContext.lookup Γ x = Some T -> typing_rule Δ Γ (Term.Var x) T
  | TRAbs : ∀ Δ Γ T M U,
      TypeVarContext.wf_type  Δ T ->
      typing_rule Δ (T :: Γ) M U ->
      typing_rule Δ Γ (Term.Abs T M) (TypeTerm.TArrow T U)
  | TRApp : ∀ Δ Γ M N T U,
      typing_rule Δ Γ M (TypeTerm.TArrow T U) ->
      typing_rule Δ Γ N T ->
      typing_rule Δ Γ (Term.App M N) U
  | TRTAbs : ∀ Δ Γ M T,
      typing_rule (S Δ) (TypingContext.shift_ty 0 1 Γ) M T -> typing_rule Δ Γ (Term.TAbs M) (TypeTerm.TAll T)
  | TRTApp : ∀ Δ Γ M T U,
      typing_rule Δ Γ M (TypeTerm.TAll T) ->
      TypeVarContext.wf_type Δ U ->
      typing_rule Δ Γ (Term.TApp M U) (TypeTerm.subst_ty_top U T).

  Definition has_type (Δ: TypeVarContext.t) (Γ: TypingContext.t) (M: Term.t) (T: TypeTerm.t) : Prop :=
    typing_rule Δ Γ M T /\ TypingContext.wf Δ Γ.

  Notation "Δ ; Γ ⊢ M : T" := (has_type Δ Γ M T) (at level 40, M at level 0, T at level 0).

  Lemma lookup_closed: ∀ Δ Γ x T, TypingContext.wf Δ Γ -> TypingContext.lookup Γ x = Some T -> TypeVarContext.wf_type Δ T.
  Proof.
    intros Δ Γ x T Hwf. revert x T.
    induction Hwf as [| A Γ HA Hwf IH]; intros x T Hlookup.
    - inversion Hlookup.
    - simpl in Hlookup. destruct (Nat.eqb_spec x 0); subst.
      + inversion Hlookup; subst. trivial.
      + apply IH with (x := Init.Nat.pred x). trivial.
  Qed.

  Lemma typing_closed : forall Δ Γ M T, has_type Δ Γ M T -> TypeVarContext.wf_type Δ T.
  Proof.
    intros Δ Γ M T [Hty Hwf]. revert Hwf.
    induction Hty; intros Hwf.
    - eapply lookup_closed; eassumption.
    - apply TypeTerm.ClosedTArrow.
      + assumption.
      + apply IHHty. constructor; assumption.
    - specialize (IHHty1 Hwf). inversion IHHty1; assumption.
    - apply TypeTerm.ClosedTAll. apply IHHty.
      apply TypingContext.wf_shift. assumption.
    - apply TypeTerm.closed_under_subst_top.
      + specialize (IHHty Hwf). inversion IHHty; assumption.
      + assumption.
  Qed.

End Typing.

Import Syntax.
Import Semantics.
Import Typing.

Lemma weakening : forall Δ Γ M T W, Δ ; Γ ⊢ M : T ->
                                                    TypeVarContext.wf_type Δ W ->
                                                    Δ ; (W :: Γ) ⊢ (Term.shift_tm 0 1 M) : T.
Proof.
  admit.
Qed.

Lemma canonical_arrow : forall M T1 T2,
  Term.value M ->
  (TypeVarContext.empty ; TypingContext.Empty ⊢ M : (TypeTerm.TArrow T1 T2)) ->
  exists N, M = Term.Abs T1 N.
Proof.
  intros M T1 T2 Hv [Hty Hwf]. inversion Hv; subst; inversion Hty; subst.
  - exists M0. reflexivity.
Qed.

Lemma canonical_all : forall M S,
  Term.value M ->
  (TypeVarContext.empty ; TypingContext.Empty ⊢ M : (TypeTerm.TAll S)) ->
  exists N, M = Term.TAbs N.
Proof.
  intros M A Hv [Hty Hwf]. inversion Hv; subst; inversion Hty; subst.
  - exists M0. reflexivity.
Qed.

Theorem progress: forall M T,
  (TypeVarContext.empty ; TypingContext.Empty ⊢ M : T) ->
  Term.value M \/ exists M', eval M M'.
Proof.
  intro M. induction M; intros T H; destruct H as [Hty Hwf].
  - inversion Hty; subst.
    match goal with [ H : TypingContext.lookup _ _ _ |- _ ] => inversion H end.
  - left. apply Term.VAbs.
  - right. inversion Hty; subst.
    assert (HM1 : TypeVarContext.empty ; TypingContext.Empty ⊢ M1 : (TypeTerm.TArrow T0 T)).
    { split; assumption. }
    assert (HM2 : TypeVarContext.empty ; TypingContext.Empty ⊢ M2 : T0).
    { split; assumption. }
    destruct (IHM1 _ HM1) as [Hval1 | [N1 Hstep1]].
    + destruct (IHM2 _ HM2) as [Hval2 | [N2 Hstep2]].
      * destruct (canonical_arrow M1 T0 T Hval1 HM1) as [P Heq]. subst M1.
        exists (Term.subst_tm_top M2 P). apply EAppAbs. assumption.
      * exists (Term.App M1 N2). apply EApp2; assumption.
    + exists (Term.App N1 M2). apply EApp1. assumption.
  - left. apply Term.VTAbs.
  - right. inversion Hty; subst.
    assert (HM : TypeVarContext.empty ; TypingContext.Empty ⊢ M : (TypeTerm.TAll T0)).
    { split; assumption. }
    destruct (IHM _ HM) as [Hval | [N Hstep]].
    + destruct (canonical_all M T0 Hval HM) as [P Heq]. subst M.
      exists (Term.subst_ty_top t P). apply ETAppTAbs.
    + exists (Term.TApp N t). apply ETApp. assumption.
Qed.

Theorem subject_reduction : forall Δ Γ M M' T,
  Δ ; Γ ⊢ M : T -> eval M M' -> Δ ; Γ ⊢ M' : T.
Proof.
  intros Δ Γ M M' T [Hty Hwf] Hev. revert Δ Γ T Hty Hwf.
  induction Hev; intros Δ Γ R Hty Hwf; inversion Hty; subst.
  (* EApp1 *)
  - match goal with
    | [ Hf : typing_rule _ _ M (TypeTerm.TArrow ?S _) |- _ ] =>
        destruct (IHHev Δ Γ (TypeTerm.TArrow S R) Hf Hwf) as [HM' _]
    end.
    split; [eapply TRApp; eassumption | assumption].
  (* EApp2 *)
  - match goal with
    | [ Ha : typing_rule _ _ N ?S |- _ ] =>
        destruct (IHHev Δ Γ S Ha Hwf) as [HN' _]
    end.
    split; [eapply TRApp; eassumption | assumption].
  (* EAppAbs: invert the TRAbs derivation and use term substitution *)
  - match goal with
    | [ Hf : typing_rule _ _ (Term.Abs T M) _ |- _ ] => inversion Hf; subst
    end.
    eapply substitution_term.
    + split; [eassumption |]. apply TypingContext.WfBinding; eassumption.
    + split; eassumption.
  (* ETApp *)
  - match goal with
    | [ Hp : typing_rule _ _ M (TypeTerm.TAll ?S) |- _ ] =>
        destruct (IHHev Δ Γ (TypeTerm.TAll S) Hp Hwf) as [HM' _]
    end.
    split; [apply TRTApp; assumption | assumption].
  (* ETAppTAbs: invert the TRTAbs derivation and use type substitution *)
  - match goal with
    | [ Hp : typing_rule _ _ (Term.TAbs M) _ |- _ ] => inversion Hp; subst
    end.
    split; [| assumption].
    apply substitution_type; assumption.
Qed.


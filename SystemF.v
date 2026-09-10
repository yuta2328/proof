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

    Definition scoped (Δ: nat) (T: t) : Prop :=
      forall θ1 θ2, (forall α, α <= Δ -> θ1 α = θ2 α) -> T.[θ1] = T.[θ2].

    Definition closed (T: t): Prop := scoped 0 T.

    Definition shift (T: t): t := T.[ren (+1)].
  End TypeTerm.

  Module Term.
    (* De Bruijn terms *)
    Inductive t: Type :=
    | Var : var -> t                                 
    | Abs : TypeTerm.t -> { bind t} -> t
    | App : t -> t -> t                              
    | TAbs : { bind TypeTerm.t in t} -> t            
    | TApp : t -> TypeTerm.t -> t.                   

    #[global] Instance HSubst_t : HSubst TypeTerm.t t. derive. Defined.   (* ← before Subst *)
    #[global] Instance Ids_t: Ids t. derive. Defined.
    #[global] Instance Rename_t: Rename t. derive. Defined.
    #[global] Instance Subst_t: Subst t. derive. Defined.
    #[global] Instance HSubstLemmas_t : HSubstLemmas TypeTerm.t t. derive. Qed.
    #[global] Instance SubstHSubstComp_t : SubstHSubstComp TypeTerm.t t. derive. Qed.
    #[global] Instance SubstLemmas_t: SubstLemmas t. derive. Qed.
    
    Inductive value: t -> Prop :=
    | VAbs: ∀ T M, value (Abs T M)
    | VTAbs: ∀ M, value (TAbs M).
  End Term.

  Module TypingContext.
    Definition t: Type := list TypeTerm.t.

    #[global] Instance Rename_t: Rename t. derive. Defined.

    Definition empty: t := [].

    Definition bind: t -> TypeTerm.t -> t := λ Γ T, T :: Γ.

    Fixpoint lookup (Γ: t) (d: nat): option TypeTerm.t :=
      match Γ with
      | [] => None
      | T :: Γ' => if d =? 0 then Some T else lookup Γ' (pred d)
      end.

    Definition shift (Γ: t) : t := map TypeTerm.shift Γ.
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
  | TRVar : ∀ Γ x T, TypingContext.lookup Γ x = Some T -> has_type Γ (Term.Var x) T
  | TRAbs : ∀ Γ T M U,
      has_type (TypingContext.bind Γ T) M U ->
      has_type Γ (Term.Abs T M) (TypeTerm.TArrow T U)
  | TRApp : ∀ Γ M N T U,
      has_type Γ M (TypeTerm.TArrow T U) ->
      has_type Γ N T ->
      has_type Γ (Term.App M N) U
  | TRTAbs : ∀ Γ M T,
      has_type (TypingContext.shift Γ) M T -> has_type Γ (Term.TAbs M) (TypeTerm.TAll T)
  | TRTApp : ∀ Γ M T U,
      has_type Γ M (TypeTerm.TAll T) ->
      has_type Γ (Term.TApp M U) U.[T/].

  Notation "Γ ⊢ M : T" := (has_type Γ M T) (at level 40, M at level 0, T at level 0).
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

Theorem progress: ∀ M T, (TypingContext.empty ⊢ M : T) -> Term.value M \/ exists M', eval M M'.
Proof.
  intro M. induction M; intros T H; destruct H as [Hty Hwf].
  - inversion Hty; subst. inversion H2; subst.
  - left. apply Term.VAbs.
  - right. inversion Hty; subst.
    assert (HM1 : TypeVarContext.empty ; TypingContext.empty ⊢ M1 : (TypeTerm.TArrow T0 T)).
    { split; assumption. }
    assert (HM2 : TypeVarContext.empty ; TypingContext.empty ⊢ M2 : T0).
    { split; assumption. }
    specialize (IHM1 (TypeTerm.TArrow T0 T) HM1). specialize (IHM2 T0 HM2).
    destruct IHM1. destruct IHM2.
    + specialize (canonical_arrow M1 T0 T H HM1). intro. destruct H1; subst. exists (x.[M2/]). apply EAppAbs. trivial.
    + destruct H0; subst. exists (Term.App M1 x). apply EApp2. trivial. trivial.
    + destruct H; subst. exists (Term.App x M2). apply EApp1. trivial. 
  - left. apply Term.VTAbs.
  - right. inversion Hty; subst.
    assert (Htyp : TypeVarContext.empty; TypingContext.empty ⊢ M : (TypeTerm.TAll T0)).
    { split; assumption. }
    specialize (IHM (TypeTerm.TAll T0) Htyp). destruct IHM.
    + specialize (canonical_all M T0 H Htyp). intro. destruct H0; subst. exists (x..[t/]). apply ETAppTAbs.
    + destruct H; subst. exists (Term.TApp x t). apply ETApp. trivial.
Qed.

Lemma typing_subst: ∀ Δ Γ M T, typing_rule Δ Γ M T ->
    ∀ Γ' σ, (∀ x T', TypingContext.lookup Γ x = Some T' -> typing_rule Δ Γ' (σ x) T') ->
            typing_rule Δ Γ' M.[σ] T.
Proof.
  intros. induction H; simpl; eauto.
  - apply 
Qed.

Lemma substitution :
  ∀ Δ Γ U T V M, Δ ; (TypingContext.bind Γ U) ⊢ M : T -> Δ; Γ ⊢ V : U -> Δ; Γ ⊢ (M.[V/]) : T.
Proof.
  intros. induction
Qed.
                                         
Theorem subject_reduction : ∀ Δ Γ M N T,
    Δ ; Γ ⊢ M : T -> eval M N -> Δ ; Γ ⊢ N : T.
Proof.
  intros Δ Γ M N T H. generalize N. inversion H; subst. induction H0.
  - intros. inversion H2; subst.
  - intros. inversion H3; subst.
  - intros.
    assert ( Δ; Γ ⊢ M : (TypeTerm.TArrow T U) ). { split; assumption. }
    assert ( Δ; Γ ⊢ N0 : T). { split; assumption. }
    inversion H0; subst.
    + specialize (IHtyping_rule1 H2 H1 M' H7). inversion IHtyping_rule1; subst.      
      specialize (TRApp Δ Γ M' N0 T U H4 H0_0). intro. assert (Δ; Γ ⊢ (Term.App M' N0) : U). { split; assumption. } trivial.
    + specialize (IHtyping_rule2 H3 H1 N' H8). inversion IHtyping_rule2; subst.
      specialize (TRApp Δ Γ M N' T U H0_ H4). intro. assert (Δ; Γ ⊢ (Term.App M N') : U). { split; assumption. } trivial.
    + inversion H; subst. inversion H4; subst. inversion H11; subst.
Qed.


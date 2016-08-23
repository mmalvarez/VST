Require Import veric.expr.
Require Import veric.SeparationLogic.
Require Import floyd.local2ptree.
Require Import floyd.client_lemmas.
Require Import floyd.efield_lemmas.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import mc_reify.clight_expr_eq.

Fixpoint denote_tc_assert_b_norho a:=
match a with 
| tc_TT => true
| tc_andp' a b => andb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| tc_orp' a b => orb (denote_tc_assert_b_norho a) (denote_tc_assert_b_norho b)
| _ => false
end.

Fixpoint denote_tc_assert_b_norho_forgive_isptr a e:=
match a with 
| tc_TT => true
| tc_andp' a b => andb (denote_tc_assert_b_norho_forgive_isptr a e)
                       (denote_tc_assert_b_norho_forgive_isptr b e)
| tc_orp' a b => orb (denote_tc_assert_b_norho_forgive_isptr a e)
                     (denote_tc_assert_b_norho_forgive_isptr b e)
| tc_isptr e0 => expr_beq e e0
| _ => false
end.

Require Import predicates_hered.

Locate denote_tc_assert.
Lemma denote_tc_assert_b_norho_sound: forall {CS : compspecs} a rho m,
    denote_tc_assert_b_norho a = true -> app_pred (expr2.denote_tc_assert a rho) m.
Proof.
intros.
induction a; simpl in *; unfold_lift; simpl; auto; try congruence.
rewrite andb_true_iff in *. intuition.
rewrite orb_true_iff in *. intuition. 
Qed.

Lemma denote_tc_assert_b_norho_forgive_isptr_sound: forall {CS:compspecs} a e rho m,
  denote_tc_assert_b_norho_forgive_isptr a e = true ->
  isptr (expr.eval_expr e rho) ->
  app_pred (expr2.denote_tc_assert a rho) m.
Proof.
intros.
induction a; simpl in *; unfold_lift; simpl; auto; try congruence.
rewrite andb_true_iff in *. intuition. 
rewrite orb_true_iff in *. intuition. 
apply expr_beq_spec in H; subst; auto.
Qed.



Definition tc_lvalue_b_norho {CS:compspecs} Delta e :=
denote_tc_assert_b_norho (typecheck_lvalue Delta e).

Definition tc_expr_b_norho {CS:compspecs} Delta e :=
denote_tc_assert_b_norho (typecheck_expr Delta e).

Definition tc_temp_id_b_norho {CS:compspecs} id t Delta e:=
denote_tc_assert_b_norho (typecheck_temp_id id t Delta e).

Definition tc_lvalue_b_norho' {CS:compspecs} Delta e :=
  match e with
  | Ederef e0 t => denote_tc_assert_b_norho_forgive_isptr
                     (typecheck_lvalue Delta e) e0
  | _ => denote_tc_assert_b_norho (typecheck_lvalue Delta e)
  end.

Lemma tc_lvalue_b_sound : 
forall {CS:compspecs} e Delta rho m,
tc_lvalue_b_norho Delta e = true ->
app_pred (tc_lvalue Delta e rho) m.
Proof.
intros.
apply denote_tc_assert_b_norho_sound; auto.
Qed.

Lemma tc_expr_b_sound : 
forall {CS:compspecs} e Delta rho m,
tc_expr_b_norho Delta e = true ->
app_pred (tc_expr Delta e rho) m.
Proof.
intros.
apply denote_tc_assert_b_norho_sound; auto.
Qed.

Lemma tc_temp_id_b_sound : 
forall {CS:compspecs} id t Delta e rho m,
tc_temp_id_b_norho id t Delta e= true ->
app_pred (tc_temp_id id t Delta e rho) m.
Proof.
intros.
apply denote_tc_assert_b_norho_sound; auto.
Qed.

Lemma tc_lvalue_b'_sound : 
forall {CS:compspecs} e Delta rho m,
tc_lvalue_b_norho' Delta e = true ->
isptr (expr.eval_lvalue e rho) ->
app_pred (tc_lvalue Delta e rho) m.
Proof.
intros.
destruct e eqn:HH; try solve [apply tc_lvalue_b_sound; auto].
eapply denote_tc_assert_b_norho_forgive_isptr_sound; [exact H |].
simpl in H0.
unfold_lift in H0.
destruct (expr.eval_expr e0 rho); try inversion H0.
simpl.
auto.
Qed.

Fixpoint tc_efield_b_norho {CS:compspecs} Delta efs :=
  match efs with
  | nil => true
  | eArraySubsc ei :: efs' =>
      (tc_expr_b_norho Delta ei && tc_efield_b_norho Delta efs')%bool
  | eStructField _ :: efs' => tc_efield_b_norho Delta efs'
  | eUnionField _ :: efs' => tc_efield_b_norho Delta efs'
  end.

(* there is a problem with typeclass resolution?
   so we have to put in app_pred manually?
   %pred vs. %logic
   pred is used in lower-level soundness proofs *)

Lemma pure_app_pred : forall (P : Prop) 
                     (m : compcert_rmaps.RML.R.rmap), app_pred (!!P)%logic m <-> P.
Proof.
  reflexivity.
Qed.

Lemma tc_efield_b_sound: forall {CS:compspecs} efs Delta rho m,
  tc_efield_b_norho Delta efs = true -> app_pred (tc_efield Delta efs rho) m.
Proof.
  intros.
  induction efs.
  + simpl; auto. rewrite pure_app_pred; auto.
  + destruct a; simpl in H |- *.
  - apply andb_true_iff in H.
    destruct H. specialize (IHefs H0).
    split; [apply tc_expr_b_sound|]; auto.
  - tauto.
  - tauto.
Qed.

Definition tc_LR_b_norho {CS:compspecs} Delta e lr :=
  match lr with
  | LLLL => tc_lvalue_b_norho' Delta e
  | RRRR => tc_expr_b_norho Delta e
  end.

Definition type_is_int (e: Clight.expr) : bool :=
  match typeof e with
  | Tint _ _ _ => true
  | _ => false
  end.
(*
Definition writable_share_b (sh: share) : bool :=
  if (seplog.writable_share_dec sh) then true else false.

Lemma writable_share_b_sound: forall sh,
  writable_share_b sh = true -> writable_share sh.
Proof.
  intros.
  unfold writable_share_b in H.
  destruct (seplog.writable_share_dec sh).
  auto.
  congruence.
Qed.
*)
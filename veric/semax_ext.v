Require Import veric.base.
Require Import msl.rmaps.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import sepcomp.extspec.
Require Import veric.juicy_extspec.
Require Import veric.expr. 
Require Import veric.semax.

Definition funsig2signature (s : funsig) : signature :=
  mksignature (map typ_of_type (map snd (fst s))) (Some (typ_of_type (snd s))) cc_default.

Definition ef_id ef :=
  match ef with EF_external id sig => id | _ => 1%positive end.

Section funspecs2jspec.

Variable Z : Type.

Variable Espec : juicy_ext_spec Z.

Parameter symb2genv : forall (ge_s : PTree.t block), genv. (*TODO*)
Axiom symb2genv_ax : forall (ge_s : PTree.t block), Genv.genv_symb (symb2genv ge_s) = ge_s.

Definition funspec2pre (A : Type) P id ef x ge_s (tys : list typ) args (z : Z) m : Prop :=
  match ident_eq id (ef_id ef) as s 
  return ((if s then (rmap*A)%type else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m) 
                       /\ P (snd x') (make_ext_args (symb2genv ge_s) 1 args) phi0
                       /\ necR (fst x') phi1 
    | right n => fun x' => ext_spec_pre Espec ef x' ge_s tys args z m
  end x.

Definition funspec2post (A : Type) (Q : A -> environ -> mpred) 
                        id ef x (tret : option typ) ret (z : Z) m : Prop :=
  match ident_eq id (ef_id ef) as s 
  return ((if s then (rmap*A)%type else ext_spec_type Espec ef) -> Prop)
  with 
    | left _ => fun x' => exists phi0 phi1, join phi0 phi1 (m_phi m) 
                       /\ Q (snd x') (make_ext_rval 1 ret) phi0
                       /\ necR (fst x') phi1 
    | right n => fun x' => ext_spec_post Espec ef x' tret ret z m
  end x.

Definition funspec2extspec (f : (ident*funspec)) 
  : external_specification juicy_mem external_function Z :=
  match f with 
    | (id, mk_funspec sig A P Q) =>
      Build_external_specification juicy_mem external_function Z
        (fun ef => if ident_eq id (ef_id ef) then (rmap*A)%type else ext_spec_type Espec ef)
        (funspec2pre A P id)
        (funspec2post A Q id)
        (fun rv z m => False)
  end.

Definition wf_funspec (f : funspec) :=
  match f with
    | mk_funspec sig A P Q => 
        (forall a rho rho' phi phi', 
        (P a rho phi -> Q a rho' phi' -> 
        forall adr, 
          match phi @ adr with
            | NO _ => True
            | YES _ _ _ _ => True
            | PURE k pp => phi' @ adr = PURE k (preds_fmap (approx (level phi')) pp)
          end))
        /\ (forall a ge ge' n args phi, Genv.genv_symb ge = Genv.genv_symb ge' ->
              (P a (make_ext_args ge n args) phi <-> 
               P a (make_ext_args ge' n args) phi))
  end.

Program Definition funspec2jspec f (wf : wf_funspec (snd f)) : juicy_ext_spec Z :=
  Build_juicy_ext_spec _ (funspec2extspec f) _ _ _ _.
Next Obligation.
destruct f; simpl; unfold funspec2pre; simpl.
simpl in t; revert t.
destruct (ident_eq i (ef_id e)).
* clear wf; subst i; intros t a a' Hage; destruct m; simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
split; [solve[eapply h; eauto]|].
apply (necR_trans (fst t) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_pre_hered.
Qed.
Next Obligation.
destruct f; simpl; unfold funspec2post; simpl.
simpl in t; revert t.
destruct (ident_eq i (ef_id e)).
* clear wf; subst i; intros t a a' Hage; destruct m0; simpl.
intros [phi0 [phi1 [Hjoin [Hx Hy]]]].
apply age1_juicy_mem_unpack in Hage.
destruct Hage as [Hage Hdry].
destruct (age1_join2 phi0 Hjoin Hage) as [x' [y' [Hjoin' [Hage' H]]]].
exists x', y'; split; auto.
split; [solve[eapply h; eauto]|].
apply (necR_trans (fst t) phi1 y'); auto.
unfold necR. constructor; auto.
* intros ? ? ?; auto.
destruct Espec; simpl; apply JE_post_hered.
Qed.
Next Obligation.
intros ? ? ? ?; destruct f; auto.
Qed.
Next Obligation.
destruct f; unfold jspec_pures_sub; simpl; intros.
revert wf; unfold wf_funspec; simpl; intros H2. revert t H H0 H2. 
unfold funspec2pre, funspec2post. 
destruct (ident_eq i (ef_id e)).
* intros. intros adr.
destruct H2 as [H2 _].
specialize (H2 (snd t) (make_ext_args (symb2genv ge_s) 1 args) (make_ext_rval 1 rv)). 
destruct H as [phi0 [phi1 [Hjoin [Hpre Hnec]]]].
destruct H0 as [phi0' [phi1' [Hjoin' [Hpost Hnec']]]].
generalize (H2 _ _ Hpre Hpost adr). clear H2.
clear -Hjoin Hjoin'. 
cut (level phi0' = level jm'). intros Hlev.
apply resource_at_join with (loc := adr) in Hjoin. revert Hjoin.
apply resource_at_join with (loc := adr) in Hjoin'. revert Hjoin'.
case_eq (m_phi jm @ adr); auto. intros k p Hpure.
case_eq (phi0 @ adr); try solve[inversion 3].
intros ? ? Hphi0. inversion 2. subst.
intros H2; rewrite H2 in Hjoin'. inv Hjoin'. rewrite Hlev.
rewrite level_juice_level_phi; auto.
apply join_level in Hjoin'. 
destruct Hjoin'; auto.
* destruct Espec; simpl; intros.
clear H2; eapply (JE_rel e); eauto.
Qed.

End funspecs2jspec.

Inductive wf_funspecs := 
| wf_nil : wf_funspecs
| wf_cons : forall (f : ident*funspec) (wf : wf_funspec (snd f)) (l : wf_funspecs), 
              wf_funspecs.

Fixpoint in_funspecs (f : (ident*funspec)) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => False
    | wf_cons f' wf fs' => f=f' \/ in_funspecs f fs'
  end.

Fixpoint in_funspecs_by_id (f : (ident*funspec)) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => False
    | wf_cons f' wf fs' => fst f=fst f' \/ in_funspecs_by_id f fs'
  end.

Lemma in_funspecs_by_id_lem id f f' fs : 
  in_funspecs_by_id (id,f) fs <-> in_funspecs_by_id (id,f') fs.
Proof.
elim fs; simpl; [split; auto|].
intros [? ?]; simpl; intros H H2 H3; rewrite H3; split; auto.
Qed.

Lemma in_funspecs_in_by_id f fs :
  in_funspecs f fs -> 
  in_funspecs_by_id f fs.
Proof.
elim fs; simpl; auto.
intros [? ?]; simpl; intros ? ? IH.
intros [?|?]. subst. left; auto. right; auto.
Qed.

Fixpoint funspecs_norepeat fs :=
  match fs with
    | wf_nil => True
    | wf_cons f wf fs' => ~in_funspecs_by_id f fs' /\ funspecs_norepeat fs'
  end.

Lemma in_funspecs_wf f fs : in_funspecs f fs -> wf_funspec (snd f).
Proof. induction fs; simpl; inversion 1; try subst f0; auto. Qed.

Fixpoint add_funspecs_rec (Z : Type) (Espec : juicy_ext_spec Z) (fs : wf_funspecs) :=
  match fs with
    | wf_nil => Espec
    | wf_cons (i,f) wf fs' => 
      funspec2jspec Z (add_funspecs_rec Z Espec fs') (i,f) wf
  end.

Require Import JMeq.

Lemma add_funspecs_pre {Z fs id sig A P Q x args m} Espec tys ge_s phi0 phi1 :
  let ef := EF_external id (funsig2signature sig) in
  funspecs_norepeat fs -> 
  in_funspecs (id, (mk_funspec sig A P Q)) fs -> 
  join phi0 phi1 (m_phi m) ->
  P x (make_ext_args (symb2genv ge_s) 1%positive args) phi0 ->
  exists x' : ext_spec_type (JE_spec _ (add_funspecs_rec Z Espec fs)) ef, 
    JMeq (phi1,x) x' 
    /\ forall z, ext_spec_pre (add_funspecs_rec Z Espec fs) ef x' ge_s tys args z m.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 H2 Hpre.
destruct H1 as [H1|H1].

{ 
subst f;simpl in *.
clear IHfs H; revert x H2 Hpre; unfold funspec2pre; simpl.
destruct (ident_eq id id); simpl.
intros x Hjoin Hp. exists (phi1,x). split; eauto.
elimtype False; auto.
}

{ 
assert (Hin: in_funspecs_by_id (id, mk_funspec sig A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
destruct (IHfs Hb H1 H2 Hpre) as [x' H3].
clear -Ha Hin H1 H3; revert x' Ha Hin H1 H3.
destruct f; simpl; destruct f; simpl; unfold funspec2pre; simpl.
destruct (ident_eq i id).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec f A0 m0 m1) in Hb.
  elimtype False; auto.
* intros; eexists; eauto.
}
Qed.

Lemma add_funspecs_post {Z Espec tret fs id sig A P Q x ret m z} :
  let ef := EF_external id (funsig2signature sig) in
  funspecs_norepeat fs -> 
  in_funspecs (id, (mk_funspec sig A P Q)) fs -> 
  ext_spec_post (add_funspecs_rec Z Espec fs) ef x tret ret z m -> 
  exists (phi0 phi1 phi1' : rmap) (x' : A), 
       join phi0 phi1 (m_phi m) 
    /\ necR phi1' phi1
    /\ JMeq x (phi1',x') 
    /\ Q x' (make_ext_rval 1%positive ret) phi0.
Proof.
induction fs; [intros; elimtype False; auto|]; intros ef H H1 Hpost.
destruct H1 as [H1|H1].

{ 
subst f;simpl in *.
clear IHfs H; revert x Hpost; unfold funspec2post; simpl.
destruct (ident_eq id id); simpl.
intros x [phi0 [phi1 [Hjoin [Hq Hnec]]]].
exists phi0, phi1, (fst x), (snd x).
split; auto. split; auto. destruct x; simpl in *. split; auto.
elimtype False; auto.
}

{ 
assert (Hin: in_funspecs_by_id (id, mk_funspec sig A P Q) fs). 
{ clear -H1; apply in_funspecs_in_by_id in H1; auto. }
destruct H as [Ha Hb]. 
clear -Ha Hin H1 Hb Hpost IHfs; revert x Ha Hin H1 Hb Hpost IHfs.
destruct f; simpl; destruct f; simpl; unfold funspec2post; simpl.
destruct (ident_eq i id).
* subst i; destruct fs; [solve[simpl; intros; elimtype False; auto]|].
  intros x' Ha Hb; simpl in Ha, Hb.
  rewrite in_funspecs_by_id_lem with (f' := mk_funspec f A0 m0 m1) in Hb.
  elimtype False; auto.
* intros. apply IHfs; auto.
}
Qed.

Definition add_funspecs (Espec : OracleKind) (fs : wf_funspecs) : OracleKind :=
  match Espec with
    | Build_OracleKind ty spec => 
      Build_OracleKind ty (add_funspecs_rec ty spec fs)
  end.

Section semax_ext.

Variable Espec : OracleKind.

Lemma semax_ext id sig A P Q (fs : wf_funspecs) : 
  let f := mk_funspec sig A P Q in
  in_funspecs (id,f) fs -> 
  funspecs_norepeat fs -> 
  (forall n, semax_external (add_funspecs Espec fs) (EF_external id (funsig2signature sig)) _ P Q n).
Proof.
intros f Hin Hnorepeat.
unfold semax_external.
intros n ge x n0 Hlater F ts args jm H jm' H2 H3.
destruct H3 as [s [t [Hjoin [Hp Hf]]]].
destruct Espec.
assert (Hp'': P x (make_ext_args (symb2genv (Genv.genv_symb ge)) 1 args) s).
{ generalize (in_funspecs_wf _ _ Hin). simpl; intros [Hwf1 Hwf2].
  rewrite Hwf2; eauto.
  rewrite symb2genv_ax; auto. }
destruct (add_funspecs_pre OK_spec ts (Genv.genv_symb ge) s t Hnorepeat Hin Hjoin Hp'') 
  as [x' [Heq Hpre]].
simpl.
exists x'.
intros z.
split; [solve[apply Hpre]|].
intros tret ret z' jm2 Hlev jm3 Hnec Hpost.

eapply add_funspecs_post in Hpost; eauto.
destruct Hpost as [phi0 [phi1 [phi1' [x'' [Hjoin' [Hnec' [Hjmeq' Hq']]]]]]].
exists phi0, phi1; split; auto.
assert (JMeq (t,x) (phi1',x'')) by (eapply JMeq_trans; eauto).
assert ((t,x) = (phi1',x'')) by (apply JMeq_eq in H0; auto).
inv H1.
split; auto.
eapply pred_nec_hereditary; eauto.
Qed.
  
End semax_ext.  
Require Import List.
Require Import Arith.
Require Import Omega.

Require Import bil.bil.

Lemma in_delta_types : forall id type v d,
    type_delta d ->
    In (var_var id type, v) d ->
    type_exp nil v type.
Proof.
  intros id type v d td v_in.
  induction td.
  - contradiction.
  - destruct v_in.
    + inversion H1.
      rewrite <- H5.
      rewrite <- H4.
      assumption.
    + apply IHtd; assumption.
Qed.

Lemma in_list_minus : forall {A} (l l' : list A) (e : A) {dec},
    In e (list_minus dec l l') <-> In e l /\ ~In e l'.
  intros A l l' e dec.
  split.
  intro e_in.
  induction l.
  - simpl in e_in; contradiction.
  - simpl in e_in.
    simpl.
    constructor.
    destruct (list_mem dec a l').
    + apply IHl in e_in; destruct e_in.
      constructor; try right; assumption.
    + destruct e_in.
      * constructor. try left; assumption.
      * right; apply IHl; assumption.
    + unfold list_mem in e_in.
      destruct (in_dec dec a l').
      tauto.
      destruct e_in.
      * rewrite <- H.
        assumption.
      * tauto.
  - intro conj; destruct conj as [in_l nin_l'].
    induction l.
    * tauto.
    * simpl.
      unfold list_mem.
      destruct (in_dec dec a l'); destruct (dec e a).
      -- rewrite e0 in nin_l'.
         tauto.
      -- destruct in_l.
         ++ symmetry in H; contradiction.
         ++ apply IHl in H; assumption.
      -- rewrite e0; simpl; auto.
      -- right; apply IHl.
         destruct in_l.
         ++ symmetry in H; contradiction.
         ++ assumption.
(* TODO: clean up proof *)
Qed.

Definition var_id : var -> id :=
(fun v : var => match v with
                | var_var id0 _ => id0
                end).

Lemma typ_gamma_remove_var : forall g x g', typ_gamma (g ++ x :: g') -> typ_gamma (g ++ g').
Proof.
  intros g x g'; revert g g' x.
  induction g as [| x g].
  - simpl.
    intros g' x txg'.
    inversion txg'; assumption.
  -  simpl.
     intros g' x0 txgxn.
     inversion txgxn as [G | G id t nin tgxn x_eq_x].
     apply IHg in tgxn.
     fold var_id in nin.
     apply tg_cons.
     fold var_id.
     rewrite map_app.
     rewrite map_app in nin.
     simpl in nin.
     intro nin'.
     apply in_app_or in nin'.
     apply nin.
     apply in_or_app.
     destruct nin'.
     left; assumption.
     right; right; assumption.
     assumption.
Qed.

(*
Ltac unique_suffices_type_exp_base :=
match goal with
    | [ H_tG : typ_gamma ?G, H_G_eq : ?G = ?x :: ?g |- _ ] =>
      destruct H_tG; inversion H_G_eq;
        match goal with
        | [ H_g_eq : ?G = g |- _ ] =>
          rewrite H_g_eq in H_tG;
            apply t_int;
            assumption
        end
    end.

Lemma unique_suffices_type_exp : forall (g g' : gamma) x e t,
    In x (g ++ g')->
    type_exp (g ++ x::g') e t ->
    type_exp (g ++ g') e t.
Proof.
  intros g g' x e t x_in_g xg_te.
  remember (g ++ x :: g') as gxg'.
  induction xg_te.
  - destruct H0; inversion Heqgxg'.
    elim (app_cons_not_nil g g' x); assumption.
    destruct (eq_var (var_var id5 t) x).
    + rewrite <- e in x_in_g.
      apply t_var.
      * apply x_in_g.
      * apply H0.
    + rewrite Heqxg in H.
      destruct H.
      * elim n; symmetry; apply H.
      * apply t_var; assumption.
  - unique_suffices_type_exp_base.
  - apply (t_load _ e1 e2 ed sz nat5); auto.
  - apply (t_store _ e1 e2 ed sz e3); auto.
  - apply t_aop; auto.
  - apply (t_lop _ e1 lop5 e2 sz); auto.
  - apply t_uop; auto.
  - apply (t_cast _ _ _ _ nat5); auto.
  - apply t_let; auto.
    


Lemma fv_impl_exp_v : forall x e, In x (fv_exp e) -> In x (vars_in_exp e).
  intros x e.
  induction e.
  all: try (simpl; tauto).
  all: try (simpl;  intro x_in;  apply in_app_or in x_in; apply in_or_app; firstorder).
  - apply in_app_or in H.
    firstorder.
  - right.
    simpl; right.
    apply IHe2.
    apply (in_list_minus (fv_exp e2) (var5 :: nil)) in H.
    assumption.
  - apply in_app_or in H.
    firstorder.
Qed.
*)

Lemma type_exp_typ_gamma : forall g e t, type_exp g e t -> typ_gamma g.
Proof.
  intros g e t te.
  induction te; auto.
Qed.

Lemma exp_weakening : forall g gw g' e t,
    type_exp (g ++ g') e t -> typ_gamma (g ++ gw ++ g') -> type_exp (g ++ gw ++ g') e t.
Proof.
  intros g gw g' e t et gt.
  remember (g ++ g') as G.
  generalize dependent g.
  induction et.
  - intros g HeqG.
    rewrite HeqG in H.
    apply t_var.
    + apply in_app_or in H.
      apply in_or_app.
      destruct H.
      * left; assumption.
      * right; apply in_or_app; right; assumption.
  - intros g HeqG.
    rewrite HeqG in H.
    apply t_int.
  - intros g HeqG tGw.
    apply (t_load _ _ _ _ sz nat5); auto.
  - intros g HeqG tGw.
    apply (t_store _ e1 e2 ed sz e3); auto.
  - intros g HeqG tGw.
    apply t_aop; auto.
  - intros g HeqG tGw.
    apply (t_lop _ e1 lop5 e2 sz); auto.
  - intros g HeqG tGw.
    apply t_uop; auto.
  - intros g HeqG tGw.
    apply (t_cast _ _ _ _ nat5); auto.
  - intros g HeqG tGw.
    apply t_let; auto.
  - intros g HeqG tGw.
    apply t_unknown; auto.
  - intros g HeqG tGw.
    apply t_ite; auto.
  - intros g HeqG tGw.
    apply (t_extract _ _ _ _ sz); auto.
  - intros g HeqG tGw.
    apply t_concat; auto.
Qed.

Ltac subst_lfv_rec_case in_y_subst :=
  simpl;
  simpl in in_y_subst;
  solve [firstorder
        | try apply in_or_app;
          apply in_app_or in in_y_subst;
          destruct in_y_subst as [in_subst_es_1 | in_y_subst];
          firstorder;
          subst_lfv_rec_case in_y_subst
        | right; subst_lfv_rec_case in_y_subst].

Lemma subst_lfv_notin_e1 : forall x y e1 e2,
    ~ In y (lfv_exp e1) ->
    In y (lfv_exp (letsubst_exp e1 x e2)) ->   In y (lfv_exp e2).
Proof.
  intros x y e1 e2 lfv_e1_nin in_y_subst_e1.
  induction e2.
  all: try contradiction.
  all: auto.
  all: try subst_lfv_rec_case in_y_subst_e1.
  - simpl in in_y_subst_e1.
    destruct (eq_letvar letvar5 x).
    +  contradiction.
    + assumption.
  - simpl.
    simpl in in_y_subst_e1.
    apply in_or_app.
    apply in_app_or in in_y_subst_e1.
    destruct in_y_subst_e1 as [in_subst_es_1 | in_y_subst].
    firstorder.
    right.
    destruct (eq_letvar letvar5 x).
    assumption.
    apply in_list_minus in in_y_subst; destruct in_y_subst.
    apply (in_list_minus (lfv_exp e2_2) (letvar5 :: nil) y).
    constructor.
    + auto.
    + assumption.
Qed.

Lemma subst_lfv : forall x y e1 e2,
    In y (lfv_exp (letsubst_exp e1 x e2)) -> In y (lfv_exp e1) \/  In y (lfv_exp e2).
Proof.
  intros x y e1 e2 in_y_subst_e1.
  destruct (in_dec eq_letvar y (lfv_exp e1)).
  - left; assumption.
  - right; apply (subst_lfv_notin_e1 x y e1 e2); assumption.
Qed.

Ltac apply_all e t:=
  repeat match goal with
         | [ H : forall _ : t, _ |- _ ] =>
           specialize (H e)
         end.

Ltac subst_lfv_neq_rec_case :=
  intros e1 x_nin_lfv_e1 in_y_subst_e1;
  simpl in in_y_subst_e1;
  apply_all e1 exp;
  repeat (apply in_app_or in in_y_subst_e1;
          destruct in_y_subst_e1 as [in_subst_es_1 | in_y_subst_e1];
          try tauto).

Lemma subst_lfv_neq : forall x y e1 e2,
    ~ In x (lfv_exp e1) ->
    In y (lfv_exp (letsubst_exp e1 x e2)) -> ~ y = x.
Proof.
  intros x y e1 e2 x_nin_lfv_e1 in_y_subst_e1 x_eq_y.
  rewrite x_eq_y in in_y_subst_e1.
  generalize dependent e1.
  induction e2.
  all: try contradiction.
  all: auto.
  all: try solve [subst_lfv_neq_rec_case].
  - intros e1 x_nin_lfv_e1 in_y_subst_e1.
    simpl in in_y_subst_e1.
    destruct (eq_letvar letvar5 x).
    + contradiction.
    + destruct in_y_subst_e1.
      * contradiction.
      * tauto.
  - intros e1 x_nin_lfv_e1 in_y_subst_e1.
    simpl in in_y_subst_e1.
    apply in_app_or in in_y_subst_e1.
    destruct in_y_subst_e1 as [in_subst_es_1 | in_y_subst].
    + firstorder.
    + apply (IHe2_2 e1).
      * assumption.
      * destruct (eq_letvar letvar5 x).
        -- rewrite <- e in in_y_subst.
           apply in_list_minus in in_y_subst.
           destruct in_y_subst.
           simpl in H0.
           elim H0.
           left; reflexivity.
        -- apply in_list_minus in in_y_subst.
           destruct in_y_subst.
           assumption.
Qed.

Ltac in_subst_lfv_rec_case :=
  intros x y e1 xneq iny;
  simpl;
  simpl in iny;
  repeat
    match goal with
    | [ H : forall (x y : letvar) (e1 : exp), _ |- _ ] =>
      specialize H with x y e1
    end;
  repeat
    match goal with
    | [ H : ?P -> _, H' : ?P |- _ ] =>
      specialize (H H')
    end;
  repeat
    (try apply in_or_app;
     apply in_app_or in iny;
     destruct iny as [iny | iny];
     match goal with
     | [ H : ?P -> ?GL, H' : ?P |- ?GL \/ _ ] =>
       left; apply H; assumption
     | [ H : ?P -> ?GR, H' : ?P |- _ \/ ?GR ] =>
       right; apply H; assumption
     | [ |- _ \/ _ ] =>
       right
     end).


Lemma in_subst_lfv : forall x y e1 e2,
    x <> y ->
    In y (lfv_exp e2) ->
    In y (lfv_exp (letsubst_exp e1 x e2)).
Proof.
  intros x y e1 e2; revert x y e1; induction e2.
  all: try solve [auto | in_subst_lfv_rec_case].
  - simpl.
    intros x y e1 xneq yin.
    destruct yin as [yeq | fls]; try contradiction.
    destruct(eq_letvar letvar5 x).
    + rewrite e in yeq; contradiction.
    + simpl; left; assumption.
  - simpl.
    intros x y e1 xne yin.
    repeat
      match goal with
      | [ H : forall (x y : letvar) (e1 : exp), _ |- _ ] =>
        specialize H with x y e1
      end.
    repeat
      match goal with
      | [ H : ?P -> _, H' : ?P |- _ ] =>
        specialize (H H')
      end.
      destruct(eq_letvar letvar5 x).
      + rewrite e.
        rewrite e in yin.
        try apply in_or_app;
          apply in_app_or in yin;
          destruct yin as [yin | yin].
        * left; apply IHe2_1; assumption.
        * right; assumption.
      + try apply in_or_app;
          apply in_app_or in yin.
        destruct yin as [yin | yin].
        * left; apply IHe2_1; assumption.
        * right. apply in_list_minus.
          apply in_list_minus in yin.
          destruct yin.
          constructor; try apply IHe2_2; assumption.
Qed.

Ltac type_exp_no_lfv_rec_case :=
  simpl;
  repeat match goal with
         | [ H : ?e1 = nil |- ?e1 ++ ?e2 = nil ] =>
           rewrite H; simpl
         end;
  auto.

Lemma notin_nil : forall {A : Set} (l : list A), (forall e, ~In e l) -> l = nil.
Proof.
  intros A l nin.
  induction l.
  - reflexivity.
  - elim (nin a).
    simpl; left; reflexivity.
Qed.

Lemma type_exp_no_lfv : forall g e t, type_exp g e t -> lfv_exp e = nil.
Proof.
  intros g e t te.
  induction te.
  all: try solve [auto | type_exp_no_lfv_rec_case].
  - apply notin_nil.
    simpl.
    rewrite IHte1.
    simpl.
    intros x in_e_let.
    rewrite in_list_minus in in_e_let.
    destruct in_e_let.
    simpl in H0.
    pose proof in_nil as inn.
    specialize inn with (A := letvar).
    rewrite <- IHte2 in inn.
    destruct (inn x).
    apply in_subst_lfv; auto.
Qed.

Lemma letsubst_fv_exp : forall x y e1 e2,
      In y (fv_exp (letsubst_exp e1 x e2)) ->
      In y (fv_exp e1) \/ In y (fv_exp e2).
Proof.
  intros x y e1 e2 iny.
  induction e2.
  all:
    try solve
        [ auto
        | simpl;
          simpl in iny;
          repeat
            (apply in_app_or in iny;
             destruct iny as [iny | iny];
             firstorder)].
  - simpl in iny.
    destruct (eq_letvar letvar5 x); auto.
  - simpl.
    simpl in iny.
    apply in_app_or in iny;
      destruct iny as [iny | iny];
      firstorder.
    destruct (eq_letvar letvar5 x).
    + right; apply in_or_app; right; assumption.
    + specialize (IHe2_2 iny).
      destruct IHe2_2.
      * left; assumption.
      * right; apply in_or_app; right; assumption.
Qed.

Ltac var_in_fvs :=
  try apply in_or_app;
  first [ assumption | left; assumption | right; assumption | right; var_in_fvs].

Ltac strengthen_rec_case C :=
  apply C;
  try assumption;
  progress repeat match goal with
  | [ H1 : ?P1, H2 : ~ In ?x _, IH : ?P1 -> ~ In ?x _ -> ?P2 |- ?P2 ] =>
    apply IH; first [apply H1 | intro x_in; elim H2; simpl; var_in_fvs]
  end.

(*
Lemma fv_subst_notin : forall x e e',
    ~In x (fv_exp e) ->
    ~In x (fv_exp (subst_exp e x e')).
Proof.
  intros x e e'.
  remember (subst_exp e x e') as se.
  induction se.
  - intros ninxe.
    destruct (eq_var var5 x).
    rewrite e0 in Heqse.
    
      try (simpl in inxsubst; inversion inxsubst).
      contradiction.
  - intros e x nxe inxsubst.
    simpl in inxsubst; inversion inxsubst.
  - intros e x nxe inxsubst.
    simpl in inxsubst.
    apply in_app_or in inxsubst.
    inversion inxsubst.
    apply IHe'1.
*)

Lemma exp_strengthening : forall g e t x,
    type_exp (cons x g) e t -> ~ In x (fv_exp e) -> type_exp g e t.
Proof.
  intros g e t x te n_in_fv.
  fold gamma in g.
  remember (x :: g) as g'.
  induction te.
  - rewrite Heqg' in H.
    rewrite Heqg' in H0.
    simpl in n_in_fv.
    inversion H0.
    inversion H.
    + symmetry in H5.
      elim n_in_fv.
      left; assumption.
    + apply t_var.
      apply H5.
      apply H4.
  - rewrite Heqg' in H.
    inversion H.
    exact (t_int g num5 sz H3).
  - strengthen_rec_case (t_load g e1 e2 ed sz nat5).
  - strengthen_rec_case (t_store g e1 e2 ed sz e3).
  - strengthen_rec_case (t_aop g e1 aop5 e2).
  - strengthen_rec_case (t_lop g e1 lop5 e2 sz).
  - strengthen_rec_case (t_uop g uop5 e1).
  - strengthen_rec_case (t_cast g cast5 sz e nat5).
  -  apply t_let.
     progress repeat match goal with
                     | [ H1 : ?P1, H2 : ~ In ?x _, IH : ?P1 -> ~ In ?x _ -> ?P2 |- ?P2 ] =>
                       apply IH; first [apply H1 | intro x_in; elim H2; simpl]
                     end.
     try apply in_or_app.
     left; assumption.
     progress repeat match goal with
                     | [ H1 : ?P1, H2 : ~ In ?x _, IH : ?P1 -> ~ In ?x _ -> ?P2 |- ?P2 ] =>
                       apply IH; first [apply H1 | intro x_in; elim H2; simpl]
                     end.
     try apply in_or_app.
     apply (letsubst_fv_exp (letvar_var id5 t) x).
     assumption.
  - apply t_unknown.
    inversion H.
    + rewrite Heqg' in H0; inversion H0.
    + rewrite Heqg' in H2.
      inversion H2.
      rewrite H5 in H1; assumption.
  - strengthen_rec_case t_ite.
  - strengthen_rec_case (t_extract g sz1 sz2 e sz).
  - strengthen_rec_case  t_concat.
Qed.

Ltac exp_exchange_simple_base G :=
  match goal with
  | [ H : typ_gamma G |- _ ] =>
    inversion H as [| G' id1' t1' notin_id1' G'_wf];
    inversion G'_wf as [| g' id2' t2' notin_id2' g'_wf];
    apply tg_cons;
    first [intro notin_id2; inversion notin_id2; contradiction
          | apply tg_cons; assumption]
  end.

(*
Lemma exp_exchange : forall id1 id2 t1 t2 g e t,
    id1 <> id2 ->
    ~ In id1 (map var_id g) ->
    ~ In id2 (map var_id g) ->
    type_exp ((var_var id1 t1) :: (var_var id2 t2) :: g) e t ->
    type_exp ((var_var id2 t2) :: (var_var id1 t1) :: g) e t.
Proof.
  intros id1 id2 t1 t2 g e t idneq id1_nin id2_nin te.
  remember (var_var id1 t1 :: var_var id2 t2 :: g) as G12.
  induction te.
  - rewrite HeqG12 in H.
    simpl in H.
    apply t_var.
    + simpl.
      firstorder.
    + inversion H0 as [| G' id1' t1' notin_id1' G'_wf];
        rewrite HeqG12 in H1; inversion H1.
      rewrite H3 in notin_id1'.
      inversion G'_wf as [| g' id2' t2' notin_id2' g'_wf].
      repeat (apply tg_cons;
              try first [intro notin_id2; inversion notin_id2; contradiction
                        | try apply tg_cons; assumption]).
      rewrite H5 in G'_wf.
      inversion G'_wf.
      assumption.
      

exp_exchange_simple_base (var_var id1 t1 :: var_var id2 t2 :: g).
  - apply t_int.
    exp_exchange_simple_base (var_var id1 t1 :: var_var id2 t2 :: g).
  - apply (t_load _ e1 e2 ed sz nat5); auto.
  - apply (t_store _ e1 e2 ed sz e3); auto.
  - apply t_aop; auto.
  - apply (t_lop _ e1 lop5 e2 sz); auto.
  - apply t_uop; auto.
  - apply (t_cast _ _ _ _ nat5); auto.
  - apply t_let.
    auto.
    apply type_exp_typ_gamma in te2.
    inversion te2.
    apply IHte2.
    + intro id5_in_g0.
      apply H1.
      simpl.
      inversion id5_in_g0.
      * simpl in H1; left; assumption.
      * right; right; assumption.
    + intro eq25.
      apply H1.
      simpl.
      right; left; assumption.
    + intro id2_in_g0.
      destruct id2_in_g0;  contradiction.
    + 
     rewrite H.
      destruct id5_in_g0.
      * simpl in H.
        apply type_exp_typ_gamma in te2.
        inversion te2.
        destruct H2.
        rewrite H.
        simpl; left; reflexivity.
      *
      inversion te2.
      inversion H0.
      fold var_id in H6.
      simpl in H6.
      
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  - apply t_aop; auto.
  -
*)

(*
Definition as_imm_type

Fixpoint infer (g : gamma) (e : exp) : option type :=
  match e with
  | exp_var (var_var id t) => if In (var_var id t) g then Some t else None
  | exp_letvar (letvar_var _ t) => None
  | exp_int (existT _ sz _) => Some (type_imm sz)
  | exp_load em ew _ sz =>
    emt <- infer gamma em;
      ewt <- infer gama ew;
      wsz <- as_imm_type ewt;
 *)

Lemma type_exp_unique : forall g e t,
    type_exp g e t -> forall t', type_exp g e t' -> t = t'.
Proof.
  intros g e t te;
  induction te;
    intros t0 t0e;
    inversion t0e.
  all: try reflexivity.
  all: try match goal with
    | [ IH : forall t', type_exp ?g ?e t' -> ?GL = t',
          H : type_exp ?g ?e ?GR |- ?GL = ?GR ] =>
      apply IH; assumption
    end.
  - repeat match goal with
           | [ IH : forall t', type_exp ?g ?e t' -> _ = t',
                 H : type_exp ?g ?e _ |- _ ] =>
             apply IH in H
           end.
    inversion H2.
    inversion H4.
    reflexivity.
Qed.

(* TODO: put in bil.ott if works well *)
Bind Scope bil_exp_scope with exp.

Notation " [ es ./ x ] e " := (letsubst_exp es x e) (at level 9) : bil_exp_scope.

Local Open Scope bil_exp_scope.

Lemma subst_inversion : forall es x e,
    e <> exp_letvar x -> ~ In x (lfv_exp es) ->
    (forall y, [es./x]e = exp_var y -> e = exp_var y) /\
    (forall y, [es./x]e = exp_letvar y -> e = exp_letvar y /\ x <> y) /\
    (forall w, [es./x]e = exp_int w -> e = exp_int w) /\
    (forall e1 e2 ed sz, [es./x]e = exp_load [es./x]e1 [es./x]e2 ed sz ->
                         e = exp_load e1 e2 ed sz) /\
    (forall e1 e2 ed sz e3, [es./x]e = exp_store [es./x]e1 [es./x]e2 ed sz [es./x]e3 ->
                            e = exp_store e1 e2 ed sz e3) /\
    (forall e1 op e2, [es./x]e = exp_binop [es./x]e1 op [es./x]e2 -> e = exp_binop e1 op e2) /\
    (forall op e1, [es./x]e = exp_unop op [es./x]e1 -> e = exp_unop op e1) /\
    (forall c sz e1, [es./x]e = exp_cast c sz [es./x]e1 -> e = exp_cast c sz e1) /\
    (forall e1 e2, [es./x]e = exp_let x [es./x]e1 e2 -> e = exp_let x e1 e2 ) /\
    (forall y e1 e2, [es./x]e = exp_let y [es./x]e1 [es./x]e2 -> x <> y -> e = exp_let y e1 e2 ) /\
    (forall str t, [es./x]e = exp_unk str t -> e = exp_unk str t) /\
    (forall e1 e2 e3, [es./x]e = exp_ite [es./x]e1 [es./x]e2 [es./x]e3 -> e = exp_ite e1 e2 e3) /\
    (forall sz1 sz2 e1, [es./x]e = exp_ext sz1 sz2 [es./x]e1 -> e = exp_ext sz1 sz2 e1) /\
    (forall e1 e2, [es./x]e = exp_concat [es./x]e1 [es./x]e2 -> e = exp_concat e1 e2).
Proof.
  intros es x e enl nisl.
  repeat constructor; induction e; simpl.
  all: try solve [try destruct (eq_letvar letvar5 x); intros; inversion H;
                  try first [reflexivity
                            | elim enl; f_equal; assumption]].
  simpl in H.
  destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).
  assumption.
  simpl in H.
  destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).
  intro.
  inversion H.
  elim n.
  rewrite H0.
  assumption.
Admitted.

(*
  intros.
  inversion H.


  simpl.
  all: try solve [intros; inversion H | auto].
  destruct (eq_letvar letvar5 x).
  rewrite e in enl; contradiction.
  auto.
  inversion H.

  all: try (destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction)).
  simpl.
  try destruct (eq_letvar letvar5 x).
  rewrite e in enl; contradiction.
  auto.
  inversion H.
  simpl; try destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).
  auto.
  auto.
  - rewrite <- H.
    simpl.
    destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).
    reflexivity.
  - simpl in H.
    destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).
    inversion H.
    rewrite <- H1; intro eq; symmetry in eq; contradiction.
  - 
    destruct (eq_letvar letvar5 x); try (rewrite e in enl; contradiction).



  constructor.
  intros y H.
  inversion H.
  constructor.
  assumption.
  inversion H.
  simpl;
    intros;
    destruct (eq_letvar letvar5 x);
    solve [rewrite e in enl; contradiction | auto].
  constructor.
  induction e; simpl; try solve [auto | intros y H; inversion H].
  intros;
    destruct (eq_letvar letvar5 x).
  rewrite e in enl; contradiction.
  inversion H.
  rewrite H1 in n.
  firstorder.
  constructor.
  induction e; simpl; try solve [auto | intros y H; inversion H].
  intros;
    destruct (eq_letvar letvar5 x).
  rewrite e in enl; contradiction.
  auto.
  constructor.
  - induction e; simpl; try solve [auto | intros; inversion H].
    + intros.
      destruct (eq_letvar letvar5 x).
      rewrite e in enl; contradiction.
      inversion H.
    + intros.
      inversion H.
      destruct (eq_exp e0 (exp_letvar x));
        destruct (eq_exp e1 (exp_letvar x));
        destruct (eq_exp e2 (exp_letvar x));
        destruct (eq_exp e3 (exp_letvar x)).
      * rewrite e, e4, e5, e6.
        reflexivity.
      * rewrite e5 in H2.
        simpl in H2.
        destruct (eq_letvar x x); try contradiction.
        

Lemma subst_eq_esubst : forall e x es, es = [es./x]e -> e = exp_letvar x \/ e = es.
Proof.
  intros e x.
  induction e; simpl; auto; intros es es_eq.
  - destruct (eq_letvar letvar5 x).
    + rewrite e.
      left; reflexivity.
    + right; symmetry; assumption.
  - inversion es_eq.


elim n.
        

        rewrite e in H1.
        rewrite e4 in H1.
        
        repeat match goal with
             |

  constructor.
  *)

Lemma letsubst_inversion_var : forall es x e y,
    e <> exp_letvar x -> [es./x]e = exp_var y -> e = exp_var y.
Proof.
  intros es x e y enl.
  induction e.
  all: simpl; try solve [auto | intro H; inversion H].
  simpl;
    intros;
    destruct (eq_letvar letvar5 x);
    solve [rewrite e in enl; contradiction | auto].
Qed.


Lemma no_typed_letvar : forall g x t, ~ type_exp g (exp_letvar x) t.
Proof.
  intros g x e te.
  inversion te.
Qed.

Ltac letsubst_unused_rec_case :=
  f_equal;
  let H := match goal with
             [ H : forall x es, ~In x _ -> [es./x]?e = ?e |- [_./_]?e = ?e] => H
           end in
  apply H;
  auto;
  let nin := match goal with
               [ nin : ~In _ _ |- _ ] => nin
             end in
  intro; elim nin;
  apply in_or_app;
  first [left; assumption
        | right; apply in_list_minus;
          solve [firstorder]
        | solve [firstorder]].

Lemma letsubst_unused : forall x es e,
    ~In x (lfv_exp e) -> [es./x]e = e.
Proof.
  intros x es e; revert x es.
  induction e;
    simpl;
    auto;
    intros x es nin;
    try solve[letsubst_unused_rec_case].
  - destruct (eq_letvar letvar5 x);
      [> elim nin; left; assumption
      | reflexivity].
  - destruct (eq_letvar letvar5 x);
    letsubst_unused_rec_case.
Qed.

Ltac letsubst_distributes_rec_case :=
  f_equal;
  match goal with
    [ IH : forall x y es1 es2,
        _ -> _ -> _ -> [es1./x]([es2./y]?e) = [es2./y]([es1./x]?e)
        |- [?es1 ./ ?x] ([?es2 ./ ?y] ?e) = [?es2 ./ ?y] ([?es1 ./ ?x] ?e) ] =>
    apply IH; assumption
  end.

Lemma letsubst_distributes : forall x y es1 es2 e,
    ~In y (lfv_exp es1) ->
    lfv_exp es2 = nil ->
    x <> y -> ([es1./x][es2./y]e) = [es2./y][es1./x]e.
  intros x y es1 es2 e; revert x y es1 es2.
  induction e;
        intros x y es1 es2 yni1 es2_closed xne;
        simpl;
        try solve [auto | letsubst_distributes_rec_case].
  - destruct (eq_letvar letvar5 y).
    + destruct (eq_letvar letvar5 x).
      * rewrite <- e in xne;
          rewrite <- e0 in xne;
          contradiction.
      * simpl.
        destruct (eq_letvar letvar5 y).
        apply letsubst_unused;
          rewrite es2_closed;
          auto.
        rewrite e in n0.
        contradiction.
    + destruct (eq_letvar letvar5 x).
      * simpl.
        destruct (eq_letvar letvar5 x);
          rewrite letsubst_unused;
          tauto.
      * simpl.
        destruct (eq_letvar letvar5 x);
          destruct (eq_letvar letvar5 y);
          tauto.
  - destruct (eq_letvar letvar5 x) as [lv5xe | nlv5xe];
    destruct (eq_letvar letvar5 y)as [lv5ye | nlv5ye].
     + rewrite <- lv5xe in xne.
       rewrite <- lv5ye in xne.
       contradiction.
     + rewrite lv5xe.
       letsubst_distributes_rec_case.
     + rewrite lv5ye.
       letsubst_distributes_rec_case.
     + letsubst_distributes_rec_case.
Qed.

Ltac type_subst_rec_case' app_tac :=
  let t := match goal with
           | [ |- type_exp _ _ ?t ] => t
           end in
  try (destruct t; inversion tses1);
  first [app_tac | app_tac ()];
  try match goal with
      | [ H : forall x es1 es2 (ts t : type),
            type_exp ?G es1 ts ->
            type_exp ?G es2 ts ->
            type_exp ?G [es1./x]?e t ->
            type_exp ?G [es2./x]?e t |- _ ] =>
        apply H with (es1 := es1) (es2 := es2) (ts := ts)
      end; assumption.

Notation "g |-- e ::: t" := (type_exp g e t) (at level 99) : type_scope.


Lemma type_subst : forall x g es1 es2 e ts t,
    g |-- es1 ::: ts ->
    type_exp g es2 ts ->
    type_exp g ([es1 ./ x ] e) t ->
    type_exp g ([es2 ./ x ] e) t.
Proof.
  intros x g es1 es2 e ts t tes1 tes2 te.
(*
  destruct (eq_exp e (exp_letvar x)).
  - rewrite e0.
    simpl.
    destruct (eq_letvar x x); try contradiction.
    rewrite e0 in te.
    simpl in te.
    destruct (eq_letvar x x); try contradiction.
    pose proof type_exp_unique as teqts.
    specialize teqts with g es1 t ts.
    specialize (teqts te tes1).
    rewrite teqts.
    assumption. *)
  - generalize dependent es2.
    generalize dependent t.
    induction e;
      simpl;
      intros t te es2 tes2;
      try assumption.
    + destruct (eq_letvar letvar5 x).
      * match goal with
        | [ H : ?g |-- ?e ::: ?t,
                H' : ?g |-- ?e ::: ?t' |- _] =>
          apply type_exp_unique with (t := t') in H as teq;
            try assumption;
            try rewrite <- teq;
            assumption
        end.
        * assumption.
    + let x := match goal with
                 [ |- _ |-- ?e ::: _] =>
                 match e with context [[_./?x]_] => x
                 end end in
      let resolve_letvar :=
          fun ei IHe te =>
            let eq_e := fresh "eq_ei" in
            let neq_e := fresh "neq_ei" in
            destruct (eq_exp ei (exp_letvar x)) as [eq_e | neq_e];
              try rewrite eq_e;
              simpl;
              (try rewrite eq_e in IHe);
              (simpl in IHe);
              (try rewrite eq_e in te) in
      multimatch goal with
        [ IH : forall t, _ -> forall es, _ -> ?g |-- [es./x]?ei ::: t |- ?g |-- ?e ::: _] =>
        lazymatch e with context [[es./x]ei] =>
                       resolve_letvar ei IH te
        end
      end;
      simpl in te;
          destruct (eq_letvar x x); try contradiction;
            inversion te;
            apply t_load with (nat5 := nat0);
            first [assumption |
                   match goal with
                   | [ IH : forall t, _ -> forall es, _ -> ?g |-- [es./?x]?e ::: t
                                                      |- ?g |-- [?es./?x]?e ::: ?t ] =>
                     apply IH; assumption
                   | [ IH : forall t, _ -> forall es, _ -> ?g |-- es ::: t
                                                      |- ?g |-- ?e ::: ?t ] =>
                     apply IH; assumption
                   end].


match goal with
[ IH : forall t, _ -> forall es, _ -> ?g |-- [es./x]?ei ::: t |- ?g |-- ?e ::: _] =>
match e with context [[es./x]ei] => resolve_letvar e1 IHe1 te
end
end


let resolve_letvar := fun e1 IHe1 te =>
destruct (eq_exp e1 (exp_letvar x)) as [eq_e1 | neq_e1];
        try rewrite eq_e1;
        simpl;
        try rewrite eq_e1 in IHe1;
        simpl in IHe1;
        try rewrite eq_e1 in te;

 apply t_load with (nat5 := nat0);
      apply t_store;




      inversion H5.
      specialize (teqts H5 H6).
      specialize teqts with g es1 (type_mem nat0 nat5) ts.
      specialize (teqts H5 tes1).
      rewrite teqts.
      assumption.

simpl in te. 
      destruct (eq_letvar letvar5 x).
      elim n. inversion e. reflexivity.
      simpl in te.
      
apply t_var with (t := type5). constructor with (t := type5).
    + apply subst_inversion in Heqe';
      try (rewrite Heqe'; simpl; constructor);
        try( rewrite type_exp_no_lfv with (g := G) (t := ts); simpl);
        auto.
    + 


apply subst_inversion with (es := es2) in Heqe';
      try (rewrite Heqe'; simpl; constructor);
        try( rewrite type_exp_no_lfv with (g := G) (t := ts); simpl);
        auto.











    generalize dependent es1.
    generalize dependent ts.
    generalize dependent x.
    induction te;
      simpl;
      intros x enl ts es1 tes1 e_subst1_eq es2 tes2;
      symmetry in e_subst1_eq.
    + apply letsubst_inversion_var in e_subst1_eq;
        try (rewrite e_subst1_eq; simpl; constructor);
        assumption.
    + apply subst_inversion in e_subst1_eq;
      try (rewrite e_subst1_eq; simpl; constructor);
        try( rewrite type_exp_no_lfv with (g := G) (t := ts); simpl);
        auto.
    + apply subst_inversion with (es := es2) in e_subst1_eq;
      try (rewrite e_subst1_eq; simpl; constructor);
        try( rewrite type_exp_no_lfv with (g := G) (t := ts); simpl);
        auto.

 apply subst_inversion in e_subst1_eq;
        try rewrite e_subst1_eq;
        first [ assumption
              | simpl; constructor].


  all: try solve [auto | assumption].
  - destruct (eq_letvar letvar5 x).
    pose proof type_exp_unique as teu.
    specialize teu with (g := g) (t := ts) (t' := t).
    specialize (teu es1 tes1 tses1) as teu1.
    rewrite <- teu1.
    assumption.
    assumption.
  - (* TODO: improve this tactic! *)
    let app_tac := (apply t_load with nat0) in
    type_subst_rec_case app_tac.
  - let app_tac := (apply t_store) in
    type_subst_rec_case app_tac.
  - let app_tac :=
        fun _ =>
          let sz := match goal with
                    | [ _ : type_exp _ _ (type_imm ?sz) |- _ ] => sz
                    end in
          first [ apply t_aop | apply t_lop with sz] in
    let t := match goal with
             | [ |- type_exp _ _ ?t ] => t
             end in
    type_subst_rec_case app_tac.
  - let app_tac := (apply t_uop) in
    type_subst_rec_case app_tac.
  - (* TODO: improve this tactic! *)
    let app_tac := (apply t_cast with nat0) in
    type_subst_rec_case app_tac.
  - destruct (eq_letvar letvar5 x);
      destruct letvar5;
      apply t_let;
      inversion tses1.
    + apply IHe1 with (es1 := es1) (ts := ts);  assumption.
    + apply IHe2 with (es2 := [es2./x]e1) (es1 := [es1./x]e1) (ts:=type5);
        try apply IHe1 with (es1:=es1) (es2:=es2) (ts := ts);
        assumption.
    + apply IHe1 with (es1 := es1) (ts := ts);  assumption.
    + rewrite letsubst_distributes with (es1 := [es2 ./ x] e1).
      inversion H6.
      

 apply IHe2 with (es2 := [es2./x]e1) (es1 := [es1./x]e1) (ts:=type5);
        try apply IHe1 with (es1:=es1) (es2:=es2) (ts := ts);
        assumption.

    rewrite e in tses1.
    apply t_let.
destruct letvar5.
    
    apply t_let.
    simpl in tses1.
    destruct t; inversion tses1.
      apply t_let.
    apply IHe1 with (ts := type5).
    
destruct (eq_letvar letvar5 x).
    + destruct letvar5.
      apply t_let.
      apply t_let with (e1 := [es2./x]e1) (t' := t).

    type_subst_rec_case app_tac.
  - 





Ltac type_subst_rec_case app_tac :=
  let t := match goal with
           | [ |- type_exp _ _ ?t ] => t
           end in
  try (destruct t; inversion tses1);
  first [app_tac | app_tac ()];
  try match goal with
      | [ H : forall ts t : type,
            _ -> _ ->
            type_exp ?G [_./?x]?e t ->
            type_exp ?G [_./?x]?e t |- _ ] =>
        apply H with (ts := ts)
      end; assumption.







destruct t; inversion tses1.
    apply t_load with (nat5 := nat0);
      match goal with
      | [ H : forall ts t : type, _ -> _ ->
                                  type_exp ?G [_./?x]?e t ->
                                  type_exp ?G [_./?x]?e t |- _ ] =>
        apply H with (ts := ts)
      end; try assumption.
  - destruct t; inversion tses1.
    apply t_store;
      try match goal with
          | [ H : forall ts t : type,
                _ -> _ ->
                type_exp ?G [_./?x]?e t ->
                type_exp ?G [_./?x]?e t |- _ ] =>
            apply H with (ts := ts)
          end; assumption.

    constructor.
    all: try assumption.
    apply IHe1 with (ts := ts).
    all: try assumption.
    apply IHe2 with (ts := ts).
    all: try assumption.
    apply IHe3 with (ts := ts).
    all: try assumption.

  remember  ([es1./x] e) as e'.
  induction tses1.
  - symmetry in Heqe'.
    apply subst_inversion_var in Heqe'.
    + rewrite Heqe';
        simpl;
        constructor;
        assumption.
    + intro eeql.
      

pose proof subst_inversion_var as s_inv_var.
    specialize (s_in_var 

  all: try solve [rewrite <- Heqe'; auto].
  

Ltac preservation_rec_case C :=
  match goal with
  | [ IH : ?A -> forall t : type, ?P t -> ?Q t,
        H : ?P ?t',
        td : ?A |- _ ] =>
    specialize (IH td) with t';
    apply C;
    try apply IH; assumption
  end.

Ltac preservation_base_case C :=
  match goal with
  | [ H : type_exp ?d _ _ |- type_exp ?d _ _] =>
    apply C;
    apply type_exp_typ_gamma in H;
    assumption
  end.


Lemma exp_preservation : forall d e e' t,
    type_delta d ->
    type_exp (map fst d) e t ->
    exp_step d e e' ->
    type_exp (map fst d) e' t.
Proof.
  intros d e e' t td te es.
  generalize dependent t.
  induction es; intros t0 te; inversion te.
  - pose proof in_delta_types as v_types.
    specialize v_types with id5 t0 v delta5.
    rewrite <- H1 in H0.
    rewrite H5 in H0.
    specialize (v_types td H0).
    rewrite <- H3.
    rewrite <- (app_nil_r G).
    rewrite <- (app_nil_l (G ++ nil)).
    apply (exp_weakening nil G nil).
    + simpl; auto.
    + simpl; rewrite app_nil_r; rewrite H3; assumption.
  - rewrite H4 in H; contradiction.
  - preservation_rec_case (t_load (map fst delta5) e1 e2' ed sz nat5).
  - preservation_rec_case (t_load (map fst delta5) e1' v2 ed sz nat5).
  - match goal with
    | [ H : type_exp ?d ?eh _ |- type_exp ?d ?e _ ] =>
      match eh with
      | context c [e] =>
        inversion H
      end
    end.
    assumption.
  - preservation_base_case t_unknown.
  - inversion H8.
    apply (t_load (map fst delta5) _ _ ed _ nat5);  assumption.
  - preservation_base_case t_unknown.
  - rewrite H4 in H11.
    inversion H11.
    rewrite H21 in H2.
    elim (n_Sn sz').
    omega.
  - rewrite H4 in H11.
    inversion H11.
    rewrite H21 in H2.
    elim (n_Sn sz').
    omega.
  - preservation_rec_case t_store.
  - preservation_rec_case t_store.
  - preservation_rec_case t_store.
  - rewrite H5 in H16.
    inversion H16.
    rewrite H27 in H3.
    elim (n_Sn sz').
    omega.
  - rewrite H5 in H16.
    inversion H16.
    rewrite H27 in H3.
    elim (n_Sn sz').
    omega.
  - apply t_let.
    match goal with
    | [ IH : ?A -> forall t : type, ?P t -> ?Q t,
          H : ?P ?t',
          td : ?A |- _ ] =>
      specialize (IH td) with t';
        try apply IH; assumption
    end.
    

  - strengthen_rec_case (t_aop g e1 aop5 e2).
  - strengthen_rec_case (t_lop g e1 lop5 e2 sz).
  - strengthen_rec_case (t_uop g uop5 e1).
  - strengthen_rec_case (t_cast g cast5 sz e nat5). apply t_load.

  Lemma wf_all_val : forall d x v, delta_wf d -> In (x,v) d -> is_val_of_exp v.
  Proof.
    intros d x v wf x_in.
    induction wf.
    - contradiction.
    - destruct x_in as [H_in | H_in].
      + inversion H_in.
        rewrite <- H3; assumption.
      + apply IHwf.
        assumption.
  Qed.

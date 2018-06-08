Require Import List.

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

(* all free and bound variables *)
Fixpoint vars_in_exp (e_5:exp) : list var :=
  match e_5 with
  | (exp_var var5) => (cons var5 nil)
  | (exp_int word5) => nil
  | (exp_load e1 e2 endian5 nat5) => (app (vars_in_exp e1) (vars_in_exp e2))
  | (exp_store e1 e2 endian5 nat5 e3) => (app (vars_in_exp e1)
                                              (app (vars_in_exp e2) (vars_in_exp e3)))
  | (exp_binop e1 bop5 e2) => (app (vars_in_exp e1) (vars_in_exp e2))
  | (exp_unop uop5 e1) => ((vars_in_exp e1))
  | (exp_cast cast5 nat5 e) => ((vars_in_exp e))
  | (exp_let var5 e1 e2) => (app (vars_in_exp e1) (cons var5 (vars_in_exp e2)))
  | (exp_unk string5 type5) => nil
  | (exp_ite e1 e2 e3) => (app (vars_in_exp e1) (app (vars_in_exp e2) (vars_in_exp e3)))
  | (exp_ext nat1 nat2 e) => (vars_in_exp e)
  | (exp_concat e1 e2) => (app (vars_in_exp e1) (vars_in_exp e2))
end.

Lemma in_list_minus : forall {A} (l l' : list A) (e : A) {dec},
    In e (list_minus dec l l') -> In e l.
  intros A l l' e dec e_in.
  induction l.
  - simpl in e_in; contradiction.
  - simpl in e_in.
    simpl.
    destruct (list_mem dec a l').
    + apply IHl in e_in; right; assumption.
    + destruct e_in.
      * left; assumption.
      * right; apply IHl; assumption.
Qed.

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

Definition var_id := (fun v => match v with var_var id _ => id end).

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
    apply (t_load _ _ _ _ _ nat5); auto.
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
    apply t_let.
    + apply IHet1; assumption.
    + rewrite app_comm_cons.
      apply (IHet2 (var_var id5 t :: g)).
      * rewrite <- app_comm_cons.
        rewrite HeqG.
        reflexivity.
      * rewrite <- app_comm_cons.
        apply tg_cons.
        -- 

Ltac exp_exchange_simple_base G :=
  match goal with
  | [ H : typ_gamma G |- _ ] =>
    inversion H as [| G' id1' t1' notin_id1' G'_wf];
    inversion G'_wf as [| g' id2' t2' notin_id2' g'_wf];
    apply tg_cons;
    first [intro notin_id2; inversion notin_id2; contradiction
          | apply tg_cons; assumption]
  end.

Require Import Coq.Program.Equality.

Lemma exp_exchange : forall id1 id2 t1 t2 g e t,
    id1 <> id2 ->
    ~ In id1 (map var_id g) ->
    ~ In id2 (map var_id g) ->
    type_exp ((var_var id1 t1) :: (var_var id2 t2) :: g) e t ->
    type_exp ((var_var id2 t2) :: (var_var id1 t1) :: g) e t.
Proof.
  intros id1 id2 t1 t2 g e t idneq id1_nin id2_nin te.
  dependent induction te.

 (* remember ((var_var id1 t1) :: (var_var id2 t2) :: g) as G in te.*)
  - apply t_var.
   (* rewrite HeqG in H. *)
    + simpl.
      inversion H.
      * right; left; assumption.
      * inversion H1.
        -- left; assumption.
        -- right; right; assumption.
    + exp_exchange_simple_base (var_var id1 t1 :: var_var id2 t2 :: g).
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


Ltac var_in_fvs :=
  try apply in_or_app;
  first [ assumption | left; assumption | right; assumption | right; var_in_fvs].

Ltac strengthen_rec_case C :=
  apply C;
  progress repeat match goal with
  | [ H1 : ?P1, H2 : ~ In ?x _, IH : ?P1 -> ~ In ?x _ -> ?P2 |- ?P2 ] =>
    apply IH; first [apply H1 | intro x_in; elim H2; simpl; var_in_fvs]
  end.

Lemma exp_strengthening : forall g e t x,
    type_exp (cons x g) e t -> ~ In x (vars_in_exp e) -> type_exp g e t.
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
  - 
  apply (t_let g id5 t e1 e2).
  progress repeat match goal with
  | [ H1 : ?P1, H2 : ~ In ?x _, IH : ?P1 -> ~ In ?x _ -> ?P2 |- ?P2 ] =>
    apply IH; first [apply H1 | intro x_in; elim H2; simpl]
  end.
  try apply in_or_app.
  left; assumption.
  

Lemma exp_weakening : forall g e t v,
    type_exp g e t -> typ_gamma (cons v g) -> type_exp (cons v g) e t.
Proof.
  intros g e t v te tg.
  induction te.
  - inversion tg.

Lemma expr_preservation : forall d e e' t,
    type_delta d ->
    type_exp (map fst d) e t ->
    exp_step d e e' ->
    type_exp (map fst d) e' t.
Proof.
  intros d e e' t td te es.
  induction es.
  





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

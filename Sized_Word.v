Require Import Arith.
Require Import Bool.
Require Import List.

Require Import bbv.Word.

Require Import Eqdep_dec.

Definition sized_word : Set := {sz : nat & (word sz)}.

Definition bbv := word.


Definition sized {sz} w : sized_word := existT _ sz w.

Definition as_size {s1 s2} (w : word s1) : s2 = s1 -> word s2.
intro eq; destruct eq.
exact w.
Defined.

(* As per the BAP implementation, lifting returns a result with the
   width of the first argument.
 *)
Definition sw_lift_binop_in {A} (op : forall sz, word sz -> word sz -> A sz)
           (w1 : sized_word) (w2 : sized_word)
  : A (projT1 w1) :=
let (sz1,w1') as s return A (projT1 s) := w1 in
let (sz2,w2') := w2 in
 op _ w1' ($ (# w2')).

Lemma lift_binop_in_equal_sizes : forall {A} op sz (w1 w2 : word sz),
    sw_lift_binop_in (A:=A) op (sized w1) (sized w2) = op sz w1 w2.
Proof.
intros A op sz w1 w2.
simpl.
rewrite -> natToWord_wordToNat.
reflexivity.
Qed.

Definition sw_lift_binop (op : forall sz, word sz -> word sz -> word sz)
           (w1 : sized_word) (w2 : sized_word) : sized_word :=
  existT word _ (sw_lift_binop_in op w1 w2).


Lemma lift_binop_equal_sizes : forall op sz (w1 w2 : word sz),
    sw_lift_binop op (sized w1) (sized w2) = existT _ _ (op sz w1 w2).
Proof.
intros op sz w1 w2.
unfold sw_lift_binop.
rewrite -> lift_binop_in_equal_sizes.
simpl.
reflexivity.
Qed.

Definition sw_lift_shiftop_in {A} (op : forall sz , word sz -> nat -> A sz)
           (w1 : sized_word) (w2 : sized_word)
  : A (projT1 w1) :=
  op _ (let (_,w1') as s return word (projT1 s) := w1 in w1')
     (wordToNat (sz:=(projT1 w2)) (let (sz,w2') as s return word (projT1 s) := w2 in w2')).

Definition sw_lift_shiftop (op : forall sz, word sz -> nat -> word sz)
           (w1 : sized_word) (w2 : sized_word) : sized_word :=
  existT word _ (sw_lift_shiftop_in op w1 w2).

(*TODO: implement all functions below this line *)

(* As per the BAP implementation, lifting returns a result with the
   width of the first argument.
 *)
Definition sw_lift_cmpop_in  (P : forall {sz}, word sz -> word sz -> Prop)
           (dec : forall sz (l r : word sz), {P l r} + {~ (P l r)})
           {sz1} {sz2} (w1 : word sz1) (w2 : word sz2)
  : {eq : sz1 = sz2 & {P w1 (as_size w2 eq) } + {~(P w1 (as_size w2 eq))}} + {sz1 <> sz2}.
destruct (eq_nat_decide sz1 sz2) as [eq | neq].
- apply eq_nat_eq in eq.
  constructor.
  exists eq.
  apply dec.
- constructor 2.
  intro H.
  apply neq.
  apply eq_eq_nat.
  apply H.
Defined.

Definition sw_lift_cmpop (P : forall sz, word sz -> word sz -> Prop)
           (dec : forall sz (l r : word sz), {P sz l r} + {~ (P sz l r)})
           (w1 : sized_word) (w2 : sized_word) : sized_word :=
  match sw_lift_cmpop_in P dec (projT2 w1) (projT2 w2) with
  | inleft eq_sz_and_dec =>
    let (eq, dec) := eq_sz_and_dec in
    match dec with
    | left _ => sized (wone 1)
    | right _ => sized (wzero 1)
    end
  | inright neq_sz => sized WO
  end.

Lemma cmpop_same_size_bool : forall (P : forall sz, word sz -> word sz -> Prop)
                                   (dec : forall sz (l r : word sz), {P sz l r} + {~ (P sz l r)})
                                   {sz1} (w1 : word sz1) {sz2} (w2 : word sz2),
    sz1 = sz2 -> sw_lift_cmpop P dec (sized w1) (sized w2) = sized (wone 1) \/
                 sw_lift_cmpop P dec (sized w1) (sized w2) = sized (wzero 1).
Proof.
intros P dec sz1 w1 sz2 w2 sz_eq.
unfold sw_lift_cmpop.
unfold sw_lift_cmpop_in.
simpl.
apply eq_eq_nat in sz_eq.
destruct (eq_nat_decide sz1 sz2).
- unfold as_size; destruct eq_nat_eq.
  destruct dec.
  + auto.
  + auto.
- contradiction.
Qed.

Definition sw_lt : sized_word -> sized_word -> sized_word := sw_lift_cmpop wlt wlt_dec.
Definition sw_slt : sized_word -> sized_word -> sized_word := sw_lift_cmpop wslt wslt_dec.

Definition sw_lift_uop (uop : forall sz, word sz -> word sz) (w : sized_word) : sized_word :=
  let (sz, w') := w in
  sized (uop sz w').

Require Import Omega.

Fixpoint ext'_lo {sz} (w : word sz) (lo : nat) : word (sz - lo).
refine (match lo as lo_ return word (sz - lo_) with
  | O => as_size w _
  | S lo' => match w in word sz_ return word (sz_ - (S lo')) with
             | WO => WO
             | @WS b sz' w' => ext'_lo sz' w' lo'
             end
  end).
omega.
Defined.

Fixpoint ext'_hi {sz} (w : word sz) (hi : nat) : word (S hi) :=
match w with
| WO => wzero(S hi)
| WS b w' => match hi as hi_ return word (S hi_) with
             | O => WS b WO
             | S hi' => WS b (ext'_hi w' hi')
             end
end.

Fixpoint ext'_hi_signed {sz} (w : word sz) (hi : nat) : word (S hi) :=
match w with
| WO => wzero (S hi) (* we assume a sign of 0 for 0-length words *)
| WS b WO => rep_bit (S hi) (WS b WO)
| WS b w' => match hi as hi_ return word (S hi_) with
             | O => WS b WO
             | S hi' => WS b (ext'_hi w' hi')
             end
end.

Definition ext' {sz} (w : word sz) (hi lo : nat) : word ((S hi) - lo) :=
  ext'_lo (ext'_hi w hi) lo.

Definition ext'_signed {sz} (w : word sz) (hi lo : nat) : word ((S hi) - lo) :=
  ext'_lo (ext'_hi_signed w hi) lo.

Definition ext (w : sized_word) (hi lo : nat) : sized_word :=
  let (sz, w') := w in
  sized (ext' w' hi lo).

Definition ext_signed (w : sized_word) (hi lo : nat) : sized_word :=
  let (sz, w') := w in
  sized (ext'_signed w' hi lo).


Definition sized_as_size : forall sz sz' (w1 : word sz) (eq : sz' = sz),
    sized w1 = sized (as_size w1 eq).
intros sz sz' w1 eq.
unfold sized.
rewrite eq.
simpl.
reflexivity.
Qed.

Lemma exist_inj : forall A R (sz : A) (w w': R sz),
    (forall x y : A, {x = y} + {x <> y}) ->
    (forall a (w w' : R a), {w = w'} + {w <> w'}) ->
    w = w' <-> existT R sz w = existT R sz w'.
Proof.
  intros A R sz w w' dec_a dec.
  split.
  - intro eq.
    rewrite eq.
    reflexivity.
  - intro eq.
    apply Eqdep_dec.inj_pair2_eq_dec;
      assumption.
Qed.

Definition eq_word (w1 w2 : sized_word) : {w1 = w2} + {w1 <> w2}.
  destruct w1.
  destruct w2.
  destruct (eq_nat_decide x x0).
  - apply eq_nat_eq in e.
    symmetry in e.
    rewrite (sized_as_size x x0) with (eq0 := e).
    unfold sized.
    destruct (weq (as_size w e) w0).
    + left.
      f_equal.
      assumption.
    + right.
      intro exeq.
      apply exist_inj in exeq.
      contradiction.
      intros x1 y.
      destruct (eq_nat_decide x1 y).
      apply eq_nat_eq in e0.
      left; assumption.
      right.
      intro xeqy.
      elim n0.
      apply eq_eq_nat.
      assumption.
      apply weq.
  - right.
      intro exeq.
      elim n.
      apply eq_eq_nat.
      apply projT1_eq in exeq.
      simpl in exeq.
      assumption.
Defined.

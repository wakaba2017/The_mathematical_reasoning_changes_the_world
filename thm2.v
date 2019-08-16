Theorem thm2 :
  forall A B C : Prop,
    (A \/ B) ->
    (B -> C) ->
    (A -> ~C) ->
    ~C ->
    A.
(*

前提

  A:嬰児は精霊である。
  B;嬰児は人間である。
  C:嬰児は村に帰ってくる。

  A \/ B:嬰児は精霊か人間のいずれかである。
  B -> C:嬰児が人間ならば、嬰児は村に帰ってくる。
  A -> ~C:嬰児が精霊ならば、嬰児は村に帰ってこない。
  ~C:嬰児は村に帰ってこなかった。

結論

  A:嬰児は精霊だった。

*)
Proof.
  intros A B C AorB_is_true BtoC_is_true AtoNotC_is_true NotC_is_true.
  inversion AorB_is_true; subst; clear AorB_is_true.
  - (* Aが成り立つ場合 *)
    apply H.
  - (* Bが成り立つ場合 *)
    apply BtoC_is_true in H.
    unfold not in NotC_is_true.
    apply NotC_is_true in H.
    exfalso.
    apply H.
Qed.

From mathcomp
Require Import ssreflect.

Theorem thm2_ssr :
  forall A B C : Prop,
    (A \/ B) ->
    (B -> C) ->
    (A -> ~C) ->
    ~C ->
    A.
Proof.
  move=> A B C AorB_is_true BtoC_is_true AtoNotC_is_true NotC_is_true.
  inversion AorB_is_true; subst; clear AorB_is_true.
  -
    done.
  -
    move: (BtoC_is_true H) => C_is_true.
    move: NotC_is_true.
    rewrite /not => CtoFalse_is_true.
    move: (CtoFalse_is_true C_is_true) => Hypothesis_is_False.
    done.
Qed.

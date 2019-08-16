Theorem thm1 :
  forall P Q : Prop,
    P ->
    (Q -> ~P) ->
    ~Q.
(*

前提

  P:
    15年前の10月10日に運動会が実行された。

  Q -> ~P:
    15年前の10月10日の朝に雨が降っていたら、
    その日に運動会は実行されなかった。

結論

  ~Q:
    15年前の10月10日の朝に雨は降っていなかった。

*)
Proof.
  intros P Q P_is_true QtoNotP_is_true.
  unfold not.
  intro Q_is_true. (* ゴールはFlaseに変わる。 *)
  apply QtoNotP_is_true in Q_is_true. (* Q_is_trueは~Pに変わる。 *)
  unfold not in Q_is_true.
  apply Q_is_true in P_is_true. (* p_is_trueはFalseに変わる。 *)
  assumption.
Qed.

Theorem thm1' :
  forall P Q : Prop,
    P ->
    (P -> ~Q) -> (* 二重否定をあらかじめ除去してしまった *)
    ~Q.
Proof.
  intros.
  apply H0 in H.
  assumption.
Qed.

Theorem thm1'' :
  forall P Q : Prop,
    P ->
    (~~P -> ~Q) ->
    ~Q.
Proof.
  intros.
  admit. (* 二重否定の除去はできない *)
Admitted.

From mathcomp
Require Import ssreflect.

Theorem thm1_ssr :
  forall P Q : Prop,
    P ->
    (Q -> ~P) ->
    ~Q.
Proof.
  move=> P Q P_is_true QtoNotP_is_true.
  rewrite /not => Q_is_true.
  move: (QtoNotP_is_true Q_is_true) => NotP_is_true.
  apply: NotP_is_true.
  done.
Qed.

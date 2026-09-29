From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51 P52 P53 P54 P55 P56.
Open Scope fo_scope.

(** ** Numerals substituted into a code, one variable after another.

    [FOSUBNUMS q c xs ys r]: substituting, in order, the numeral of
    each [y] for the corresponding variable [x] in the formula coded
    [c] gives the code [r]; each step is a substitution row of the
    checker's tables. *)

Fixpoint FOSUBNUMS (q : nat) (c : FOTerm) (xs : list nat) (ys : list FOTerm) (r : FOTerm)
    : FOFormula :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      FOExists q (FOExists (S q)
        (FOAnd (FONUMR y (FOVar (S q)))
          (FOAnd (FOTBLEX (FOnumeral 3) (FOnumeral x) (FOVar (S q)) c (FOVar q))
                 (FOSUBNUMS (S (S q)) (FOVar q) xs' ys' r))))
  | _, _ => FOEq c r
  end.

Lemma FOsubst_f_SUBNUMS : forall xs ys q c r z s,
  z < q -> 50 <= z -> z <> 802 -> z <> 803 -> z <> 804 -> FOtms_avoid [s] 802 805 ->
  FOsubst_f z s (FOSUBNUMS q c xs ys r) =
  FOSUBNUMS q (FOsubst_t z s c) xs (map (FOsubst_t z s) ys) (FOsubst_t z s r).
Proof.
  induction xs as [|x xs IH]; intros ys q c r z s Hzq H50 H1 H2 H3 Hs.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys]; [reflexivity|]. cbn [FOSUBNUMS map].
    rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_ex_ne by lia.
    rewrite !FOsubst_f_and, FOsubst_f_NUMR, FOsubst_f_TBLEX by (lia || avoid_tms).
    rewrite IH by (lia || avoid_tms).
    rewrite !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_numeral. reflexivity.
Qed.

Lemma FOsubst_ok_SUBNUMS : forall xs ys q c r z s,
  13 <= z -> FOtms_avoid [s] 2 50 -> FOtms_avoid [s] 802 805 ->
  FOtms_avoid [s] q (q + 2 * length xs) ->
  FOsubst_ok z s (FOSUBNUMS q c xs ys r) = true.
Proof.
  induction xs as [|x xs IH]; intros ys q c r z s Hz H1 H2 Hq.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys]; [reflexivity|]. cbn [FOSUBNUMS length] in *.
    apply FOsubst_ok_ex; [apply Hq; [left; reflexivity | lia | lia]|].
    apply FOsubst_ok_ex; [apply Hq; [left; reflexivity | lia | lia]|].
    apply FOsubst_ok_and; [apply FOsubst_ok_NUMR; [lia | exact H1 | exact H2]|].
    apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | apply H1; left; reflexivity]|].
    apply IH; [lia | exact H1 | exact H2 | intros t Ht w ? ?; apply (Hq t Ht); lia].
Qed.

Lemma FOfree_in_SUBNUMS : forall xs ys q c r w,
  (w < q \/ q + 2 * length xs <= w) -> FOtms_avoid (c :: r :: ys) w (S w) ->
  FOtms_avoid (c :: r :: ys) 13 18 -> FOtms_avoid (c :: r :: ys) 802 805 ->
  (18 <= q /\ (q + 2 * length xs <= 802 \/ 805 <= q) \/ xs = []) ->
  FOfree_in w (FOSUBNUMS q c xs ys r) = false.
Proof.
  induction xs as [|x xs IH]; intros ys q c r w Hw Hav H13 H802 Hq.
  - destruct ys; cbn [FOSUBNUMS]; cbn [FOfree_in]; apply Bool.orb_false_iff;
      split; apply Hav; first [left; reflexivity | right; left; reflexivity | lia].
  - destruct ys as [|y ys].
    + cbn [FOSUBNUMS FOfree_in]. apply Bool.orb_false_iff;
        split; apply Hav; first [left; reflexivity | right; left; reflexivity | lia].
    + destruct Hq as [[Hq1 Hq2]|Hq]; [|discriminate]. cbn [FOSUBNUMS length] in *.
      cbn [FOfree_in]. destruct (Nat.eqb_spec q w) as [_|Hqw]; [reflexivity|].
      destruct (Nat.eqb_spec (S q) w) as [_|HSqw]; [reflexivity|].
      rewrite !fv_and. apply Bool.orb_false_iff. split.
      * apply FOfree_in_NUMR_all; avoid_tms.
      * apply Bool.orb_false_iff. split.
        -- apply FOfree_in_TBLEX_all; avoid_tms.
        -- apply IH; [lia | avoid_tms | avoid_tms | avoid_tms | left; lia].
Qed.

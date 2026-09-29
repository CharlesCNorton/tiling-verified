From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17.
Open Scope fo_scope.

(** ** Bounds from pairing. *)

Lemma FOPrH_cpair_lt_l : forall n G a b c,
  FOPrH n G (FOcpairF a b c) -> FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc a) (FOSucc c)).
Proof.
  intros n G a b c H Hav.
  destruct (FOPrH_cpair_le_cf n G a b c Hav H) as [Ha _].
  apply FOPrH_le_succ_of_le; [exact Ha | avoid_tms].
Qed.

Lemma FOPrH_cpair_lt_r : forall n G a b c,
  FOPrH n G (FOcpairF a b c) -> FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) (FOSucc c)).
Proof.
  intros n G a b c H Hav.
  destruct (FOPrH_cpair_le_cf n G a b c Hav H) as [_ Hb].
  apply FOPrH_le_succ_of_le; [exact Hb | avoid_tms].
Qed.

(** ** The binary substitution step.

    [tc] codes a binary node [cpair ktag (cpair a b)]; the table maps
    [a], [b] to [a'], [b'] under tag [lktag]; the result [r] is
    [cpair rtag (cpair a' b')]. *)

Lemma FOPrH_substbin_intro : forall n G T x sc tc r ktag lktag rtag p a b a' b' p',
  FOPrH n G (FOcpairF (FOnumeral ktag) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral lktag) x sc a a') ->
  FOPrH n G (FOlookupT 28 T (FOnumeral lktag) x sc b b') ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral rtag) p' r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; r; p; a; b; a'; b'; p']) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; r; p; a; b; a'; b'; p']) 420 500 ->
  FOPrH n G (FOSTEP_substbin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc r ktag lktag rtag).
Proof.
  intros n G T x sc tc r ktag lktag rtag p a b a' b' p' Hk Hp La Lb Hp' Hr Hav Hav2.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOlookupT, FOtab_terms in *.
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOSTEP_substbin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  destruct (FOPrH_cpair_le_cf n G (FOnumeral rtag) p' r ltac:(avoid_tms) Hr) as [_ Lp'].
  destruct (FOPrH_cpair_le_cf n G a' b' p' ltac:(avoid_tms) Hp') as [La' Lb'].
  row_bex a'.
  { apply FOPrH_le_succ_of_le; [|avoid_tms].
    exact (FOPrH_le_trans _ _ _ _ _ La' Lp' ltac:(avoid_tms)). }
  row_bex b'.
  { apply FOPrH_le_succ_of_le; [|avoid_tms].
    exact (FOPrH_le_trans _ _ _ _ _ Lb' Lp' ltac:(avoid_tms)). }
  apply FOPrH_and_intro.
  { apply (FOPrH_lookup_rebase n G 28 60 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ La);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms]. }
  apply FOPrH_and_intro.
  { apply (FOPrH_lookup_rebase n G 28 82 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Lb);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms]. }
  row_bex p'; [apply FOPrH_le_succ_of_le; [exact Lp' | avoid_tms]|].
  apply FOPrH_and_intro; [exact Hp' | exact Hr].
Qed.

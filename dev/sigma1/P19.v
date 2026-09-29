From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18.
Open Scope fo_scope.

(** ** Step clauses introduced from component facts.

    Each lemma builds one step formula at base [50], the base the
    dispatch uses, from the pairing facts of the node and the rows of
    its children looked up at base [28]. *)

Ltac tab_open T :=
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len];
  unfold FOlookupT, FOtab_terms in *;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.

Ltac rebase_to B' L :=
  apply (FOPrH_lookup_rebase _ _ 28 B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L);
  [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].

Lemma FOPrH_stepbin_one : forall n G T w pc k tg p a b,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w a FOZero (FOnumeral 1)) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_bin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc (FOnumeral 1) k tg).
Proof.
  intros n G T w pc k tg p a b Hk Hp La Hav Hav2. tab_open T.
  unfold FOSTEP_bin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [rebase_to 56 La | apply FOPrH_refl].
Qed.

Lemma FOPrH_stepbin_zero : forall n G T w pc r k tg p a b,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w a FOZero FOZero) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w b FOZero r) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_bin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc r k tg).
Proof.
  intros n G T w pc r k tg p a b Hk Hp La Lb Hav Hav2. tab_open T.
  unfold FOSTEP_bin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 La | rebase_to 78 Lb].
Qed.

Lemma FOPrH_quant0_eq : forall n G T w pc k tg p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y w) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_quant0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc FOZero k tg).
Proof.
  intros n G T w pc k tg p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_quant0.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_quant0_ne : forall n G T w pc r k tg p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w bb FOZero r) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_quant0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc r k tg).
Proof.
  intros n G T w pc r k tg p y bb Hk Hp E L Hav Hav2. tab_open T.
  unfold FOSTEP_quant0.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | rebase_to 56 L].
Qed.

Lemma FOPrH_substquant_eq : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_substquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc pc k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_substquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_substquant_ne : forall n G T x sc pc r k p y bb bb' p',
  1 <= k ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 3) x sc bb bb') ->
  FOPrH n G (FOcpairF y bb' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb; bb'; p']) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb; bb'; p']) 420 500 ->
  FOPrH n G (FOSTEP_substquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r k).
Proof.
  intros n G T x sc pc r k p y bb bb' p' Hk1 Hk Hp E L Hp' Hr Hav Hav2. tab_open T.
  assert (Lp' : FOPrH n G (FOle (FOSucc p') r)).
  { destruct k as [|k']; [lia|].
    exact (FOPrH_cpair_lt n G (FOnumeral k') p' r Hr ltac:(avoid_tms)). }
  destruct (FOPrH_cpair_le_cf n G y bb' p' ltac:(avoid_tms) Hp') as [_ Lb'].
  unfold FOSTEP_substquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  row_bex bb'.
  { apply (FOPrH_le_trans n G (FOSucc bb') (FOSucc p') r); [| exact Lp' | avoid_tms].
    apply FOPrH_le_succ_of_le; [exact Lb' | avoid_tms]. }
  apply FOPrH_and_intro; [rebase_to 58 L|].
  row_bex p'; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hr ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp' | exact Hr].
Qed.

Lemma FOPrH_subokbin_one : forall n G T x sc pc r p a b,
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc a (FOnumeral 1)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc b r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_subokbin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r).
Proof.
  intros n G T x sc pc r p a b Hk Hp La Lb Hav Hav2. tab_open T.
  unfold FOSTEP_subokbin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 La | rebase_to 78 Lb].
Qed.

Lemma FOPrH_subokquant_eq : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1) k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_subokquant_nf : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 1) x bb FOZero FOZero) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1) k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E L Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [rebase_to 56 L | apply FOPrH_refl].
Qed.

Lemma FOPrH_subokquant_fr : forall n G T x sc pc r k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 1) x bb FOZero (FOnumeral 1)) ->
  FOPrH n G (FOlookupT 28 T FOZero y sc FOZero FOZero) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc bb r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r k).
Proof.
  intros n G T x sc pc r k p y bb Hk Hp E L1 L0 L4 Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 L1|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 78 L0 | rebase_to 100 L4].
Qed.

(** ** Variable leaves. *)

Lemma FOPrH_step2_var_eq : forall n G T x sc tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP2 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc sc).
Proof.
  intros n G T x sc tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP2. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step2_var_ne : forall n G T x sc tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y x)) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP2 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc tc).
Proof.
  intros n G T x sc tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP2. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step0_var_eq : forall n G T w tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y w) ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w tc (FOnumeral 1)).
Proof.
  intros n G T w tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP0. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step0_var_ne : forall n G T w tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y w)) ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w tc FOZero).
Proof.
  intros n G T w tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP0. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

(** ** Leaf clauses of the equation and falsum codes. *)

Lemma FOPrH_step4_eq : forall n G T x sc pc p,
  FOPrH n G (FOcpairF FOZero p pc) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p]) 420 500 ->
  FOPrH n G (FOSTEP4 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1)).
Proof.
  intros n G T x sc pc p Hc Hav Hav2. tab_open T.
  unfold FOSTEP4. apply FOPrH_or_intro_l.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc | apply FOPrH_refl].
Qed.

Lemma FOPrH_step4_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP4 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc (FOnumeral 1)).
Proof.
  intros. unfold FOSTEP4. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.

Lemma FOPrH_step3_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP3 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc pc).
Proof.
  intros. unfold FOSTEP3. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.

Lemma FOPrH_step1_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP1 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc FOZero).
Proof.
  intros. unfold FOSTEP1. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.

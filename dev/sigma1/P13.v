From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12.
Open Scope fo_scope.

(** ** Tables holding a list of rows.

    [FOlookups B T rs]: every row of [rs] is looked up in [T] at base
    [B].  [FOTBLROWS rs]: some valid table at the variables [2] through
    [12] holds every row of [rs]. *)

Definition FOrow : Type := (FOTerm * FOTerm * FOTerm * FOTerm * FOTerm)%type.

Definition FOrow_terms (rw : FOrow) : list FOTerm :=
  let '(tg, a1, a2, a3, r) := rw in [tg; a1; a2; a3; r].

Fixpoint FOrows_terms (rs : list FOrow) : list FOTerm :=
  match rs with
  | [] => []
  | rw :: rs' => FOrow_terms rw ++ FOrows_terms rs'
  end.

Fixpoint FOlookups (B : nat) (T : FOtab) (rs : list FOrow) : FOFormula :=
  match rs with
  | [] => FOTrue
  | (tg, a1, a2, a3, r) :: rs' => FOAnd (FOlookupT B T tg a1 a2 a3 r) (FOlookups B T rs')
  end.

Definition FOtab2 : FOtab :=
  mkTab (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
    (FOVar 10) (FOVar 11) (FOVar 12).

Definition FOTBLROWS (rs : list FOrow) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
       (FOlookups 28 FOtab2 rs)))))))))))).

Lemma FOrows_terms_app : forall rs1 rs2,
  FOrows_terms (rs1 ++ rs2) = FOrows_terms rs1 ++ FOrows_terms rs2.
Proof.
  induction rs1 as [|rw rs1 IH]; intros rs2; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma FOtms_avoid_rows_cons : forall rw rs lo hi,
  FOtms_avoid (FOrows_terms (rw :: rs)) lo hi ->
  FOtms_avoid (FOrow_terms rw) lo hi /\ FOtms_avoid (FOrows_terms rs) lo hi.
Proof.
  intros rw rs lo hi H. cbn in H. split; intros t Ht; apply H; apply in_or_app;
    [left | right]; exact Ht.
Qed.

Lemma FOsubst_f_lookups : forall x s B T rs, x < B ->
  FOtms_avoid (FOrows_terms rs) x (S x) ->
  FOsubst_f x s (FOlookups B T rs) = FOlookups B (FOtab_subst x s T) rs.
Proof.
  intros x s B T rs HB. induction rs as [|[[[[tg a1] a2] a3] r] rs IH]; intros Hav.
  - reflexivity.
  - apply FOtms_avoid_rows_cons in Hav. destruct Hav as [Hh Ht].
    cbn [FOlookups]. rewrite FOsubst_f_and. unfold FOlookupT.
    rewrite FOsubst_f_lookup by exact HB. rewrite (IH Ht).
    cbn [FOrow_terms] in Hh.
    rewrite (FOsubst_t_not_in tg x s) by (apply (Hh tg ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a1 x s) by (apply (Hh a1 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a2 x s) by (apply (Hh a2 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a3 x s) by (apply (Hh a3 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in r x s) by (apply (Hh r ltac:(in_list) x); lia).
    reflexivity.
Qed.

Lemma FOsubst_ok_lookups : forall x s B T rs, FOtm_avoid s B (B + 22) ->
  FOsubst_ok x s (FOlookups B T rs) = true.
Proof.
  intros x s B T rs Hs. induction rs as [|[[[[tg a1] a2] a3] r] rs IH].
  - reflexivity.
  - cbn [FOlookups]. apply FOsubst_ok_and; [apply FOsubst_ok_lookup; exact Hs | exact IH].
Qed.

Lemma FOfree_in_lookups : forall w B T rs, 2 <= w ->
  FOtms_avoid (FOtab_terms T ++ FOrows_terms rs) w (S w) ->
  FOfree_in w (FOlookups B T rs) = false.
Proof.
  intros w B T rs Hw. induction rs as [|[[[[tg a1] a2] a3] r] rs IH]; intros Hav.
  - reflexivity.
  - cbn [FOlookups]. rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + unfold FOlookupT. free_by FOlookup_free;
        match goal with E : FOin_tm w ?t = true |- _ =>
          rewrite (Hav t ltac:(cbn; in_list) w ltac:(lia) ltac:(lia)) in E; discriminate E
        end.
    + apply IH. intros t Ht. apply Hav. apply in_app_or in Ht.
      destruct Ht as [Ht|Ht]; apply in_or_app; [left; exact Ht|].
      right. cbn [FOrows_terms]. apply in_or_app. right. exact Ht.
Qed.

(** ** Tables holding three given rows. *)

Definition FOTBLEX3 (tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' : FOTerm)
  : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
    (FOAnd (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg a1 a2 a3 r)
    (FOAnd (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg' a1' a2' a3' r')
           (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg'' a1'' a2'' a3'' r'')))))))))))))).

Lemma FOPrH_tblex3_elim : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'' k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    2 122 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                  (FOAnd (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg a1 a2 a3 r)
                  (FOAnd (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg' a1' a2' a3' r')
                         (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg'' a1'' a2'' a3'' r'')))]) C ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' .-> C).
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' k C
    Hk Hk' HG HC Hr Hrk H.
  unfold FOTBLEX3.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.

Lemma FOPrH_tblex3_intro : forall n G T tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg' a1' a2' a3' r') ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg'' a1'' a2'' a3'' r'') ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r';
                                 tg''; a1''; a2''; a3''; r'']) 2 122 ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'').
Proof.
  intros n G T tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' HV H1 H2 H3 Hav.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOtab_terms in Hav. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOTBLEX3.
  tblex_intro_step ct Hav. tblex_intro_step dt Hav. tblex_intro_step c1 Hav.
  tblex_intro_step d1 Hav. tblex_intro_step c2 Hav. tblex_intro_step d2 Hav.
  tblex_intro_step c3 Hav. tblex_intro_step d3 Hav. tblex_intro_step cr Hav.
  tblex_intro_step dr Hav. tblex_intro_step len Hav.
  apply FOPrH_and_intro; [exact HV|].
  apply FOPrH_and_intro; [exact H1|].
  apply FOPrH_and_intro; [exact H2 | exact H3].
Qed.

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4.
Open Scope fo_scope.

(** ** A new row added to a valid table.

    The dispatch clause of the new row is supplied for every extension
    of [T]; the continuation receives the extension [T'] at the
    variables [k] .. [k+9], its validity, its inclusion of [T], and the
    lookup of the new row at base [28]. *)

Definition FOTBLNEW (T T' : FOtab) (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOAnd (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
           (td3 T') (tcr T') (tdr T') (tlen T'))
  (FOAnd (FOINCL T T')
         (FOlookup 28 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
            (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r)).

Lemma FOfree_in_INCL_any : forall w T T',
  2 <= w -> FOtms_avoid (FOtab_terms T ++ FOtab_terms T') w (S w) ->
  FOfree_in w (FOINCL T T') = false.
Proof.
  intros w T T' Hw Hav. unfold FOINCL, FOROWMAP.
  destruct (Nat.eq_dec 460 w) as [<-|H0]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by exact H0. rewrite FOfree_in_impl.
  apply Bool.orb_false_iff. split.
  - destruct (Nat.eq_dec 461 w) as [<-|H1]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by exact H1. free_fm.
  - destruct (Nat.eq_dec 462 w) as [<-|H2]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by exact H2.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + destruct (Nat.eq_dec 463 w) as [<-|H3]; [apply FOfree_in_ex_self|].
      rewrite FOfree_in_FOExists_neq by exact H3. free_fm.
    + free_fm.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOPATF _ _ _ _) = false =>
      apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

Lemma FOPrH_row_new : forall n G T tg a1 a2 a3 r k C,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOctx_avoid G' 18 122 -> FOctx_avoid G' 420 500 ->
     FOTabMono n G' T (FOtabx k (FOSucc (tlen T))) ->
     FOPrH n G' (FODISPCASES (FOVar k) (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3))
                   (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6)) (FOVar (k + 7))
                   (FOVar (k + 8)) (FOVar (k + 9)) (FOSucc (tlen T)) tg a1 a2 a3 r)) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 -> FOctx_avoid G k (k + 10) ->
  122 <= k -> k + 10 <= 400 ->
  (forall w, k <= w -> w < k + 10 -> FOfree_in w C = false) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) k (k + 10) ->
  FOPrH n (G ++ [FOTBLNEW T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G T tg a1 a2 a3 r k C HV HD HG1 HG2 HGk Hk1 Hk2 HC Hav1 Hav2 Hav3 H0.
  apply (FOPrH_text_elim n G T tg a1 a2 a3 r k C);
    [exact HG2 | exact HGk | lia | lia | exact HC | avoid_tms | avoid_tms |].
  assert (HavA : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 18 122).
  { unfold FOtabx, FOtab_terms at 2. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    avoid_tms. }
  assert (HavB : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 400 500).
  { unfold FOtabx, FOtab_terms at 2. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    avoid_tms. }
  assert (HavC : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 420 500) by avoid_tms.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (HX : FOPrH n G1 (FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r))
      by apply FOPrH_last;
    assert (HV1 : FOPrH n G1 (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                               (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T))) by wk HV;
    assert (C1 : FOctx_avoid G1 18 122);
    [ intros w ? ?; apply FOfree_ctx_app_inv; [apply HG1; lia|];
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil];
      unfold FOTEXT, FOtabx; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen]; free_fm |];
    assert (C2 : FOctx_avoid G1 420 500);
    [ intros w ? ?; apply FOfree_ctx_app_inv; [apply HG2; lia|];
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil];
      unfold FOTEXT, FOtabx; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen]; free_fm |]
  end.
  pose proof (FOPrH_text_mono n _ T _ tg a1 a2 a3 r HX eq_refl C2 HavC) as Hm.
  pose proof (HD _ (fun X HX => in_or_app _ _ _ (or_introl HX)) C1 C2 Hm) as HDC.
  destruct (FOPrH_row_add n _ T _ tg a1 a2 a3 r HV1 HX eq_refl HDC C1 C2 HavA HavB)
    as [HV' _].
  pose proof (FOPrH_text_lookup n _ 28 T _ tg a1 a2 a3 r HX eq_refl ltac:(lia) ltac:(lia)
                ltac:(avoid_tms) HavC) as HL.
  destruct Hm as [HI _].
  refine (FOPrH_cut _ _ (FOTBLNEW T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r) _ _ _).
  - unfold FOTBLNEW. apply FOPrH_and_intro; [exact HV'|].
    apply FOPrH_and_intro; [exact HI | exact HL].
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX'. apply in_app_or in HX'. destruct HX' as [HX'|[<-|[]]].
    + do 2 (apply in_or_app; left). exact HX'.
    + apply in_or_app. right. left. reflexivity.
Qed.

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
Open Scope fo_scope.

(** ** Freshness of the pattern and guard facts. *)

Lemma FOfree_in_PATF_any : forall w B env p d,
  2 <= w -> FOtms_avoid (d :: env) w (S w) -> FOfree_in w (FOPATF B env p d) = false.
Proof.
  intros w B env p d Hw Hav.
  destruct (FOfree_in w (FOPATF B env p d)) eqn:E; [exfalso | reflexivity].
  apply FOPATF_free in E. destruct E as [E|[E|E]].
  - apply existsb_exists in E. destruct E as [t [Ht E]].
    rewrite (Hav t (or_intror Ht) w ltac:(lia) ltac:(lia)) in E. discriminate E.
  - rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)) in E. discriminate E.
  - lia.
Qed.

Lemma FOfree_in_GUARDB_any : forall w c,
  2 <= w -> FOtms_avoid [c] w (S w) -> FOfree_in w (FOGUARDB c) = false.
Proof.
  intros w c Hw Hav. unfold FOGUARDB.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
  - free_by FOTBLVALID_free.
  - rewrite FOBexC_ltv.
    destruct (Nat.eq_dec 13 w) as [<-|?]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by assumption.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia | fr_tm].
    + free_by FOlookup_free.
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
  | |- _ => free_fm_core
  end.

(** ** Modus ponens under the matrix in a context whose free variables
    lie outside the eigenvariable ranges. *)

Lemma FOPrH_D2_gen : forall n G cores a b c,
  FOctx_avoid G 2 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n G (FOGUARDB c) ->
  FOtms_avoid [a; b; c] 1 500 ->
  FOPrH n G (FOPRMATx cores a .-> FOPRMATx cores b .-> FOPRMATx cores c).
Proof.
  intros n G cores a b c HG HP HB Hav.
  apply (FOPrH_PRMAT_elim_rename n G cores a 330);
    [lia | lia | intros w H1 H2; apply HG; lia | side | avoid_tms |].
  cbn [Nat.add].
  apply (FOPrH_PRMAT_elim_rename n _ cores b 260); [lia | lia | side | side | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1 : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                               (FOVar 343) (FOVar 344) (FOVar 345))) by wk_in;
    assert (D2 : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                               (FOVar 273) (FOVar 274) (FOVar 275))) by wk_in;
    assert (HP0 : FOPrH n Gc (FOPATF 52 [b; c] cpatImpl01 a)) by wk HP;
    assert (HB0 : FOPrH n Gc (FOGUARDB c)) by wk HB;
    assert (A0 : FOctx_avoid Gc 2 18) by ctx_list;
    assert (A1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (A2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (A3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G0 := Gc) in *
  end.
  clearbody G0. clear HP HB HG.
  refine (FOPrH_mp _ _ (FOGUARDB c) _ _ HB0).
  unfold FOGUARDB.
  do 11 (apply FOPrH_imp_exl; [free_ctx | free_fm |]).
  apply FOPrH_imp_andl. apply FOPrH_intro.
  apply FOPrH_imp_bexl; [free_ctx | free_fm |]. apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1' : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                                (FOVar 343) (FOVar 344) (FOVar 345))) by wk D1;
    assert (D2' : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                                (FOVar 273) (FOVar 274) (FOVar 275))) by wk D2;
    assert (HP1 : FOPrH n Gc (FOPATF 52 [b; c] cpatImpl01 a)) by wk HP0;
    assert (VB : FOPrH n Gc (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12))) by wk_in;
    assert (LK : FOPrH n Gc (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12) (FOnumeral 3) (FOSucc c) FOZero c
                               (FOVar 13))) by wk_in;
    assert (Le : FOPrH n Gc (FOle (FOSucc (FOVar 13)) (FOSucc (FOVar 10))))
      by (apply FOPrH_le_of_ltv; [free_ctx | lia | lia | avoid_tm | avoid_tm | wk_in]);
    assert (B1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (B2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (B3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G1 := Gc) in *
  end.
  clearbody G1. clear D1 D2 HP0 HB0 A0 A1 A2 A3.
  pose proof D1' as E1. unfold FOPRDERp in E1.
  apply FOPrH_and_r, FOPrH_and_l in E1.
  pose proof D2' as E2. unfold FOPRDERp in E2.
  apply FOPrH_and_r, FOPrH_and_l in E2.
  apply (FOPrH_final_elim n _ (FOVar 345) (FOVar 341) (FOVar 342) a 290 _ E1);
    [side | side | lia | side | side |].
  apply (FOPrH_final_elim n _ (FOVar 275) (FOVar 271) (FOVar 272) b 291);
    [wk E2 | side | side | lia | side | side |].
  apply (FOPrH_merge3_elim n _ (FOVar 330) (FOVar 331) (FOVar 340) (FOVar 260) (FOVar 261)
           (FOVar 270) (FOVar 2) (FOVar 3) (FOVar 12) 292 293 294 295); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 332) (FOVar 333) (FOVar 340) (FOVar 262) (FOVar 263)
           (FOVar 270) (FOVar 4) (FOVar 5) (FOVar 12) 296 297 298 299); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 334) (FOVar 335) (FOVar 340) (FOVar 264) (FOVar 265)
           (FOVar 270) (FOVar 6) (FOVar 7) (FOVar 12) 300 301 302 303); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 336) (FOVar 337) (FOVar 340) (FOVar 266) (FOVar 267)
           (FOVar 270) (FOVar 8) (FOVar 9) (FOVar 12) 304 305 306 307); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 338) (FOVar 339) (FOVar 340) (FOVar 268) (FOVar 269)
           (FOVar 270) (FOVar 10) (FOVar 11) (FOVar 12) 308 309 310 311); [side.. |].
  apply (FOPrH_ftrack_elim n _ (FOVar 341) (FOVar 342) (FOVar 345) (FOVar 271) (FOVar 272)
           (FOVar 275) c 312 313 314 315); [side.. |].
  apply (FOPrH_jtrack_elim n _ (FOVar 343) (FOVar 344) (FOVar 345) (FOVar 273) (FOVar 274)
           (FOVar 275) (FOVar 290) (FOVar 291) 316); [side.. |].
  cbn [Nat.add].
  apply (FOPrH_PRMAT_intro n _ cores c (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299)
           (FOVar 302) (FOVar 303) (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
           (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)) (FOVar 314) (FOVar 315)
           (FOVar 323) (FOVar 324) (FOPlus (FOPlus (FOVar 345) (FOVar 275)) (FOSucc FOZero)));
    [avoid_tms | avoid_tms |].
  apply (FOPrH_D2_body n _ cores (FOtabv 330) (FOtabv 260) (FOtabv 2)
           (mkTab (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299) (FOVar 302) (FOVar 303)
              (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
              (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)))
           (FOVar 341) (FOVar 342) (FOVar 343) (FOVar 344) (FOVar 345)
           (FOVar 271) (FOVar 272) (FOVar 273) (FOVar 274) (FOVar 275)
           (FOVar 314) (FOVar 315) (FOVar 323) (FOVar 324) (FOVar 290) (FOVar 291)
           a b c (FOVar 321) (FOVar 322) (FOVar 13) 316 325 326 327 328 329).
  all: lazymatch goal with
       | |- FOPrH _ _ _ => idtac
       | |- FOtms_avoid _ _ _ => tab_avoid
       | |- forall v, In v _ -> _ =>
           let v := fresh "v" in let Hv := fresh "Hv" in
           intros v Hv; simpl in Hv;
           destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; tab_avoid
       | |- _ = _ => reflexivity
       | |- _ => side
       end.
  - wk D1'.
  - wk D2'.
  - wk VB.
  - wk Le.
  - wk LK.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 341) (FOVar 342) (FOVar 290) a)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 345) (FOSucc (FOVar 290)))). wk_in.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 271) (FOVar 272) (FOVar 291) b)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 275) (FOSucc (FOVar 291)))). wk_in.
  - wk HP1.
  - unfold FOTABM3.
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; wk_in.
  - wk_in.
  - wk_in.
Qed.

(** ** Internal modus ponens as one theorem of the tower.

    For all codes [a], [b], [c]: when [a] codes the implication from
    [b] to [c] and the guard rows of [c] exist, the matrix at [a] and at
    [b] gives the matrix at [c].  The variable [0] stays free. *)

Definition FOD2F (cores : list nat) : FOFormula :=
  FOForall 600 (FOForall 601 (FOForall 602
    (FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600) .->
     FOGUARDB (FOVar 602) .->
     FOPRMATx cores (FOVar 600) .-> FOPRMATx cores (FOVar 601) .->
     FOPRMATx cores (FOVar 602)))).

Theorem FOPr_D2F : forall n cores, FOProvesTn n (FOD2F cores).
Proof.
  intros n cores.
  assert (H : FOPrH n [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600);
                       FOGUARDB (FOVar 602)]
                (FOPRMATx cores (FOVar 600) .-> FOPRMATx cores (FOVar 601) .->
                 FOPRMATx cores (FOVar 602))).
  { apply FOPrH_D2_gen.
    - intros w H1 H2. free_ctx.
    - apply FOPrH_assum. left. reflexivity.
    - apply FOPrH_assum. right. left. reflexivity.
    - avoid_tms. }
  change [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600); FOGUARDB (FOVar 602)]
    with ([] ++ [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600)] ++
          [FOGUARDB (FOVar 602)]) in H.
  rewrite app_assoc in H.
  apply FOPrH_intro, FOPrH_intro in H.
  unfold FOD2F.
  apply (FOPrH_all_intro n [] 602 _ (FOfree_ctx_nil 602)) in H.
  apply (FOPrH_all_intro n [] 601 _ (FOfree_ctx_nil 601)) in H.
  apply (FOPrH_all_intro n [] 600 _ (FOfree_ctx_nil 600)) in H.
  unfold FOPrH in H. cbn [FOimps] in H.
  exact H.
Qed.

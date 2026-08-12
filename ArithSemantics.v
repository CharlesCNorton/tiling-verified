(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 3 of 5. N-satisfaction, the arithmetized checker, HBL, FOembed.   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.ClassicalEpsilon.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax.

Lemma FOsat_FOJMP : forall e B cs ds vd pl ipos,
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  (FOsat e (FOJMP B cs ds vd pl ipos) <->
   exists i' j' bi bj,
     cpair i' j' = FOeval e pl /\
     i' < FOeval e ipos /\ j' < FOeval e ipos /\
     beta (FOeval e cs) (FOeval e ds) i' = bi /\
     beta (FOeval e cs) (FOeval e ds) j' = bj /\
     bi = cpair 2 (cpair bj (FOeval e vd))).
Proof.
  intros e B cs ds vd pl ipos Hcs Hds Hvd Hpl Hip.
  assert (HinB : FOin_tm B ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinSB : FOin_tm (S B) ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinB2 : FOin_tm (B+2) ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB6 : FOin_tm (B+6) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB6 : FOin_tm (S (B+6)) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+16)
                   [FOVar (B+6); vd])
    by (constructor; [cbn; lia |
        constructor; [lia | constructor]]).
  unfold FOJMP.
  rewrite (FOsat_FOBexC e B ipos _ HinB HinSB).
  split.
  - intros [i' [Hi' Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) ipos _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [j' [Hj' Hb2]].
    rewrite (FOeval_update_above ipos e B i' Hip) in Hj'.
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb2.
    destruct Hb2 as [Hcp Hb3].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cs) _ HinB4 HinSB4) in Hb3.
    destruct Hb3 as [bi [Hbi Hb4]].
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc cs) _ HinB6 HinSB6) in Hb4.
    destruct Hb4 as [bj [Hbj Hb5]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb5.
    destruct Hb5 as [Hbt1 Hb6].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb6.
    destruct Hb6 as [Hbt2 Hpat].
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B i')
                 (B+2) j') (B+4) bi) (B+6) bj) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4.
      rewrite (FOeval_update_above t _ (B+6) bj ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) bi ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) j' ltac:(lia)).
      exact (FOeval_update_above t e B i' Ht). }
    assert (EvB : e4 B = i').
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) bi B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) j' B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = j').
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) bi (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e4 (B+4) = bi).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e4 (B+6) = bj).
    { unfold e4. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    cbn [FOeval] in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOupdate_neq _ (B+2) j' B ltac:(lia)) in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOeval_update_above pl _ (B+2) j' ltac:(lia)) in Hcp.
    rewrite (FOeval_update_above pl e B i' Hpl) in Hcp.
    apply (proj1 (FOsat_FObetaF e4 (B+8) cs ds (FOVar B)
                    (FOVar (B+4)) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))) in Hbt1.
    cbn [FOeval] in Hbt1.
    rewrite (Hstab cs Hcs), (Hstab ds Hds), EvB, EvB4 in Hbt1.
    apply (proj1 (FOsat_FObetaF e4 (B+12) cs ds (FOVar (B+2))
                    (FOVar (B+6)) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))) in Hbt2.
    cbn [FOeval] in Hbt2.
    rewrite (Hstab cs Hcs), (Hstab ds Hds), EvB2, EvB6 in Hbt2.
    apply (proj1 (FOsat_FOPATF cpatImpl01 _ (B+16) _ (FOVar (B+4))
                    Henv ltac:(cbn; lia))) in Hpat.
    assert (Hsg : forall s,
        FOeval e4 (nth s [FOVar (B+6); vd] FOZero)
        = (fun s => match s with
                    | 0 => bj | 1 => FOeval e vd | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB6.
      - exact (Hstab vd Hvd).
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    cbn [FOeval] in Hpat.
    rewrite EvB4 in Hpat.
    cbn [cpat_sem cpatImpl01 pImpP] in Hpat.
    exists i', j', bi, bj.
    split; [exact Hcp|].
    split; [exact Hi'|].
    split; [exact Hj'|].
    split; [exact Hbt1|].
    split; [exact Hbt2|].
    symmetry. exact Hpat.
  - intros [i' [j' [bi [bj [Hcp [Hi' [Hj' [Hbt1 [Hbt2 Hsh]]]]]]]]].
    exists i'. split; [exact Hi'|].
    rewrite (FOsat_FOBexC _ (B+2) ipos _ HinB2 HinSB2).
    exists j'. split.
    { rewrite (FOeval_update_above ipos e B i' Hip). exact Hj'. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      cbn [FOeval].
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOupdate_neq _ (B+2) j' B ltac:(lia)).
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above pl _ (B+2) j' ltac:(lia)).
      rewrite (FOeval_update_above pl e B i' Hpl).
      exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cs) _ HinB4 HinSB4).
    exists bi. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cs _ (B+2) j' ltac:(lia)).
      rewrite (FOeval_update_above cs e B i' Hcs).
      unfold beta in Hbt1.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
                    (FOeval e ds * S i' + 1)).
      lia. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc cs) _ HinB6 HinSB6).
    exists bj. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cs _ (B+4) bi ltac:(lia)).
      rewrite (FOeval_update_above cs _ (B+2) j' ltac:(lia)).
      rewrite (FOeval_update_above cs e B i' Hcs).
      unfold beta in Hbt2.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
                    (FOeval e ds * S j' + 1)).
      lia. }
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B i')
                 (B+2) j') (B+4) bi) (B+6) bj).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4.
      rewrite (FOeval_update_above t _ (B+6) bj ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) bi ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) j' ltac:(lia)).
      exact (FOeval_update_above t e B i' Ht). }
    assert (EvB : e4 B = i').
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) bi B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) j' B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = j').
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) bi (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e4 (B+4) = bi).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) bj (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e4 (B+6) = bj).
    { unfold e4. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF e4 (B+8) cs ds (FOVar B)
                      (FOVar (B+4)) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite (Hstab cs Hcs), (Hstab ds Hds), EvB, EvB4.
      exact Hbt1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF e4 (B+12) cs ds (FOVar (B+2))
                      (FOVar (B+6)) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite (Hstab cs Hcs), (Hstab ds Hds), EvB2, EvB6.
      exact Hbt2. }
    apply (proj2 (FOsat_FOPATF cpatImpl01 e4 (B+16) _ (FOVar (B+4))
                    Henv ltac:(cbn; lia))).
    assert (Hsg : forall s,
        FOeval e4 (nth s [FOVar (B+6); vd] FOZero)
        = (fun s => match s with
                    | 0 => bj | 1 => FOeval e vd | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB6.
      - exact (Hstab vd Hvd).
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    cbn [FOeval].
    rewrite EvB4.
    cbn [cpat_sem cpatImpl01 pImpP].
    symmetry. exact Hsh.
Qed.

Lemma FOsat_FOJGEN : forall e B cs ds vd pl ipos,
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  (FOsat e (FOJGEN B cs ds vd pl ipos) <->
   FOeval e pl < FOeval e ipos /\
   exists bj x,
     beta (FOeval e cs) (FOeval e ds) (FOeval e pl) = bj /\
     FOeval e vd = cpair 3 (cpair x bj)).
Proof.
  intros e B cs ds vd pl ipos Hcs Hds Hvd Hpl Hip.
  assert (HinB : FOin_tm B ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinSB : FOin_tm (S B) ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB8 : FOin_tm (B+8) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB8 : FOin_tm (S (B+8)) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+10)
                   [FOVar (B+8); FOVar (B+2)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]).
  assert (Hvd10 : FOmax_var_tm vd < B+10) by lia.
  unfold FOJGEN.
  rewrite (FOsat_FOBexC e B ipos _ HinB HinSB).
  split.
  - intros [w [Hw Hb1]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb1.
    destruct Hb1 as [Heq Hb2].
    cbn [FOsat FOeval] in Heq.
    rewrite (FOupdate_eq _ _ _) in Heq.
    rewrite (FOeval_update_above pl e B w Hpl) in Heq.
    subst w.
    split; [exact Hw|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cs) _ HinB2 HinSB2) in Hb2.
    destruct Hb2 as [bj [Hbj Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hbt Hb4].
    apply (proj1 (FOsat_FObetaF _ (B+4) cs ds (FOVar B)
                    (FOVar (B+2)) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))) in Hbt.
    cbn [FOeval] in Hbt.
    rewrite (FOupdate_eq _ _ _) in Hbt.
    rewrite (FOupdate_neq _ (B+2) bj B ltac:(lia)) in Hbt.
    rewrite (FOupdate_eq _ _ _) in Hbt.
    rewrite (FOeval_update_above cs _ (B+2) bj ltac:(lia)) in Hbt.
    rewrite (FOeval_update_above cs e B (FOeval e pl) Hcs) in Hbt.
    rewrite (FOeval_update_above ds _ (B+2) bj ltac:(lia)) in Hbt.
    rewrite (FOeval_update_above ds e B (FOeval e pl) Hds) in Hbt.
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc vd) _ HinB8 HinSB8) in Hb4.
    destruct Hb4 as [x [Hx Hpat]].
    set (e3 := FOupdate (FOupdate (FOupdate e B (FOeval e pl))
                 (B+2) bj) (B+8) x) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+8) x ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
      exact (FOeval_update_above t e B (FOeval e pl) Ht). }
    assert (EvB2 : e3 (B+2) = bj).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+8) x (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e3 (B+8) = x).
    { unfold e3. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOPATF cpatAll01 _ (B+10) _ vd Henv Hvd10))
      in Hpat.
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+8); FOVar (B+2)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => bj | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB8.
      - exact EvB2.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab vd Hvd) in Hpat.
    cbn [cpat_sem cpatAll01 pAllP] in Hpat.
    exists bj, x.
    split; [exact Hbt|].
    symmetry. exact Hpat.
  - intros [Hlt [bj [x [Hbt Hsh]]]].
    exists (FOeval e pl). split; [exact Hlt|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { cbn [FOsat FOeval].
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above pl e B (FOeval e pl) Hpl).
      reflexivity. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cs) _ HinB2 HinSB2).
    exists bj. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cs e B (FOeval e pl) Hcs).
      unfold beta in Hbt.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
                    (FOeval e ds * S (FOeval e pl) + 1)).
      lia. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { set (e2 := FOupdate (FOupdate e B (FOeval e pl)) (B+2) bj).
      apply (proj2 (FOsat_FObetaF e2 (B+4) cs ds (FOVar B)
                      (FOVar (B+2)) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia))).
      cbn [FOeval].
      assert (EvB : e2 B = FOeval e pl).
      { unfold e2.
        rewrite (FOupdate_neq _ (B+2) bj B ltac:(lia)).
        apply FOupdate_eq. }
      assert (EvB2 : e2 (B+2) = bj).
      { unfold e2. apply FOupdate_eq. }
      assert (Hstab : forall t, FOmax_var_tm t < B ->
          FOeval e2 t = FOeval e t).
      { intros t Ht. unfold e2.
        rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
        exact (FOeval_update_above t e B (FOeval e pl) Ht). }
      rewrite (Hstab cs Hcs), (Hstab ds Hds), EvB, EvB2.
      exact Hbt. }
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc vd) _ HinB8 HinSB8).
    pose proof (cpair_bound x bj) as Hb1.
    pose proof (cpair_bound 3 (cpair x bj)) as Hb2.
    exists x. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above vd _ (B+2) bj ltac:(lia)).
      rewrite (FOeval_update_above vd e B (FOeval e pl) Hvd).
      lia. }
    set (e3 := FOupdate (FOupdate (FOupdate e B (FOeval e pl))
                 (B+2) bj) (B+8) x).
    apply (proj2 (FOsat_FOPATF cpatAll01 e3 (B+10) _ vd Henv Hvd10)).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+8) x ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
      exact (FOeval_update_above t e B (FOeval e pl) Ht). }
    assert (EvB2 : e3 (B+2) = bj).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+8) x (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e3 (B+8) = x).
    { unfold e3. apply FOupdate_eq. }
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+8); FOVar (B+2)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => bj | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB8.
      - exact EvB2.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    rewrite (Hstab vd Hvd).
    cbn [cpat_sem cpatAll01 pAllP].
    symmetry. exact Hsh.
Qed.

Lemma FOsat_FOJLOEB : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds vd pl ipos,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  (FOsat e (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds
              vd pl ipos) <->
   FOeval e pl < FOeval e ipos /\
   exists bj nu core na p,
     beta (FOeval e cs) (FOeval e ds) (FOeval e pl) = bj /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 5 /\
        beta (FOeval e c1) (FOeval e d1) j = e 0 /\
        beta (FOeval e c2) (FOeval e d2) j = 0 /\
        beta (FOeval e c3) (FOeval e d3) j = 0 /\
        beta (FOeval e cr) (FOeval e dr) j = nu) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 3 /\
        beta (FOeval e c1) (FOeval e d1) j = 0 /\
        beta (FOeval e c2) (FOeval e d2) j = nu /\
        beta (FOeval e c3) (FOeval e d3) j = e 0 /\
        beta (FOeval e cr) (FOeval e dr) j = core) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 5 /\
        beta (FOeval e c1) (FOeval e d1) j = FOeval e vd /\
        beta (FOeval e c2) (FOeval e d2) j = 0 /\
        beta (FOeval e c3) (FOeval e d3) j = 0 /\
        beta (FOeval e cr) (FOeval e dr) j = na) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 3 /\
        beta (FOeval e c1) (FOeval e d1) j = 1 /\
        beta (FOeval e c2) (FOeval e d2) j = na /\
        beta (FOeval e c3) (FOeval e d3) j = core /\
        beta (FOeval e cr) (FOeval e dr) j = p) /\
     bj = cpair 2 (cpair p (FOeval e vd))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos
    Htb Hcs Hds Hvd Hpl Hip.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb16 : tbl_below (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb38 : tbl_below (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb82 : tbl_below (B+82) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinSB : FOin_tm (S B) ipos = false)
    by (apply FOin_tm_above; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB8 : FOin_tm (B+8) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB8 : FOin_tm (S (B+8)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB10 : FOin_tm (B+10) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB10 : FOin_tm (S (B+10)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB12 : FOin_tm (B+12) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB12 : FOin_tm (S (B+12)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB14 : FOin_tm (B+14) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB14 : FOin_tm (S (B+14)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (H5m16 : FOmax_var_tm (FOnumeral 5) < B+16)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hv016 : FOmax_var_tm (FOVar 0) < B+16) by (cbn; lia).
  assert (H0m16 : FOmax_var_tm FOZero < B+16) by (cbn; lia).
  assert (HvB816 : FOmax_var_tm (FOVar (B+8)) < B+16) by (cbn; lia).
  assert (H3m38 : FOmax_var_tm (FOnumeral 3) < B+38)
    by (rewrite FOmax_var_numeral; lia).
  assert (H0m38 : FOmax_var_tm FOZero < B+38) by (cbn; lia).
  assert (HvB838 : FOmax_var_tm (FOVar (B+8)) < B+38) by (cbn; lia).
  assert (Hv038 : FOmax_var_tm (FOVar 0) < B+38) by (cbn; lia).
  assert (HvB1038 : FOmax_var_tm (FOVar (B+10)) < B+38)
    by (cbn; lia).
  assert (H5m60 : FOmax_var_tm (FOnumeral 5) < B+60)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hvd60 : FOmax_var_tm vd < B+60) by lia.
  assert (H0m60 : FOmax_var_tm FOZero < B+60) by (cbn; lia).
  assert (HvB1260 : FOmax_var_tm (FOVar (B+12)) < B+60)
    by (cbn; lia).
  assert (H3m82 : FOmax_var_tm (FOnumeral 3) < B+82)
    by (rewrite FOmax_var_numeral; lia).
  assert (H1m82 : FOmax_var_tm (FOnumeral 1) < B+82)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvB1282 : FOmax_var_tm (FOVar (B+12)) < B+82)
    by (cbn; lia).
  assert (HvB1082 : FOmax_var_tm (FOVar (B+10)) < B+82)
    by (cbn; lia).
  assert (HvB1482 : FOmax_var_tm (FOVar (B+14)) < B+82)
    by (cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+104)
                   [FOVar (B+14); vd])
    by (constructor; [cbn; lia |
        constructor; [lia | constructor]]).
  unfold FOJLOEB.
  rewrite (FOsat_FOBexC e B ipos _ HinB HinSB).
  split.
  - intros [w [Hw Hb1]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb1.
    destruct Hb1 as [Heq Hb2].
    cbn [FOsat FOeval] in Heq.
    rewrite (FOupdate_eq _ _ _) in Heq.
    rewrite (FOeval_update_above pl e B w Hpl) in Heq.
    subst w.
    split; [exact Hw|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cs) _ HinB2 HinSB2) in Hb2.
    destruct Hb2 as [bj [Hbj Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hbt Hb4].
    apply (proj1 (FOsat_FObetaF _ (B+4) cs ds (FOVar B)
                    (FOVar (B+2)) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))) in Hbt.
    cbn [FOeval] in Hbt.
    rewrite (FOupdate_eq _ _ _) in Hbt.
    rewrite (FOupdate_neq _ (B+2) bj B ltac:(lia)) in Hbt.
    rewrite (FOupdate_eq _ _ _) in Hbt.
    rewrite (FOeval_update_above cs _ (B+2) bj ltac:(lia)) in Hbt.
    rewrite (FOeval_update_above cs e B (FOeval e pl) Hcs) in Hbt.
    rewrite (FOeval_update_above ds _ (B+2) bj ltac:(lia)) in Hbt.
    rewrite (FOeval_update_above ds e B (FOeval e pl) Hds) in Hbt.
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc cr) _ HinB8 HinSB8) in Hb4.
    destruct Hb4 as [nu [Hnu Hb5]].
    rewrite (FOsat_FOBexC _ (B+10) (FOSucc cr) _ HinB10 HinSB10)
      in Hb5.
    destruct Hb5 as [core [Hcore Hb6]].
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc cr) _ HinB12 HinSB12)
      in Hb6.
    destruct Hb6 as [na [Hna Hb7]].
    rewrite (FOsat_FOBexC _ (B+14) (FOSucc cr) _ HinB14 HinSB14)
      in Hb7.
    destruct Hb7 as [p [Hp Hb8]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb8.
    destruct Hb8 as [Hlk1 Hb9].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb9.
    destruct Hb9 as [Hlk2 Hb10].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb10.
    destruct Hb10 as [Hlk3 Hb11].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb11.
    destruct Hb11 as [Hlk4 Hpat].
    set (e6 := FOupdate (FOupdate (FOupdate (FOupdate (FOupdate
                 (FOupdate e B (FOeval e pl)) (B+2) bj) (B+8) nu)
                 (B+10) core) (B+12) na) (B+14) p) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e6 t = FOeval e t).
    { intros t Ht. unfold e6.
      rewrite (FOeval_update_above t _ (B+14) p ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+12) na ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+10) core ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) nu ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
      exact (FOeval_update_above t e B (FOeval e pl) Ht). }
    assert (Ev0 : e6 0 = e 0).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) nu 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) bj 0 ltac:(lia)).
      apply (FOupdate_neq _ B (FOeval e pl) 0 ltac:(lia)). }
    assert (EvB2 : e6 (B+2) = bj).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) nu (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e6 (B+8) = nu).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+8) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+8) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core (B+8) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB10 : e6 (B+10) = core).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+10) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+10) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB12 : e6 (B+12) = na).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+12) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB14 : e6 (B+14) = p).
    { unfold e6. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOlookup e6 (B+16) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 5) (FOVar 0) FOZero FOZero
                    (FOVar (B+8))
                    Htb16 H5m16 Hv016 H0m16 H0m16 HvB816)) in Hlk1.
    destruct Hlk1 as [j1 [Hj1 [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
    rewrite (Hstab len Hlen) in Hj1.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Ha1.
    cbn [FOeval] in Ha2, Ha3, Ha4, Ha5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ev0 in Ha2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Ha3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Ha4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB8 in Ha5.
    apply (proj1 (FOsat_FOlookup e6 (B+38) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) FOZero (FOVar (B+8))
                    (FOVar 0) (FOVar (B+10))
                    Htb38 H3m38 H0m38 HvB838 Hv038 HvB1038)) in Hlk2.
    destruct Hlk2 as [j2 [Hj2 [Hb1' [Hb2' [Hb3' [Hb4' Hb5']]]]]].
    rewrite (Hstab len Hlen) in Hj2.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hb1'.
    cbn [FOeval] in Hb2', Hb3', Hb4', Hb5'.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in Hb2'.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB8 in Hb3'.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), Ev0 in Hb4'.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB10 in Hb5'.
    apply (proj1 (FOsat_FOlookup e6 (B+60) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 5) vd FOZero FOZero
                    (FOVar (B+12))
                    Htb60 H5m60 Hvd60 H0m60 H0m60 HvB1260)) in Hlk3.
    destruct Hlk3 as [j3 [Hj3 [Hc1' [Hc2' [Hc3' [Hc4' Hc5']]]]]].
    rewrite (Hstab len Hlen) in Hj3.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hc1'.
    cbn [FOeval] in Hc3', Hc4', Hc5'.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab vd Hvd) in Hc2'.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hc3'.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Hc4'.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB12 in Hc5'.
    apply (proj1 (FOsat_FOlookup e6 (B+82) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOnumeral 1)
                    (FOVar (B+12)) (FOVar (B+10)) (FOVar (B+14))
                    Htb82 H3m82 H1m82 HvB1282 HvB1082 HvB1482))
      in Hlk4.
    destruct Hlk4 as [j4 [Hj4 [Hd1'' [Hd2'' [Hd3'' [Hd4'' Hd5'']]]]]].
    rewrite (Hstab len Hlen) in Hj4.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hd1''.
    cbn [FOeval] in Hd3'', Hd4'', Hd5''.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral in Hd2''.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB12 in Hd3''.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB10 in Hd4''.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB14 in Hd5''.
    apply (proj1 (FOsat_FOPATF cpatImpl01 _ (B+104) _ (FOVar (B+2))
                    Henv ltac:(cbn; lia))) in Hpat.
    assert (Hsg : forall s,
        FOeval e6 (nth s [FOVar (B+14); vd] FOZero)
        = (fun s => match s with
                    | 0 => p | 1 => FOeval e vd | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB14.
      - exact (Hstab vd Hvd).
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    cbn [FOeval] in Hpat.
    rewrite EvB2 in Hpat.
    cbn [cpat_sem cpatImpl01 pImpP] in Hpat.
    exists bj, nu, core, na, p.
    split; [exact Hbt|].
    split.
    { exists j1. repeat split; assumption. }
    split.
    { exists j2. repeat split; assumption. }
    split.
    { exists j3. repeat split; assumption. }
    split.
    { exists j4. repeat split; assumption. }
    symmetry. exact Hpat.
  - intros [Hlt [bj [nu [core [na [p
      [Hbt [Hr1 [Hr2 [Hr3 [Hr4 Hsh]]]]]]]]]]].
    assert (Hnub : nu <= FOeval e cr).
    { destruct Hr1 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    assert (Hcoreb : core <= FOeval e cr).
    { destruct Hr2 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    assert (Hnab : na <= FOeval e cr).
    { destruct Hr3 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    assert (Hpb : p <= FOeval e cr).
    { destruct Hr4 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    assert (Hbjb : bj <= FOeval e cs).
    { unfold beta in Hbt.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
                    (FOeval e ds * S (FOeval e pl) + 1)).
      lia. }
    exists (FOeval e pl). split; [exact Hlt|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { cbn [FOsat FOeval].
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above pl e B (FOeval e pl) Hpl).
      reflexivity. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cs) _ HinB2 HinSB2).
    exists bj. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cs e B (FOeval e pl) Hcs).
      lia. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { set (e2 := FOupdate (FOupdate e B (FOeval e pl)) (B+2) bj).
      apply (proj2 (FOsat_FObetaF e2 (B+4) cs ds (FOVar B)
                      (FOVar (B+2)) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia))).
      cbn [FOeval].
      assert (EvB : e2 B = FOeval e pl).
      { unfold e2.
        rewrite (FOupdate_neq _ (B+2) bj B ltac:(lia)).
        apply FOupdate_eq. }
      assert (EvB2 : e2 (B+2) = bj).
      { unfold e2. apply FOupdate_eq. }
      assert (Hstab2 : forall t, FOmax_var_tm t < B ->
          FOeval e2 t = FOeval e t).
      { intros t Ht. unfold e2.
        rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
        exact (FOeval_update_above t e B (FOeval e pl) Ht). }
      rewrite (Hstab2 cs Hcs), (Hstab2 ds Hds), EvB, EvB2.
      exact Hbt. }
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc cr) _ HinB8 HinSB8).
    exists nu. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+2) bj ltac:(lia)).
      rewrite (FOeval_update_above cr e B (FOeval e pl) Hcr).
      lia. }
    rewrite (FOsat_FOBexC _ (B+10) (FOSucc cr) _ HinB10 HinSB10).
    exists core. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+8) nu ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) bj ltac:(lia)).
      rewrite (FOeval_update_above cr e B (FOeval e pl) Hcr).
      lia. }
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc cr) _ HinB12 HinSB12).
    exists na. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+10) core ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+8) nu ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) bj ltac:(lia)).
      rewrite (FOeval_update_above cr e B (FOeval e pl) Hcr).
      lia. }
    rewrite (FOsat_FOBexC _ (B+14) (FOSucc cr) _ HinB14 HinSB14).
    exists p. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+12) na ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+10) core ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+8) nu ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) bj ltac:(lia)).
      rewrite (FOeval_update_above cr e B (FOeval e pl) Hcr).
      lia. }
    set (e6 := FOupdate (FOupdate (FOupdate (FOupdate (FOupdate
                 (FOupdate e B (FOeval e pl)) (B+2) bj) (B+8) nu)
                 (B+10) core) (B+12) na) (B+14) p).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e6 t = FOeval e t).
    { intros t Ht. unfold e6.
      rewrite (FOeval_update_above t _ (B+14) p ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+12) na ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+10) core ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) nu ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) bj ltac:(lia)).
      exact (FOeval_update_above t e B (FOeval e pl) Ht). }
    assert (Ev0 : e6 0 = e 0).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) nu 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) bj 0 ltac:(lia)).
      apply (FOupdate_neq _ B (FOeval e pl) 0 ltac:(lia)). }
    assert (EvB2 : e6 (B+2) = bj).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) nu (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e6 (B+8) = nu).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+8) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+8) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+10) core (B+8) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB10 : e6 (B+10) = core).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+10) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) na (B+10) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB12 : e6 (B+12) = na).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+14) p (B+12) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB14 : e6 (B+14) = p).
    { unfold e6. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 5) (FOVar 0) FOZero FOZero
                      (FOVar (B+8))
                      Htb16 H5m16 Hv016 H0m16 H0m16 HvB816)).
      destruct Hr1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ev0. exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'). exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB8. exact Hf5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+38) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) FOZero (FOVar (B+8))
                      (FOVar 0) (FOVar (B+10))
                      Htb38 H3m38 H0m38 HvB838 Hv038 HvB1038)).
      destruct Hr2 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'). exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB8. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), Ev0. exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB10. exact Hf5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+60) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 5) vd FOZero FOZero
                      (FOVar (B+12))
                      Htb60 H5m60 Hvd60 H0m60 H0m60 HvB1260)).
      destruct Hr3 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab vd Hvd).
        exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'). exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB12. exact Hf5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+82) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) (FOnumeral 1)
                      (FOVar (B+12)) (FOVar (B+10)) (FOVar (B+14))
                      Htb82 H3m82 H1m82 HvB1282 HvB1082 HvB1482)).
      destruct Hr4 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral.
        exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB12. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB10. exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB14. exact Hf5. }
    apply (proj2 (FOsat_FOPATF cpatImpl01 e6 (B+104) _ (FOVar (B+2))
                    Henv ltac:(cbn; lia))).
    assert (Hsg : forall s,
        FOeval e6 (nth s [FOVar (B+14); vd] FOZero)
        = (fun s => match s with
                    | 0 => p | 1 => FOeval e vd | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn [nth FOeval].
      - exact EvB14.
      - exact (Hstab vd Hvd).
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    cbn [FOeval].
    rewrite EvB2.
    cbn [cpat_sem cpatImpl01 pImpP].
    symmetry. exact Hsh.
Qed.

Lemma FOsat_FOJUSTCK : forall e B cores ct dt c1 d1 c2 d2 c3 d3 cr dr
    len cs ds cj dj i,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm cj < B -> FOmax_var_tm dj < B ->
  FOmax_var_tm i < B ->
  (FOsat e (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
              cs ds cj dj i) <->
   justck_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (e 0) (FOeval e cs) (FOeval e ds) (FOeval e cj)
     (FOeval e dj) (FOeval e i)).
Proof.
  intros e B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i
    Htb Hcs Hds Hcj Hdj Hi.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb16 : tbl_below (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cj) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cj) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Hin12 : FOin_tm (B+12) (FOSucc (FOVar (B+2))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinS12 : FOin_tm (S (B+12)) (FOSucc (FOVar (B+2))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Hin14 : FOin_tm (B+14) (FOSucc (FOVar (B+2))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinS14 : FOin_tm (S (B+14)) (FOSucc (FOVar (B+2))) = false)
    by (apply FOin_tm_above; cbn; lia).
  unfold FOJUSTCK, justck_sem.
  rewrite (FOsat_FOBexC e B (FOSucc cs) _ HinB HinSB).
  split.
  - intros [vd [Hvdb Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cj) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [vj [Hvjb Hb2]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb2.
    destruct Hb2 as [Hbeta1 Hb3].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hbeta2 Hb4].
    apply (proj1 (FOsat_FObetaF _ (B+4) cs ds i (FOVar B)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia))) in Hbeta1.
    cbn [FOeval] in Hbeta1.
    rewrite (FOupdate_neq _ (B+2) vj B ltac:(lia)) in Hbeta1.
    rewrite (FOupdate_eq _ _ _) in Hbeta1.
    rewrite (FOeval_update_above cs _ (B+2) vj ltac:(lia)) in Hbeta1.
    rewrite (FOeval_update_above cs e B vd Hcs) in Hbeta1.
    rewrite (FOeval_update_above ds _ (B+2) vj ltac:(lia)) in Hbeta1.
    rewrite (FOeval_update_above ds e B vd Hds) in Hbeta1.
    rewrite (FOeval_update_above i _ (B+2) vj ltac:(lia)) in Hbeta1.
    rewrite (FOeval_update_above i e B vd Hi) in Hbeta1.
    apply (proj1 (FOsat_FObetaF _ (B+8) cj dj i (FOVar (B+2))
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia))) in Hbeta2.
    cbn [FOeval] in Hbeta2.
    rewrite (FOupdate_eq _ _ _) in Hbeta2.
    rewrite (FOeval_update_above cj _ (B+2) vj ltac:(lia)) in Hbeta2.
    rewrite (FOeval_update_above cj e B vd Hcj) in Hbeta2.
    rewrite (FOeval_update_above dj _ (B+2) vj ltac:(lia)) in Hbeta2.
    rewrite (FOeval_update_above dj e B vd Hdj) in Hbeta2.
    rewrite (FOeval_update_above i _ (B+2) vj ltac:(lia)) in Hbeta2.
    rewrite (FOeval_update_above i e B vd Hi) in Hbeta2.
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc (FOVar (B+2))) _
               Hin12 HinS12) in Hb4.
    destruct Hb4 as [tg [Htgb Hb5]].
    rewrite (FOsat_FOBexC _ (B+14) (FOSucc (FOVar (B+2))) _
               Hin14 HinS14) in Hb5.
    destruct Hb5 as [pl [Hplb Hb6]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb6.
    destruct Hb6 as [Hcp Hor].
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B vd)
                 (B+2) vj) (B+12) tg) (B+14) pl) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4.
      rewrite (FOeval_update_above t _ (B+14) pl ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+12) tg ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) vj ltac:(lia)).
      exact (FOeval_update_above t e B vd Ht). }
    assert (Ev0 : e4 0 = e 0).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) vj 0 ltac:(lia)).
      apply (FOupdate_neq _ B vd 0 ltac:(lia)). }
    assert (EvB : e4 B = vd).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) vj B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = vj).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB12 : e4 (B+12) = tg).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl (B+12) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB14 : e4 (B+14) = pl).
    { unfold e4. apply FOupdate_eq. }
    assert (HL4 : forall a b c0 d0 r,
        (exists j, j < FOeval e4 len /\
           beta (FOeval e4 ct) (FOeval e4 dt) j = a /\
           beta (FOeval e4 c1) (FOeval e4 d1) j = b /\
           beta (FOeval e4 c2) (FOeval e4 d2) j = c0 /\
           beta (FOeval e4 c3) (FOeval e4 d3) j = d0 /\
           beta (FOeval e4 cr) (FOeval e4 dr) j = r) <->
        (exists j, j < FOeval e len /\
           beta (FOeval e ct) (FOeval e dt) j = a /\
           beta (FOeval e c1) (FOeval e d1) j = b /\
           beta (FOeval e c2) (FOeval e d2) j = c0 /\
           beta (FOeval e c3) (FOeval e d3) j = d0 /\
           beta (FOeval e cr) (FOeval e dr) j = r)).
    { intros a b c0 d0 r. split;
        intros [j [Hj [F1 [F2 [F3 [F4 F5]]]]]]; exists j.
      - rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption.
      - split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split; [rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'); exact F2|].
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split; [rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'); exact F4|].
        rewrite (Hstab cr Hcr), (Hstab dr Hdr); exact F5. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    cbn [FOeval] in Hcp.
    rewrite EvB12, EvB14, EvB2 in Hcp.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    rewrite (FOsat_FOOr _ _ _) in Hor.
    exists vd, vj, tg, pl.
    split; [exact Hbeta1|].
    split; [exact Hbeta2|].
    split; [exact Hcp|].
    destruct Hor as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
    + left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq Hth].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOTHAXc e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cores (FOVar B) Htb16
                      ltac:(cbn; lia))) in Hth.
      cbn [FOeval] in Hth.
      rewrite EvB in Hth.
      apply (proj1 (thax_sem_ext _ _ cores vd HL4)).
      exact Hth.
    + right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq Hlg].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOLOGc e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))) in Hlg.
      cbn [FOeval] in Hlg.
      rewrite EvB in Hlg.
      apply (proj1 (logax_sem_ext _ _ vd HL4)).
      exact Hlg.
    + do 2 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJSUBST e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cpatAllElim (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia)
                      eq_refl eq_refl)) in HJ.
      destruct HJ as [x [tc [P [Q [Hxtc [Hsem [Hr1 Hr2]]]]]]].
      cbn [FOeval] in Hxtc, Hsem.
      rewrite EvB14 in Hxtc.
      rewrite EvB in Hsem.
      cbn [cpat_sem cpatAllElim pImpP pAllP] in Hsem.
      exists x, tc, P, Q.
      split; [exact Hxtc|].
      split; [symmetry; exact Hsem|].
      split; [apply (proj1 (HL4 4 x tc P 1)); exact Hr1|].
      apply (proj1 (HL4 3 x tc P Q)). exact Hr2.
    + do 3 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJSUBST e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cpatExIntro (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia)
                      eq_refl eq_refl)) in HJ.
      destruct HJ as [x [tc [P [Q [Hxtc [Hsem [Hr1 Hr2]]]]]]].
      cbn [FOeval] in Hxtc, Hsem.
      rewrite EvB14 in Hxtc.
      rewrite EvB in Hsem.
      cbn [cpat_sem cpatExIntro pImpP pExP] in Hsem.
      exists x, tc, P, Q.
      split; [exact Hxtc|].
      split; [symmetry; exact Hsem|].
      split; [apply (proj1 (HL4 4 x tc P 1)); exact Hr1|].
      apply (proj1 (HL4 3 x tc P Q)). exact Hr2.
    + do 4 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJMP e4 (B+16) cs ds (FOVar B)
                      (FOVar (B+14)) i ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(lia))) in HJ.
      destruct HJ as [i' [j' [bi [bj
        [Hpl' [Hi' [Hj' [Hb1' [Hb2' Hsh]]]]]]]]].
      cbn [FOeval] in Hpl', Hsh.
      rewrite EvB14 in Hpl'.
      rewrite EvB in Hsh.
      rewrite (Hstab i Hi) in Hi', Hj'.
      rewrite (Hstab cs Hcs), (Hstab ds Hds) in Hb1', Hb2'.
      exists i', j', bi, bj.
      split; [exact Hpl'|].
      split; [exact Hi'|].
      split; [exact Hj'|].
      split; [exact Hb1'|].
      split; [exact Hb2'|].
      exact Hsh.
    + do 5 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJGEN e4 (B+16) cs ds (FOVar B)
                      (FOVar (B+14)) i ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(lia))) in HJ.
      destruct HJ as [Hlt [bj [x [Hbt Hsh]]]].
      cbn [FOeval] in Hlt, Hbt, Hsh.
      rewrite EvB14 in Hlt, Hbt.
      rewrite (Hstab i Hi) in Hlt.
      rewrite (Hstab cs Hcs), (Hstab ds Hds) in Hbt.
      rewrite EvB in Hsh.
      split; [exact Hlt|].
      exists bj, x.
      split; [exact Hbt|].
      exact Hsh.
    + do 6 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJLOEB e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cs ds (FOVar B) (FOVar (B+14)) i
                      Htb16 ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(lia))) in HJ.
      destruct HJ as [Hlt [bj [nu [core [na [p
        [Hbt [Hr1 [Hr2 [Hr3 [Hr4 Hsh]]]]]]]]]]].
      cbn [FOeval] in Hlt, Hbt, Hsh.
      rewrite EvB14 in Hlt, Hbt.
      rewrite (Hstab i Hi) in Hlt.
      rewrite (Hstab cs Hcs), (Hstab ds Hds) in Hbt.
      rewrite EvB in Hsh.
      split; [exact Hlt|].
      exists bj, nu, core, na, p.
      split; [exact Hbt|].
      split.
      { destruct Hr1 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ev0 in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption. }
      split.
      { destruct Hr2 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), Ev0 in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption. }
      split.
      { destruct Hr3 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        cbn [FOeval] in F2.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption. }
      split.
      { destruct Hr4 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption. }
      exact Hsh.
    + do 7 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq Hd].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOD2Sc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))) in Hd.
      cbn [FOeval] in Hd.
      rewrite EvB in Hd.
      apply (proj1 (d2s_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 8 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq Hd].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOD3Sc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))) in Hd.
      cbn [FOeval] in Hd.
      rewrite EvB in Hd.
      apply (proj1 (d3s_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 9 right; left.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq Hd].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FODMONSc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))) in Hd.
      cbn [FOeval] in Hd.
      rewrite EvB in Hd.
      apply (proj1 (dmons_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 10 right.
      apply (proj1 (FOsat_FOAnd _ _ _)) in H.
      destruct H as [Heq HJ].
      cbn [FOsat FOeval] in Heq.
      rewrite EvB12 in Heq.
      split; [exact Heq|].
      apply (proj1 (FOsat_FOJIND e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia))) in HJ.
      destruct HJ as [x [PA [C0 [SS [Hxpa [Hsem [Hr1 [Hr2 [Hr3 Hr4]]]]]]]]].
      cbn [FOeval] in Hxpa, Hsem.
      rewrite EvB14 in Hxpa.
      rewrite EvB in Hsem.
      cbn [cpat_sem cpatInd pImpP pAllP] in Hsem.
      exists x, PA, C0, SS.
      split; [symmetry; exact Hxpa|].
      split; [symmetry; exact Hsem|].
      split; [apply (proj1 (HL4 4 x (cpair 1 0) PA 1)); exact Hr1|].
      split; [apply (proj1 (HL4 3 x (cpair 1 0) PA C0)); exact Hr2|].
      split; [apply (proj1 (HL4 4 x (cpair 2 (cpair 0 x)) PA 1)); exact Hr3|].
      apply (proj1 (HL4 3 x (cpair 2 (cpair 0 x)) PA SS)). exact Hr4.
  - intros [vd [vj [tg [pl [Hbeta1 [Hbeta2 [Hcp Hdisp]]]]]]].
    assert (Hvdb : vd <= FOeval e cs).
    { unfold beta in Hbeta1.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
                    (FOeval e ds * S (FOeval e i) + 1)).
      lia. }
    assert (Hvjb : vj <= FOeval e cj).
    { unfold beta in Hbeta2.
      pose proof (Nat.Div0.mod_le (FOeval e cj)
                    (FOeval e dj * S (FOeval e i) + 1)).
      lia. }
    pose proof (cpair_bound tg pl) as Htgplb.
    exists vd. split; [cbn [FOeval]; lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cj) _ HinB2 HinSB2).
    exists vj. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cj e B vd Hcj). lia. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF _ (B+4) cs ds i (FOVar B)
                      ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite (FOupdate_neq _ (B+2) vj B ltac:(lia)).
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above cs _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above cs e B vd Hcs).
      rewrite (FOeval_update_above ds _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above ds e B vd Hds).
      rewrite (FOeval_update_above i _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above i e B vd Hi).
      exact Hbeta1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF _ (B+8) cj dj i (FOVar (B+2))
                      ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above cj _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above cj e B vd Hcj).
      rewrite (FOeval_update_above dj _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above dj e B vd Hdj).
      rewrite (FOeval_update_above i _ (B+2) vj ltac:(lia)).
      rewrite (FOeval_update_above i e B vd Hi).
      exact Hbeta2. }
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc (FOVar (B+2))) _
               Hin12 HinS12).
    exists tg. split.
    { cbn [FOeval].
      rewrite (FOupdate_eq _ _ _). lia. }
    rewrite (FOsat_FOBexC _ (B+14) (FOSucc (FOVar (B+2))) _
               Hin14 HinS14).
    exists pl. split.
    { cbn [FOeval].
      rewrite (FOupdate_neq _ (B+12) tg (B+2) ltac:(lia)).
      rewrite (FOupdate_eq _ _ _). lia. }
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B vd)
                 (B+2) vj) (B+12) tg) (B+14) pl).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4.
      rewrite (FOeval_update_above t _ (B+14) pl ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+12) tg ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) vj ltac:(lia)).
      exact (FOeval_update_above t e B vd Ht). }
    assert (Ev0 : e4 0 = e 0).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg 0 ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) vj 0 ltac:(lia)).
      apply (FOupdate_neq _ B vd 0 ltac:(lia)). }
    assert (EvB : e4 B = vd).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) vj B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = vj).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+12) tg (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB12 : e4 (B+12) = tg).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+14) pl (B+12) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB14 : e4 (B+14) = pl).
    { unfold e4. apply FOupdate_eq. }
    assert (HL4 : forall a b c0 d0 r,
        (exists j, j < FOeval e4 len /\
           beta (FOeval e4 ct) (FOeval e4 dt) j = a /\
           beta (FOeval e4 c1) (FOeval e4 d1) j = b /\
           beta (FOeval e4 c2) (FOeval e4 d2) j = c0 /\
           beta (FOeval e4 c3) (FOeval e4 d3) j = d0 /\
           beta (FOeval e4 cr) (FOeval e4 dr) j = r) <->
        (exists j, j < FOeval e len /\
           beta (FOeval e ct) (FOeval e dt) j = a /\
           beta (FOeval e c1) (FOeval e d1) j = b /\
           beta (FOeval e c2) (FOeval e d2) j = c0 /\
           beta (FOeval e c3) (FOeval e d3) j = d0 /\
           beta (FOeval e cr) (FOeval e dr) j = r)).
    { intros a b c0 d0 r. split;
        intros [j [Hj [F1 [F2 [F3 [F4 F5]]]]]]; exists j.
      - rewrite (Hstab len Hlen) in Hj.
        rewrite (Hstab ct Hct), (Hstab dt Hdt) in F1.
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in F2.
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in F4.
        rewrite (Hstab cr Hcr), (Hstab dr Hdr) in F5.
        repeat split; assumption.
      - split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split; [rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'); exact F2|].
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split; [rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'); exact F4|].
        rewrite (Hstab cr Hcr), (Hstab dr Hdr); exact F5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      cbn [FOeval].
      rewrite EvB12, EvB14, EvB2.
      exact Hcp. }
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    rewrite (FOsat_FOOr _ _ _).
    destruct Hdisp as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
    + left.
      destruct H as [Heq Hth].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOTHAXc e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cores (FOVar B) Htb16
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite EvB.
      apply (proj2 (thax_sem_ext _ _ cores vd HL4)).
      exact Hth.
    + right; left.
      destruct H as [Heq Hlg].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOLOGc e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) Htb16 ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite EvB.
      apply (proj2 (logax_sem_ext _ _ vd HL4)).
      exact Hlg.
    + do 2 right; left.
      destruct H as [Heq [x [tc [P [Q [Hxtc [Hsh [Hr1 Hr2]]]]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJSUBST e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cpatAllElim (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia)
                      eq_refl eq_refl)).
      exists x, tc, P, Q.
      split.
      { cbn [FOeval]. rewrite EvB14. exact Hxtc. }
      split.
      { cbn [FOeval]. rewrite EvB.
        cbn [cpat_sem cpatAllElim pImpP pAllP].
        symmetry. exact Hsh. }
      split; [apply (proj2 (HL4 4 x tc P 1)); exact Hr1|].
      apply (proj2 (HL4 3 x tc P Q)). exact Hr2.
    + do 3 right; left.
      destruct H as [Heq [x [tc [P [Q [Hxtc [Hsh [Hr1 Hr2]]]]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJSUBST e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cpatExIntro (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia)
                      eq_refl eq_refl)).
      exists x, tc, P, Q.
      split.
      { cbn [FOeval]. rewrite EvB14. exact Hxtc. }
      split.
      { cbn [FOeval]. rewrite EvB.
        cbn [cpat_sem cpatExIntro pImpP pExP].
        symmetry. exact Hsh. }
      split; [apply (proj2 (HL4 4 x tc P 1)); exact Hr1|].
      apply (proj2 (HL4 3 x tc P Q)). exact Hr2.
    + do 4 right; left.
      destruct H as [Heq [i' [j' [bi [bj
        [Hpl' [Hi' [Hj' [Hb1' [Hb2' Hsh]]]]]]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJMP e4 (B+16) cs ds (FOVar B)
                      (FOVar (B+14)) i ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia))).
      exists i', j', bi, bj.
      split.
      { cbn [FOeval]. rewrite EvB14. exact Hpl'. }
      split.
      { rewrite (Hstab i Hi). exact Hi'. }
      split.
      { rewrite (Hstab i Hi). exact Hj'. }
      split.
      { rewrite (Hstab cs Hcs), (Hstab ds Hds). exact Hb1'. }
      split.
      { rewrite (Hstab cs Hcs), (Hstab ds Hds). exact Hb2'. }
      cbn [FOeval]. rewrite EvB. exact Hsh.
    + do 5 right; left.
      destruct H as [Heq [Hlt [bj [x [Hbt Hsh]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJGEN e4 (B+16) cs ds (FOVar B)
                      (FOVar (B+14)) i ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia))).
      split.
      { cbn [FOeval]. rewrite EvB14, (Hstab i Hi). exact Hlt. }
      exists bj, x.
      split.
      { cbn [FOeval].
        rewrite EvB14, (Hstab cs Hcs), (Hstab ds Hds). exact Hbt. }
      cbn [FOeval]. rewrite EvB. exact Hsh.
    + do 6 right; left.
      destruct H as [Heq [Hlt [bj [nu [core [na [p
        [Hbt [Hr1 [Hr2 [Hr3 [Hr4 Hsh]]]]]]]]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJLOEB e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len cs ds (FOVar B) (FOVar (B+14)) i
                      Htb16 ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(lia))).
      split.
      { cbn [FOeval]. rewrite EvB14, (Hstab i Hi). exact Hlt. }
      exists bj, nu, core, na, p.
      split.
      { cbn [FOeval].
        rewrite EvB14, (Hstab cs Hcs), (Hstab ds Hds). exact Hbt. }
      split.
      { destruct Hr1 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split.
        { rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ev0. exact F2. }
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split; [rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'); exact F4|].
        rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact F5. }
      split.
      { destruct Hr2 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split; [rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'); exact F2|].
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split.
        { rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), Ev0. exact F4. }
        rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact F5. }
      split.
      { destruct Hr3 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split.
        { cbn [FOeval].
          rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact F2. }
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split; [rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'); exact F4|].
        rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact F5. }
      split.
      { destruct Hr4 as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
        exists j.
        split; [rewrite (Hstab len Hlen); exact Hj|].
        split; [rewrite (Hstab ct Hct), (Hstab dt Hdt); exact F1|].
        split; [rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'); exact F2|].
        split; [rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'); exact F3|].
        split; [rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'); exact F4|].
        rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact F5. }
      cbn [FOeval]. rewrite EvB. exact Hsh.
    + do 7 right; left.
      destruct H as [Heq Hd].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOD2Sc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite EvB.
      apply (proj2 (d2s_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 8 right; left.
      destruct H as [Heq Hd].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOD3Sc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite EvB.
      apply (proj2 (d3s_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 9 right; left.
      destruct H as [Heq Hd].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FODMONSc cores e4 (B+16) ct dt c1 d1 c2 d2
                      c3 d3 cr dr len (FOVar B) Htb16
                      ltac:(cbn; lia))).
      cbn [FOeval].
      rewrite EvB.
      apply (proj2 (dmons_sem_ext cores _ _ vd HL4)).
      exact Hd.
    + do 10 right.
      destruct H as [Heq [x [PA [C0 [SS [Hxpa [Hsh [Hr1 [Hr2 [Hr3 Hr4]]]]]]]]]].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { cbn [FOsat FOeval]. rewrite EvB12. exact Heq. }
      apply (proj2 (FOsat_FOJIND e4 (B+16) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) (FOVar (B+14))
                      Htb16 ltac:(cbn; lia) ltac:(cbn; lia))).
      exists x, PA, C0, SS.
      split.
      { cbn [FOeval]. rewrite EvB14. symmetry. exact Hxpa. }
      split.
      { cbn [FOeval]. rewrite EvB.
        cbn [cpat_sem cpatInd pImpP pAllP].
        symmetry. exact Hsh. }
      split; [apply (proj2 (HL4 4 x (cpair 1 0) PA 1)); exact Hr1|].
      split; [apply (proj2 (HL4 3 x (cpair 1 0) PA C0)); exact Hr2|].
      split; [apply (proj2 (HL4 4 x (cpair 2 (cpair 0 x)) PA 1)); exact Hr3|].
      apply (proj2 (HL4 3 x (cpair 2 (cpair 0 x)) PA SS)). exact Hr4.
Qed.

Lemma FOdelta0_FOJUSTCK : forall B cores ct dt c1 d1 c2 d2 c3 d3 cr dr
    len cs ds cj dj i,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm cj < B -> FOmax_var_tm dj < B ->
  FOmax_var_tm i < B ->
  FOdelta0 (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
              cs ds cj dj i).
Proof.
  intros B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i
    Htb Hcs Hds Hcj Hdj Hi.
  assert (Htb16 : tbl_below (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (destruct Htb as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
          [Hcr [Hdr Hlen]]]]]]]]]]; unfold tbl_below; lia).
  unfold FOJUSTCK.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOTHAXc; [exact Htb16 | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOLOGc; [exact Htb16 | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOJSUBST; [exact Htb16 | cbn; lia | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOJSUBST; [exact Htb16 | cbn; lia | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOJMP; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOJGEN; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOJLOEB; try (exact Htb16); cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOD2Sc; [exact Htb16 | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOD3Sc; [exact Htb16 | cbn; lia]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FODMONSc; [exact Htb16 | cbn; lia]. }
  apply FOdelta0_and; [apply FOd0_eq|].
  apply FOdelta0_FOJIND; [exact Htb16 | cbn; lia | cbn; lia].
Qed.

Definition mfun (tag a1 a2 a3 : nat) : nat :=
  match tag with
  | 0 => if FOin_tm a1 (FOdecode_tm a2) then 1 else 0
  | 1 => if FOfree_in a1 (FOdecode_f a2) then 1 else 0
  | 2 => FOcode_tm (FOsubst_t a1 (FOdecode_tm a2) (FOdecode_tm a3))
  | 3 => FOcode_f (FOsubst_f a1 (FOdecode_tm a2) (FOdecode_f a3))
  | 4 => if FOsubst_ok a1 (FOdecode_tm a2) (FOdecode_f a3) then 1 else 0
  | _ => FOcode_tm (FOnumeral a1)
  end.

Definition step0_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (w tc r : nat) : Prop :=
  (exists y, y < S tc /\ cpair 0 y = tc /\
     ((y = w /\ r = 1) \/ (y <> w /\ r = 0)))
  \/ (cpair 1 0 = tc /\ r = 0)
  \/ (exists tc', tc' < S tc /\ cpair 2 tc' = tc /\ L 0 w tc' 0 r)
  \/ (exists p, p < S tc /\ cpair 3 p = tc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\
        cpair ta tb = p /\
        ((L 0 w ta 0 1 /\ r = 1) \/ (L 0 w ta 0 0 /\ L 0 w tb 0 r)))
  \/ (exists p, p < S tc /\ cpair 4 p = tc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\
        cpair ta tb = p /\
        ((L 0 w ta 0 1 /\ r = 1) \/ (L 0 w ta 0 0 /\ L 0 w tb 0 r))).

Lemma FOdelta0_FOSTEP0 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    w tc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r Htb Hw Htc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htbl2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htbl6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htbl28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP0.
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_or; apply FOdelta0_and;
      try apply FOd0_eq; apply FOdelta0_neg; apply FOd0_eq. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]. }
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_FOlookup; try assumption; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_or; apply FOdelta0_and.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia.
    - apply FOd0_eq.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia. }
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_or; apply FOdelta0_and.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia.
    - apply FOd0_eq.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia.
    - apply FOdelta0_FOlookup; try assumption; cbn; lia. }
Qed.

Lemma FOsat_STEP0_var_case : forall e B w tc r,
  FOmax_var_tm w < B -> FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc tc)
        (FOAnd (FOcpairF FOZero (FOVar B) tc)
           (FOOr (FOAnd (FOEq (FOVar B) w) (FOEq r (FOnumeral 1)))
                 (FOAnd (FONeg (FOEq (FOVar B) w)) (FOEq r FOZero)))))
   <-> exists y, y < S (FOeval e tc) /\ cpair 0 y = FOeval e tc /\
       ((y = FOeval e w /\ FOeval e r = 1)
        \/ (y <> FOeval e w /\ FOeval e r = 0))).
Proof.
  intros e B w tc r Hw Htc Hr.
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  split.
  - intros [y [Hy Hb]].
    assert (EB : FOeval (FOupdate e B y) (FOVar B) = y)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists y. split; [exact Hy|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb. destruct Hb as [Hcp Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    change (FOeval (FOupdate e B y) FOZero) with 0 in Hcp.
    rewrite EB, (FOeval_upd_above tc e B y Htc) in Hcp.
    split; [exact Hcp|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc; destruct Hc as [Hc1 Hc2].
    + left.
      change (FOeval (FOupdate e B y) (FOVar B)
              = FOeval (FOupdate e B y) w) in Hc1.
      change (FOeval (FOupdate e B y) r
              = FOeval (FOupdate e B y) (FOnumeral 1)) in Hc2.
      rewrite EB, (FOeval_upd_above w e B y Hw) in Hc1.
      rewrite (FOeval_upd_above r e B y Hr), FOeval_numeral in Hc2.
      split; assumption.
    + right.
      change ((FOeval (FOupdate e B y) (FOVar B)
               = FOeval (FOupdate e B y) w) -> False) in Hc1.
      change (FOeval (FOupdate e B y) r
              = FOeval (FOupdate e B y) FOZero) in Hc2.
      rewrite EB, (FOeval_upd_above w e B y Hw) in Hc1.
      rewrite (FOeval_upd_above r e B y Hr) in Hc2.
      change (FOeval e FOZero) with 0 in Hc2.
      split; assumption.
  - intros [y [Hy [Hcp Hca]]].
    assert (EB : FOeval (FOupdate e B y) (FOVar B) = y)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists y. split; [exact Hy|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      change (FOeval (FOupdate e B y) FOZero) with 0.
      rewrite EB, (FOeval_upd_above tc e B y Htc). exact Hcp. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[He1 He2]|[He1 He2]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change (FOeval (FOupdate e B y) (FOVar B)
                = FOeval (FOupdate e B y) w).
        rewrite EB, (FOeval_upd_above w e B y Hw). exact He1.
      * change (FOeval (FOupdate e B y) r
                = FOeval (FOupdate e B y) (FOnumeral 1)).
        rewrite (FOeval_upd_above r e B y Hr), FOeval_numeral.
        exact He2.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change ((FOeval (FOupdate e B y) (FOVar B)
                 = FOeval (FOupdate e B y) w) -> False).
        rewrite EB, (FOeval_upd_above w e B y Hw). exact He1.
      * change (FOeval (FOupdate e B y) r
                = FOeval (FOupdate e B y) FOZero).
        change (FOeval (FOupdate e B y) FOZero) with 0.
        rewrite (FOeval_upd_above r e B y Hr). exact He2.
Qed.

Lemma FOsat_STEP0_zero_case : forall e tc r,
  (FOsat e (FOAnd (FOcpairF (FOnumeral 1) FOZero tc) (FOEq r FOZero))
   <-> (cpair 1 0 = FOeval e tc /\ FOeval e r = 0)).
Proof.
  intros e tc r.
  rewrite (FOsat_FOAnd e _ _).
  rewrite (FOsat_FOcpairF e _ _ _).
  change (FOsat e (FOEq r FOZero))
    with (FOeval e r = FOeval e FOZero).
  change (FOeval e FOZero) with 0.
  rewrite FOeval_numeral.
  tauto.
Qed.

Lemma FOsat_STEP_unary_case : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len w tc r k tg,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc tc)
        (FOAnd (FOcpairF (FOnumeral k) (FOVar B) tc)
           (FOlookup (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOnumeral tg) w (FOVar B) FOZero r)))
   <-> exists tc', tc' < S (FOeval e tc) /\ cpair k tc' = FOeval e tc /\
       (exists j, j < FOeval e len /\
          beta (FOeval e ct) (FOeval e dt) j = tg /\
          beta (FOeval e c1) (FOeval e d1) j = FOeval e w /\
          beta (FOeval e c2) (FOeval e d2) j = tc' /\
          beta (FOeval e c3) (FOeval e d3) j = 0 /\
          beta (FOeval e cr) (FOeval e dr) j = FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r k tg Htb Hw Htc
    Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  split.
  - intros [y [Hy Hb]].
    assert (EB : FOeval (FOupdate e B y) (FOVar B) = y)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists y. split; [exact Hy|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb. destruct Hb as [Hcp Hlk].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above tc e B y Htc) in Hcp.
    split; [exact Hcp|].
    apply (proj1 (FOsat_FOlookup _ (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr
                    len (FOnumeral tg) w (FOVar B) FOZero r Htb2
                    ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)))
      in Hlk.
    destruct Hlk as [j [Hj Hfields]].
    rewrite (FOeval_upd_above len e B y Hlen) in Hj.
    rewrite FOeval_numeral in Hfields.
    rewrite (FOeval_upd_above ct e B y Hct),
      (FOeval_upd_above dt e B y Hdt),
      (FOeval_upd_above c1 e B y Hc1),
      (FOeval_upd_above d1 e B y Hd1),
      (FOeval_upd_above c2 e B y Hc2),
      (FOeval_upd_above d2 e B y Hd2),
      (FOeval_upd_above c3 e B y Hc3),
      (FOeval_upd_above d3 e B y Hd3),
      (FOeval_upd_above cr e B y Hcr),
      (FOeval_upd_above dr e B y Hdr),
      (FOeval_upd_above w e B y Hw),
      (FOeval_upd_above r e B y Hr), EB in Hfields.
    change (FOeval (FOupdate e B y) FOZero) with 0 in Hfields.
    exists j. split; [exact Hj | exact Hfields].
  - intros [tc' [Hy [Hcp [j [Hj Hfields]]]]].
    assert (EB : FOeval (FOupdate e B tc') (FOVar B) = tc')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists tc'. split; [exact Hy|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above tc e B tc' Htc). exact Hcp. }
    apply (proj2 (FOsat_FOlookup _ (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr
                    len (FOnumeral tg) w (FOVar B) FOZero r Htb2
                    ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia))).
    exists j.
    rewrite (FOeval_upd_above len e B tc' Hlen).
    rewrite FOeval_numeral.
    rewrite (FOeval_upd_above ct e B tc' Hct),
      (FOeval_upd_above dt e B tc' Hdt),
      (FOeval_upd_above c1 e B tc' Hc1),
      (FOeval_upd_above d1 e B tc' Hd1),
      (FOeval_upd_above c2 e B tc' Hc2),
      (FOeval_upd_above d2 e B tc' Hd2),
      (FOeval_upd_above c3 e B tc' Hc3),
      (FOeval_upd_above d3 e B tc' Hd3),
      (FOeval_upd_above cr e B tc' Hcr),
      (FOeval_upd_above dr e B tc' Hdr),
      (FOeval_upd_above w e B tc' Hw),
      (FOeval_upd_above r e B tc' Hr), EB.
    change (FOeval (FOupdate e B tc') FOZero) with 0.
    split; [exact Hj | exact Hfields].
Qed.

Lemma FOsat_STEP_bin_case : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len w tc r k tg,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc tc)
        (FOAnd (FOcpairF (FOnumeral k) (FOVar B) tc)
           (FOBexC (B+2) (FOSucc (FOVar B))
              (FOBexC (B+4) (FOSucc (FOVar B))
                 (FOAnd
                    (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                    (FOOr
                       (FOAnd
                          (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                             len (FOnumeral tg) w (FOVar (B+2)) FOZero
                             (FOnumeral 1))
                          (FOEq r (FOnumeral 1)))
                       (FOAnd
                          (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                             len (FOnumeral tg) w (FOVar (B+2)) FOZero
                             FOZero)
                          (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr
                             len (FOnumeral tg) w (FOVar (B+4)) FOZero
                             r))))))))
   <-> exists p, p < S (FOeval e tc) /\ cpair k p = FOeval e tc /\
       exists ta, ta < S p /\ exists tb, tb < S p /\
         cpair ta tb = p /\
         (((exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = tg /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e w /\
              beta (FOeval e c2) (FOeval e d2) j = ta /\
              beta (FOeval e c3) (FOeval e d3) j = 0 /\
              beta (FOeval e cr) (FOeval e dr) j = 1)
           /\ FOeval e r = 1)
          \/ ((exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = tg /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e w /\
              beta (FOeval e c2) (FOeval e d2) j = ta /\
              beta (FOeval e c3) (FOeval e d3) j = 0 /\
              beta (FOeval e cr) (FOeval e dr) j = 0)
           /\ (exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = tg /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e w /\
              beta (FOeval e c2) (FOeval e d2) j = tb /\
              beta (FOeval e c3) (FOeval e d3) j = 0 /\
              beta (FOeval e cr) (FOeval e dr) j = FOeval e r)))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r k tg Htb Hw Htc
    Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above tc e B p Htc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [ta [Hta Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) ta)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [tb [Htbnd Hin]].
    exists ta. split; [exact Hta|].
    exists tb. split; [exact Htbnd|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) ta) (B+4) tb)
      in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) tb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) ta ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = ta).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = tb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB, EvB2, EvB4 in Hcp2.
    split; [exact Hcp2|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
      destruct Hc as [Hl1 Hl2].
    + left.
      apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral tg) w (FOVar (B+2)) FOZero
                      (FOnumeral 1) Htb6
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(rewrite FOmax_var_numeral; lia))) in Hl1.
      destruct Hl1 as [j [Hj Hf]].
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
        (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
        (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), EvB2,
        !FOeval_numeral in Hf.
      rewrite (Eu len Hlen) in Hj.
      change (FOeval e3 FOZero) with 0 in Hf.
      split.
      * exists j. split; [exact Hj | exact Hf].
      * change (FOeval e3 r = FOeval e3 (FOnumeral 1)) in Hl2.
        rewrite (Eu r Hr), FOeval_numeral in Hl2. exact Hl2.
    + right.
      apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral tg) w (FOVar (B+2)) FOZero
                      FOZero Htb6
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))) in Hl1.
      apply (proj1 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral tg) w (FOVar (B+4)) FOZero r
                      Htb28
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(lia))) in Hl2.
      destruct Hl1 as [j [Hj Hf]].
      destruct Hl2 as [j' [Hj' Hf']].
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
        (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
        (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), EvB2,
        FOeval_numeral in Hf.
      rewrite (Eu len Hlen) in Hj.
      change (FOeval e3 FOZero) with 0 in Hf.
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
        (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
        (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), (Eu r Hr),
        EvB4, FOeval_numeral in Hf'.
      rewrite (Eu len Hlen) in Hj'.
      change (FOeval e3 FOZero) with 0 in Hf'.
      split.
      * exists j. split; [exact Hj | exact Hf].
      * exists j'. split; [exact Hj' | exact Hf'].
  - intros [p [Hp [Hcp [ta [Hta [tb [Htbnd [Hcp2 Hca]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above tc e B p Htc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists ta. split; [exact Hta|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) ta)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists tb. split; [exact Htbnd|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) ta) (B+4) tb).
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) tb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) ta ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = ta).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = tb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB, EvB2, EvB4. exact Hcp2. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[Hlk Hre]|[Hlk1 Hlk2]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral tg) w (FOVar (B+2)) FOZero
                        (FOnumeral 1) Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(rewrite FOmax_var_numeral; lia))).
        destruct Hlk as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), EvB2,
          !FOeval_numeral.
        change (FOeval e3 FOZero) with 0.
        split; [exact Hj | exact Hf].
      * change (FOeval e3 r = FOeval e3 (FOnumeral 1)).
        rewrite (Eu r Hr), FOeval_numeral. exact Hre.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral tg) w (FOVar (B+2)) FOZero
                        FOZero Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(cbn; lia))).
        destruct Hlk1 as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), EvB2,
          FOeval_numeral.
        change (FOeval e3 FOZero) with 0.
        split; [exact Hj | exact Hf].
      * apply (proj2 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral tg) w (FOVar (B+4)) FOZero
                        r Htb28
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(lia))).
        destruct Hlk2 as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), (Eu r Hr),
          EvB4, FOeval_numeral.
        change (FOeval e3 FOZero) with 0.
        split; [exact Hj | exact Hf].
Qed.

Lemma FOsat_STEP_quant0_case : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len w pc r k tg,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc pc)
        (FOAnd (FOcpairF (FOnumeral k) (FOVar B) pc)
           (FOBexC (B+2) (FOSucc (FOVar B))
              (FOBexC (B+4) (FOSucc (FOVar B))
                 (FOAnd
                    (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                    (FOOr
                       (FOAnd (FOEq (FOVar (B+2)) w) (FOEq r FOZero))
                       (FOAnd (FONeg (FOEq (FOVar (B+2)) w))
                          (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                             len (FOnumeral tg) w (FOVar (B+4)) FOZero
                             r))))))))
   <-> exists p, p < S (FOeval e pc) /\ cpair k p = FOeval e pc /\
       exists y, y < S p /\ exists pb, pb < S p /\
         cpair y pb = p /\
         ((y = FOeval e w /\ FOeval e r = 0)
          \/ (y <> FOeval e w /\
              (exists j, j < FOeval e len /\
                 beta (FOeval e ct) (FOeval e dt) j = tg /\
                 beta (FOeval e c1) (FOeval e d1) j = FOeval e w /\
                 beta (FOeval e c2) (FOeval e d2) j = pb /\
                 beta (FOeval e c3) (FOeval e d3) j = 0 /\
                 beta (FOeval e cr) (FOeval e dr) j = FOeval e r)))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg Htb Hw Hpc
    Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc pc) = S (FOeval e pc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc pc) _
             (FOin_tm_above (FOSucc pc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc pc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above pc e B p Hpc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [y [Hy Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [pb [Hpb Hin]].
    exists y. split; [exact Hy|].
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb)
      in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB, EvB2, EvB4 in Hcp2.
    split; [exact Hcp2|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
      destruct Hc as [Hq1 Hq2].
    + left.
      change (FOeval e3 (FOVar (B+2)) = FOeval e3 w) in Hq1.
      change (FOeval e3 r = FOeval e3 FOZero) in Hq2.
      rewrite EvB2, (Eu w Hw) in Hq1.
      rewrite (Eu r Hr) in Hq2.
      change (FOeval e3 FOZero) with 0 in Hq2.
      split; assumption.
    + right.
      change ((FOeval e3 (FOVar (B+2)) = FOeval e3 w) -> False) in Hq1.
      rewrite EvB2, (Eu w Hw) in Hq1.
      split; [exact Hq1|].
      apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral tg) w (FOVar (B+4)) FOZero r
                      Htb6
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(lia))) in Hq2.
      destruct Hq2 as [j [Hj Hf]].
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
        (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
        (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), (Eu r Hr), EvB4,
        FOeval_numeral in Hf.
      rewrite (Eu len Hlen) in Hj.
      change (FOeval e3 FOZero) with 0 in Hf.
      exists j. split; [exact Hj | exact Hf].
  - intros [p [Hp [Hcp [y [Hy [pb [Hpb [Hcp2 Hca]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above pc e B p Hpc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists y. split; [exact Hy|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb).
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB, EvB2, EvB4. exact Hcp2. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[He1 He2]|[He1 Hlk]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change (FOeval e3 (FOVar (B+2)) = FOeval e3 w).
        rewrite EvB2, (Eu w Hw). exact He1.
      * change (FOeval e3 r = FOeval e3 FOZero).
        change (FOeval e3 FOZero) with 0.
        rewrite (Eu r Hr). exact He2.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change ((FOeval e3 (FOVar (B+2)) = FOeval e3 w) -> False).
        rewrite EvB2, (Eu w Hw). exact He1.
      * apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral tg) w (FOVar (B+4)) FOZero
                        r Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(lia))).
        destruct Hlk as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu w Hw), (Eu r Hr),
          EvB4, FOeval_numeral.
        change (FOeval e3 FOZero) with 0.
        split; [exact Hj | exact Hf].
Qed.

Lemma FOsat_FOSTEP0 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    w tc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r)
   <-> step0_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e w) (FOeval e tc) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r Htb Hw Htc Hr.
  unfold FOSTEP0, step0_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_STEP0_var_case e B w tc r Hw Htc Hr).
  rewrite (FOsat_STEP0_zero_case e tc r).
  rewrite (FOsat_STEP_unary_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w tc r 2 0 Htb Hw Htc Hr).
  rewrite (FOsat_STEP_bin_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w tc r 3 0 Htb Hw Htc Hr).
  rewrite (FOsat_STEP_bin_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w tc r 4 0 Htb Hw Htc Hr).
  reflexivity.
Qed.

Definition step1_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (w pc r : nat) : Prop :=
  (exists p, p < S pc /\ cpair 0 p = pc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\
        cpair ta tb = p /\
        ((L 0 w ta 0 1 /\ r = 1) \/ (L 0 w ta 0 0 /\ L 0 w tb 0 r)))
  \/ (cpair 1 0 = pc /\ r = 0)
  \/ (exists p, p < S pc /\ cpair 2 p = pc /\
      exists pa, pa < S p /\ exists pb, pb < S p /\
        cpair pa pb = p /\
        ((L 1 w pa 0 1 /\ r = 1) \/ (L 1 w pa 0 0 /\ L 1 w pb 0 r)))
  \/ (exists p, p < S pc /\ cpair 3 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\
        cpair y pb = p /\
        ((y = w /\ r = 0) \/ (y <> w /\ L 1 w pb 0 r)))
  \/ (exists p, p < S pc /\ cpair 4 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\
        cpair y pb = p /\
        ((y = w /\ r = 0) \/ (y <> w /\ L 1 w pb 0 r))).

Lemma FOdelta0_FOSTEP_bin : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    w pc r k tg,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP_bin B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg Htb Hw Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_bin.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or; apply FOdelta0_and.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOd0_eq.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOSTEP_quant0 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len w pc r k tg,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0
    (FOSTEP_quant0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg Htb Hw Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_quant0.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or; apply FOdelta0_and.
  - apply FOd0_eq.
  - apply FOd0_eq.
  - apply FOdelta0_neg. apply FOd0_eq.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOSTEP1 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    w pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r Htb Hw Hpc Hr.
  unfold FOSTEP1.
  apply FOdelta0_or; [apply FOdelta0_FOSTEP_bin; assumption|].
  apply FOdelta0_or;
    [apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]|].
  apply FOdelta0_or; [apply FOdelta0_FOSTEP_bin; assumption|].
  apply FOdelta0_or; apply FOdelta0_FOSTEP_quant0; assumption.
Qed.

Lemma FOsat_FOSTEP1 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    w pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm w < B -> FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r)
   <-> step1_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e w) (FOeval e pc) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r Htb Hw Hpc Hr.
  unfold FOSTEP1, FOSTEP_bin, FOSTEP_quant0, step1_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_STEP_bin_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w pc r 0 0 Htb Hw Hpc Hr).
  rewrite (FOsat_STEP0_zero_case e pc r).
  rewrite (FOsat_STEP_bin_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w pc r 2 1 Htb Hw Hpc Hr).
  rewrite (FOsat_STEP_quant0_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w pc r 3 1 Htb Hw Hpc Hr).
  rewrite (FOsat_STEP_quant0_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
             w pc r 4 1 Htb Hw Hpc Hr).
  reflexivity.
Qed.

Definition step5_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (a1 r : nat) : Prop :=
  (a1 = 0 /\ cpair 1 0 = r)
  \/ (exists k', k' < a1 /\ a1 = S k' /\
      exists r', r' < r /\ L 5 k' 0 0 r' /\ cpair 2 r' = r).

Lemma FOdelta0_FOSTEP5 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    a1 r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm a1 < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r Htb Ha1 Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb4 : tbl_below (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP5.
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq | apply FOdelta0_FOcpairF]. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; lia | apply FOin_tm_above; lia |].
  apply FOdelta0_and; [apply FOd0_eq|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; lia | apply FOin_tm_above; lia |].
  apply FOdelta0_and; [|apply FOdelta0_FOcpairF].
  apply FOdelta0_FOlookup; try assumption;
    rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOsat_FOSTEP5 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    a1 r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm a1 < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r)
   <-> step5_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e a1) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r Htb Ha1 Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb4 : tbl_below (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  unfold FOSTEP5, step5_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOAnd e _ _).
  rewrite (FOsat_FOcpairF e _ _ _).
  rewrite (FOsat_FOBexC e B a1 _
             (FOin_tm_above a1 B ltac:(lia))
             (FOin_tm_above a1 (S B) ltac:(lia))).
  change (FOsat e (FOEq a1 FOZero))
    with (FOeval e a1 = FOeval e FOZero).
  change (FOeval e FOZero) with 0.
  rewrite FOeval_numeral.
  apply Morphisms_Prop.or_iff_morphism; [tauto|].
  split.
  - intros [k' [Hk' Hb]].
    assert (EB : FOeval (FOupdate e B k') (FOVar B) = k')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Heq Hin].
    change (FOeval (FOupdate e B k') a1
            = FOeval (FOupdate e B k') (FOSucc (FOVar B))) in Heq.
    assert (Es : FOeval (FOupdate e B k') (FOSucc (FOVar B)) = S k')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Es, (FOeval_upd_above a1 e B k' Ha1) in Heq.
    exists k'. split; [exact Hk'|]. split; [exact Heq|].
    rewrite (FOsat_FOBexC _ (B+2) r _
               (FOin_tm_above r (B+2) ltac:(lia))
               (FOin_tm_above r (S (B+2)) ltac:(lia))) in Hin.
    rewrite (FOeval_upd_above r e B k' Hr) in Hin.
    destruct Hin as [r' [Hr' Hin]].
    set (e2 := FOupdate (FOupdate e B k') (B+2) r') in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e2 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e2.
      rewrite (FOeval_upd_above t0 _ (B+2) r' ltac:(lia)).
      exact (FOeval_upd_above t0 e B k' Ht0). }
    assert (EvB : FOeval e2 (FOVar B) = k').
    { unfold e2. cbn. unfold FOupdate.
      rewrite E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e2 (FOVar (B+2)) = r').
    { unfold e2. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hlk Hcp].
    apply (proj1 (FOsat_FOlookup e2 (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr
                    len (FOnumeral 5) (FOVar B) FOZero FOZero
                    (FOVar (B+2)) Htb4
                    ltac:(rewrite FOmax_var_numeral; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
                    ltac:(cbn; lia))) in Hlk.
    destruct Hlk as [j [Hj Hf]].
    rewrite (Eu len Hlen) in Hj.
    rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
      (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
      (Eu cr Hcr), (Eu dr Hdr), EvB, EvB2, FOeval_numeral in Hf.
    change (FOeval e2 FOZero) with 0 in Hf.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EvB2, (Eu r Hr) in Hcp.
    exists r'. split; [exact Hr'|]. split.
    + exists j. split; [exact Hj | exact Hf].
    + exact Hcp.
  - intros [k' [Hk' [Heq [r' [Hr' [Hlk Hcp]]]]]].
    assert (EB : FOeval (FOupdate e B k') (FOVar B) = k')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists k'. split; [exact Hk'|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { change (FOeval (FOupdate e B k') a1
              = FOeval (FOupdate e B k') (FOSucc (FOVar B))).
      assert (Es : FOeval (FOupdate e B k') (FOSucc (FOVar B)) = S k')
        by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
      rewrite Es, (FOeval_upd_above a1 e B k' Ha1). exact Heq. }
    rewrite (FOsat_FOBexC _ (B+2) r _
               (FOin_tm_above r (B+2) ltac:(lia))
               (FOin_tm_above r (S (B+2)) ltac:(lia))).
    rewrite (FOeval_upd_above r e B k' Hr).
    exists r'. split; [exact Hr'|].
    set (e2 := FOupdate (FOupdate e B k') (B+2) r').
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e2 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e2.
      rewrite (FOeval_upd_above t0 _ (B+2) r' ltac:(lia)).
      exact (FOeval_upd_above t0 e B k' Ht0). }
    assert (EvB : FOeval e2 (FOVar B) = k').
    { unfold e2. cbn. unfold FOupdate.
      rewrite E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e2 (FOVar (B+2)) = r').
    { unfold e2. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e2 (B+4) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral 5) (FOVar B) FOZero FOZero
                      (FOVar (B+2)) Htb4
                      ltac:(rewrite FOmax_var_numeral; lia)
                      ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      destruct Hlk as [j [Hj Hf]].
      exists j.
      rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
        (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
        (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), EvB, EvB2,
        FOeval_numeral.
      change (FOeval e2 FOZero) with 0.
      split; [exact Hj | exact Hf]. }
    apply (proj2 (FOsat_FOcpairF _ _ _ _)).
    rewrite FOeval_numeral, EvB2, (Eu r Hr). exact Hcp.
Qed.

Lemma FOsat_STEP_substvar_case : forall e B x sc tc r,
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc tc)
        (FOAnd (FOcpairF FOZero (FOVar B) tc)
           (FOOr (FOAnd (FOEq (FOVar B) x) (FOEq r sc))
                 (FOAnd (FONeg (FOEq (FOVar B) x)) (FOEq r tc)))))
   <-> exists y, y < S (FOeval e tc) /\ cpair 0 y = FOeval e tc /\
       ((y = FOeval e x /\ FOeval e r = FOeval e sc)
        \/ (y <> FOeval e x /\ FOeval e r = FOeval e tc))).
Proof.
  intros e B x sc tc r Hx Hsc Htc Hr.
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  split.
  - intros [y [Hy Hb]].
    assert (EB : FOeval (FOupdate e B y) (FOVar B) = y)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists y. split; [exact Hy|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb. destruct Hb as [Hcp Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    change (FOeval (FOupdate e B y) FOZero) with 0 in Hcp.
    rewrite EB, (FOeval_upd_above tc e B y Htc) in Hcp.
    split; [exact Hcp|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc; destruct Hc as [Hq1 Hq2].
    + left.
      change (FOeval (FOupdate e B y) (FOVar B)
              = FOeval (FOupdate e B y) x) in Hq1.
      change (FOeval (FOupdate e B y) r
              = FOeval (FOupdate e B y) sc) in Hq2.
      rewrite EB, (FOeval_upd_above x e B y Hx) in Hq1.
      rewrite (FOeval_upd_above r e B y Hr),
        (FOeval_upd_above sc e B y Hsc) in Hq2.
      split; assumption.
    + right.
      change ((FOeval (FOupdate e B y) (FOVar B)
               = FOeval (FOupdate e B y) x) -> False) in Hq1.
      change (FOeval (FOupdate e B y) r
              = FOeval (FOupdate e B y) tc) in Hq2.
      rewrite EB, (FOeval_upd_above x e B y Hx) in Hq1.
      rewrite (FOeval_upd_above r e B y Hr),
        (FOeval_upd_above tc e B y Htc) in Hq2.
      split; assumption.
  - intros [y [Hy [Hcp Hca]]].
    assert (EB : FOeval (FOupdate e B y) (FOVar B) = y)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists y. split; [exact Hy|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      change (FOeval (FOupdate e B y) FOZero) with 0.
      rewrite EB, (FOeval_upd_above tc e B y Htc). exact Hcp. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[He1 He2]|[He1 He2]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change (FOeval (FOupdate e B y) (FOVar B)
                = FOeval (FOupdate e B y) x).
        rewrite EB, (FOeval_upd_above x e B y Hx). exact He1.
      * change (FOeval (FOupdate e B y) r
                = FOeval (FOupdate e B y) sc).
        rewrite (FOeval_upd_above r e B y Hr),
          (FOeval_upd_above sc e B y Hsc). exact He2.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change ((FOeval (FOupdate e B y) (FOVar B)
                 = FOeval (FOupdate e B y) x) -> False).
        rewrite EB, (FOeval_upd_above x e B y Hx). exact He1.
      * change (FOeval (FOupdate e B y) r
                = FOeval (FOupdate e B y) tc).
        rewrite (FOeval_upd_above r e B y Hr),
          (FOeval_upd_above tc e B y Htc). exact He2.
Qed.

Lemma FOsat_STEP_substun_case : forall e B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len x sc tc r ktag lktag rtag,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc tc)
        (FOAnd (FOcpairF (FOnumeral ktag) (FOVar B) tc)
           (FOBexC (B+2) r
              (FOAnd
                 (FOlookup (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                    (FOnumeral lktag) x sc (FOVar B) (FOVar (B+2)))
                 (FOcpairF (FOnumeral rtag) (FOVar (B+2)) r)))))
   <-> exists tc', tc' < S (FOeval e tc) /\
       cpair ktag tc' = FOeval e tc /\
       exists r', r' < FOeval e r /\
         (exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = lktag /\
            beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
            beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
            beta (FOeval e c3) (FOeval e d3) j = tc' /\
            beta (FOeval e cr) (FOeval e dr) j = r') /\
         cpair rtag r' = FOeval e r).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r ktag lktag
    rtag Htb Hx Hsc Htc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb4 : tbl_below (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  split.
  - intros [tc' [Hy Hb]].
    assert (EB : FOeval (FOupdate e B tc') (FOVar B) = tc')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists tc'. split; [exact Hy|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb. destruct Hb as [Hcp Hin].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above tc e B tc' Htc) in Hcp.
    split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) r _
               (FOin_tm_above r (B+2) ltac:(lia))
               (FOin_tm_above r (S (B+2)) ltac:(lia))) in Hin.
    rewrite (FOeval_upd_above r e B tc' Hr) in Hin.
    destruct Hin as [r' [Hr' Hin]].
    set (e2 := FOupdate (FOupdate e B tc') (B+2) r') in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e2 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e2.
      rewrite (FOeval_upd_above t0 _ (B+2) r' ltac:(lia)).
      exact (FOeval_upd_above t0 e B tc' Ht0). }
    assert (EvB : FOeval e2 (FOVar B) = tc').
    { unfold e2. cbn. unfold FOupdate.
      rewrite E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e2 (FOVar (B+2)) = r').
    { unfold e2. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hlk Hcp2].
    apply (proj1 (FOsat_FOlookup e2 (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr
                    len (FOnumeral lktag) x sc (FOVar B) (FOVar (B+2))
                    Htb4
                    ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia)
                    ltac:(cbn; lia))) in Hlk.
    destruct Hlk as [j [Hj Hf]].
    rewrite (Eu len Hlen) in Hj.
    rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
      (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
      (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc), EvB, EvB2,
      FOeval_numeral in Hf.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite FOeval_numeral, EvB2, (Eu r Hr) in Hcp2.
    exists r'. split; [exact Hr'|]. split.
    + exists j. split; [exact Hj | exact Hf].
    + exact Hcp2.
  - intros [tc' [Hy [Hcp [r' [Hr' [Hlk Hcp2]]]]]].
    assert (EB : FOeval (FOupdate e B tc') (FOVar B) = tc')
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists tc'. split; [exact Hy|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above tc e B tc' Htc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) r _
               (FOin_tm_above r (B+2) ltac:(lia))
               (FOin_tm_above r (S (B+2)) ltac:(lia))).
    rewrite (FOeval_upd_above r e B tc' Hr).
    exists r'. split; [exact Hr'|].
    set (e2 := FOupdate (FOupdate e B tc') (B+2) r').
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e2 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e2.
      rewrite (FOeval_upd_above t0 _ (B+2) r' ltac:(lia)).
      exact (FOeval_upd_above t0 e B tc' Ht0). }
    assert (EvB : FOeval e2 (FOVar B) = tc').
    { unfold e2. cbn. unfold FOupdate.
      rewrite E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e2 (FOVar (B+2)) = r').
    { unfold e2. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e2 (B+4) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral lktag) x sc (FOVar B)
                      (FOVar (B+2)) Htb4
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      destruct Hlk as [j [Hj Hf]].
      exists j.
      rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
        (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
        (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc),
        EvB, EvB2, FOeval_numeral.
      split; [exact Hj | exact Hf]. }
    apply (proj2 (FOsat_FOcpairF _ _ _ _)).
    rewrite FOeval_numeral, EvB2, (Eu r Hr). exact Hcp2.
Qed.

Lemma FOdelta0_FOSTEP_substbin : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len x sc tc r ktag lktag rtag,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc tc r ktag lktag rtag).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r ktag lktag rtag
    Htb Hx Hsc Htc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb10 : tbl_below (B+10) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb32 : tbl_below (B+32) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_substbin.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; apply FOdelta0_FOcpairF.
Qed.

Lemma FOsat_FOSTEP_substbin : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len x sc tc r ktag lktag rtag,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc tc r ktag lktag rtag)
   <-> exists p, p < S (FOeval e tc) /\
       cpair ktag p = FOeval e tc /\
       exists ta, ta < S p /\ exists tb, tb < S p /\
         cpair ta tb = p /\
         exists ra, ra < S (FOeval e r) /\
         exists rb, rb < S (FOeval e r) /\
           (exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = lktag /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
              beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
              beta (FOeval e c3) (FOeval e d3) j = ta /\
              beta (FOeval e cr) (FOeval e dr) j = ra) /\
           (exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = lktag /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
              beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
              beta (FOeval e c3) (FOeval e d3) j = tb /\
              beta (FOeval e cr) (FOeval e dr) j = rb) /\
           exists q, q < S (FOeval e r) /\ cpair ra rb = q /\
             cpair rtag q = FOeval e r).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r ktag lktag
    rtag Htb Hx Hsc Htc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb10 : tbl_below (B+10) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb32 : tbl_below (B+32) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E06 : Nat.eqb B (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E08 : Nat.eqb B (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E26 : Nat.eqb (B+2) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E28 : Nat.eqb (B+2) (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E46 : Nat.eqb (B+4) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E48 : Nat.eqb (B+4) (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E68 : Nat.eqb (B+6) (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E654 : Nat.eqb (B+6) (B+54) = false)
    by (apply Nat.eqb_neq; lia).
  assert (E854 : Nat.eqb (B+8) (B+54) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc tc) = S (FOeval e tc)) by reflexivity.
  unfold FOSTEP_substbin.
  rewrite (FOsat_FOBexC e B (FOSucc tc) _
             (FOin_tm_above (FOSucc tc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc tc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above tc e B p Htc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [ta [Hta Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) ta)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [tb [Htbnd Hin]].
    exists ta. split; [exact Hta|].
    exists tb. split; [exact Htbnd|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hin].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) ta) (B+4) tb)
      in *.
    assert (Eu3 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) tb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) ta ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB3 : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB23 : FOeval e3 (FOVar (B+2)) = ta).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB43 : FOeval e3 (FOVar (B+4)) = tb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB3, EvB23, EvB43 in Hcp2.
    split; [exact Hcp2|].
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+6) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+6)) ltac:(cbn; lia)))
      in Hin.
    assert (EsR3 : FOeval e3 (FOSucc r) = S (FOeval e r)).
    { change (S (FOeval e3 r) = S (FOeval e r)).
      rewrite (Eu3 r Hr). reflexivity. }
    rewrite EsR3 in Hin.
    destruct Hin as [ra [Hra Hin]].
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+8) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+8)) ltac:(cbn; lia)))
      in Hin.
    assert (EsR4 : FOeval (FOupdate e3 (B+6) ra) (FOSucc r)
                   = S (FOeval e r)).
    { change (S (FOeval (FOupdate e3 (B+6) ra) r) = S (FOeval e r)).
      rewrite (FOeval_upd_above r _ (B+6) ra ltac:(lia)).
      rewrite (Eu3 r Hr). reflexivity. }
    rewrite EsR4 in Hin.
    destruct Hin as [rb [Hrb Hin]].
    exists ra. split; [exact Hra|].
    exists rb. split; [exact Hrb|].
    set (e5 := FOupdate (FOupdate e3 (B+6) ra) (B+8) rb) in *.
    assert (Eu5 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e5 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e5.
      rewrite (FOeval_upd_above t0 _ (B+8) rb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+6) ra ltac:(lia)).
      exact (Eu3 t0 Ht0). }
    assert (EvB25 : FOeval e5 (FOVar (B+2)) = ta).
    { unfold e5, e3. cbn. unfold FOupdate.
      rewrite E28, E26, E24, Nat.eqb_refl. reflexivity. }
    assert (EvB45 : FOeval e5 (FOVar (B+4)) = tb).
    { unfold e5, e3. cbn. unfold FOupdate.
      rewrite E48, E46, Nat.eqb_refl. reflexivity. }
    assert (EvB65 : FOeval e5 (FOVar (B+6)) = ra).
    { unfold e5. cbn. unfold FOupdate.
      rewrite E68, Nat.eqb_refl. reflexivity. }
    assert (EvB85 : FOeval e5 (FOVar (B+8)) = rb).
    { unfold e5. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hlk1 Hin].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hlk2 Hin].
    apply (proj1 (FOsat_FOlookup e5 (B+10) ct dt c1 d1 c2 d2 c3 d3 cr
                    dr len (FOnumeral lktag) x sc (FOVar (B+2))
                    (FOVar (B+6)) Htb10
                    ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia)
                    ltac:(cbn; lia))) in Hlk1.
    apply (proj1 (FOsat_FOlookup e5 (B+32) ct dt c1 d1 c2 d2 c3 d3 cr
                    dr len (FOnumeral lktag) x sc (FOVar (B+4))
                    (FOVar (B+8)) Htb32
                    ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                    ltac:(lia) ltac:(cbn; lia)
                    ltac:(cbn; lia))) in Hlk2.
    destruct Hlk1 as [j [Hj Hf]].
    destruct Hlk2 as [j' [Hj' Hf']].
    rewrite (Eu5 ct Hct), (Eu5 dt Hdt), (Eu5 c1 Hc1), (Eu5 d1 Hd1),
      (Eu5 c2 Hc2), (Eu5 d2 Hd2), (Eu5 c3 Hc3), (Eu5 d3 Hd3),
      (Eu5 cr Hcr), (Eu5 dr Hdr), (Eu5 x Hx), (Eu5 sc Hsc), EvB25,
      EvB65, FOeval_numeral in Hf.
    rewrite (Eu5 len Hlen) in Hj.
    rewrite (Eu5 ct Hct), (Eu5 dt Hdt), (Eu5 c1 Hc1), (Eu5 d1 Hd1),
      (Eu5 c2 Hc2), (Eu5 d2 Hd2), (Eu5 c3 Hc3), (Eu5 d3 Hd3),
      (Eu5 cr Hcr), (Eu5 dr Hdr), (Eu5 x Hx), (Eu5 sc Hsc), EvB45,
      EvB85, FOeval_numeral in Hf'.
    rewrite (Eu5 len Hlen) in Hj'.
    split; [exists j; split; [exact Hj | exact Hf]|].
    split; [exists j'; split; [exact Hj' | exact Hf']|].
    rewrite (FOsat_FOBexC _ (B+54) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+54) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+54))
                  ltac:(cbn; lia))) in Hin.
    assert (EbS : FOeval e5 (FOSucc r) = S (FOeval e r)).
    { change (S (FOeval e5 r) = S (FOeval e r)).
      rewrite (Eu5 r Hr). reflexivity. }
    rewrite EbS in Hin.
    destruct Hin as [q [Hq Hin]].
    set (e6 := FOupdate e5 (B+54) q) in *.
    assert (EvB66 : FOeval e6 (FOVar (B+6)) = ra).
    { unfold e6, e5. cbn. unfold FOupdate.
      rewrite E654, E68, Nat.eqb_refl. reflexivity. }
    assert (EvB86 : FOeval e6 (FOVar (B+8)) = rb).
    { unfold e6, e5. cbn. unfold FOupdate.
      rewrite E854, Nat.eqb_refl. reflexivity. }
    assert (EvQ6 : FOeval e6 (FOVar (B+54)) = q).
    { unfold e6. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    assert (Er6 : FOeval e6 r = FOeval e r).
    { unfold e6.
      rewrite (FOeval_upd_above r _ (B+54) q ltac:(lia)).
      exact (Eu5 r Hr). }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hq1 Hq2].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hq1.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hq2.
    rewrite EvB66, EvB86, EvQ6 in Hq1.
    rewrite FOeval_numeral, EvQ6, Er6 in Hq2.
    exists q. split; [exact Hq|]. split; [exact Hq1 | exact Hq2].
  - intros [p [Hp [Hcp [ta [Hta [tb [Htbnd [Hcp2
      [ra [Hra [rb [Hrb [Hlk1 [Hlk2 [q [Hq [Hq1 Hq2]]]]]]]]]]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above tc e B p Htc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists ta. split; [exact Hta|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) ta)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists tb. split; [exact Htbnd|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) ta) (B+4) tb).
    assert (Eu3 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) tb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) ta ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB3 : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB23 : FOeval e3 (FOVar (B+2)) = ta).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB43 : FOeval e3 (FOVar (B+4)) = tb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB3, EvB23, EvB43. exact Hcp2. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+6) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+6)) ltac:(cbn; lia))).
    assert (EsR3 : FOeval e3 (FOSucc r) = S (FOeval e r)).
    { change (S (FOeval e3 r) = S (FOeval e r)).
      rewrite (Eu3 r Hr). reflexivity. }
    rewrite EsR3.
    exists ra. split; [exact Hra|].
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+8) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+8)) ltac:(cbn; lia))).
    assert (EsR4 : FOeval (FOupdate e3 (B+6) ra) (FOSucc r)
                   = S (FOeval e r)).
    { change (S (FOeval (FOupdate e3 (B+6) ra) r) = S (FOeval e r)).
      rewrite (FOeval_upd_above r _ (B+6) ra ltac:(lia)).
      rewrite (Eu3 r Hr). reflexivity. }
    rewrite EsR4.
    exists rb. split; [exact Hrb|].
    set (e5 := FOupdate (FOupdate e3 (B+6) ra) (B+8) rb).
    assert (Eu5 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e5 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e5.
      rewrite (FOeval_upd_above t0 _ (B+8) rb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+6) ra ltac:(lia)).
      exact (Eu3 t0 Ht0). }
    assert (EvB25 : FOeval e5 (FOVar (B+2)) = ta).
    { unfold e5, e3. cbn. unfold FOupdate.
      rewrite E28, E26, E24, Nat.eqb_refl. reflexivity. }
    assert (EvB45 : FOeval e5 (FOVar (B+4)) = tb).
    { unfold e5, e3. cbn. unfold FOupdate.
      rewrite E48, E46, Nat.eqb_refl. reflexivity. }
    assert (EvB65 : FOeval e5 (FOVar (B+6)) = ra).
    { unfold e5. cbn. unfold FOupdate.
      rewrite E68, Nat.eqb_refl. reflexivity. }
    assert (EvB85 : FOeval e5 (FOVar (B+8)) = rb).
    { unfold e5. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e5 (B+10) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral lktag) x sc (FOVar (B+2))
                      (FOVar (B+6)) Htb10
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      destruct Hlk1 as [j [Hj Hf]].
      exists j.
      rewrite (Eu5 len Hlen), (Eu5 ct Hct), (Eu5 dt Hdt), (Eu5 c1 Hc1),
        (Eu5 d1 Hd1), (Eu5 c2 Hc2), (Eu5 d2 Hd2), (Eu5 c3 Hc3),
        (Eu5 d3 Hd3), (Eu5 cr Hcr), (Eu5 dr Hdr), (Eu5 x Hx),
        (Eu5 sc Hsc), EvB25, EvB65, FOeval_numeral.
      split; [exact Hj | exact Hf]. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e5 (B+32) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral lktag) x sc (FOVar (B+4))
                      (FOVar (B+8)) Htb32
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      destruct Hlk2 as [j [Hj Hf]].
      exists j.
      rewrite (Eu5 len Hlen), (Eu5 ct Hct), (Eu5 dt Hdt), (Eu5 c1 Hc1),
        (Eu5 d1 Hd1), (Eu5 c2 Hc2), (Eu5 d2 Hd2), (Eu5 c3 Hc3),
        (Eu5 d3 Hd3), (Eu5 cr Hcr), (Eu5 dr Hdr), (Eu5 x Hx),
        (Eu5 sc Hsc), EvB45, EvB85, FOeval_numeral.
      split; [exact Hj | exact Hf]. }
    rewrite (FOsat_FOBexC _ (B+54) (FOSucc r) _
               (FOin_tm_above (FOSucc r) (B+54) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc r) (S (B+54))
                  ltac:(cbn; lia))).
    assert (EbS : FOeval e5 (FOSucc r) = S (FOeval e r)).
    { change (S (FOeval e5 r) = S (FOeval e r)).
      rewrite (Eu5 r Hr). reflexivity. }
    rewrite EbS.
    exists q. split; [exact Hq|].
    set (e6 := FOupdate e5 (B+54) q).
    assert (EvB66 : FOeval e6 (FOVar (B+6)) = ra).
    { unfold e6, e5. cbn. unfold FOupdate.
      rewrite E654, E68, Nat.eqb_refl. reflexivity. }
    assert (EvB86 : FOeval e6 (FOVar (B+8)) = rb).
    { unfold e6, e5. cbn. unfold FOupdate.
      rewrite E854, Nat.eqb_refl. reflexivity. }
    assert (EvQ6 : FOeval e6 (FOVar (B+54)) = q).
    { unfold e6. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    assert (Er6 : FOeval e6 r = FOeval e r).
    { unfold e6.
      rewrite (FOeval_upd_above r _ (B+54) q ltac:(lia)).
      exact (Eu5 r Hr). }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB66, EvB86, EvQ6. exact Hq1. }
    apply (proj2 (FOsat_FOcpairF _ _ _ _)).
    rewrite FOeval_numeral, EvQ6, Er6. exact Hq2.
Qed.

Lemma FOsat_STEP_substzero_case : forall e tc r,
  (FOsat e (FOAnd (FOcpairF (FOnumeral 1) FOZero tc) (FOEq r tc))
   <-> (cpair 1 0 = FOeval e tc /\ FOeval e r = FOeval e tc)).
Proof.
  intros e tc r.
  rewrite (FOsat_FOAnd e _ _).
  rewrite (FOsat_FOcpairF e _ _ _).
  change (FOsat e (FOEq r tc)) with (FOeval e r = FOeval e tc).
  change (FOeval e FOZero) with 0.
  rewrite FOeval_numeral.
  tauto.
Qed.

Definition step2_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (x sc tc r : nat) : Prop :=
  (exists y, y < S tc /\ cpair 0 y = tc /\
     ((y = x /\ r = sc) \/ (y <> x /\ r = tc)))
  \/ (cpair 1 0 = tc /\ r = tc)
  \/ (exists tc', tc' < S tc /\ cpair 2 tc' = tc /\
      exists r', r' < r /\ L 2 x sc tc' r' /\ cpair 2 r' = r)
  \/ (exists p, p < S tc /\ cpair 3 p = tc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\ cpair ta tb = p /\
      exists ra, ra < S r /\ exists rb, rb < S r /\
        L 2 x sc ta ra /\ L 2 x sc tb rb /\
        exists q, q < S r /\ cpair ra rb = q /\ cpair 3 q = r)
  \/ (exists p, p < S tc /\ cpair 4 p = tc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\ cpair ta tb = p /\
      exists ra, ra < S r /\ exists rb, rb < S r /\
        L 2 x sc ta ra /\ L 2 x sc tb rb /\
        exists q, q < S r /\ cpair ra rb = q /\ cpair 4 q = r).

Lemma FOdelta0_FOSTEP2 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc tc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP2 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r Htb Hx Hsc Htc
    Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb4 : tbl_below (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP2.
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_or; apply FOdelta0_and;
      try apply FOd0_eq; apply FOdelta0_neg; apply FOd0_eq. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]. }
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
    apply FOdelta0_FOBexC;
      [apply FOin_tm_above; lia | apply FOin_tm_above; lia |].
    apply FOdelta0_and; [|apply FOdelta0_FOcpairF].
    apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_or; apply FOdelta0_FOSTEP_substbin; assumption.
Qed.

Lemma FOsat_FOSTEP2 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc tc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm tc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP2 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r)
   <-> step2_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e x) (FOeval e sc) (FOeval e tc) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r Htb Hx Hsc
    Htc Hr.
  unfold FOSTEP2, step2_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_STEP_substvar_case e B x sc tc r Hx Hsc Htc Hr).
  rewrite (FOsat_STEP_substzero_case e tc r).
  rewrite (FOsat_STEP_substun_case e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc tc r 2 2 2 Htb Hx Hsc Htc Hr).
  rewrite (FOsat_FOSTEP_substbin e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc tc r 3 2 3 Htb Hx Hsc Htc Hr).
  rewrite (FOsat_FOSTEP_substbin e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc tc r 4 2 4 Htb Hx Hsc Htc Hr).
  reflexivity.
Qed.

Lemma FOdelta0_FOSTEP_substquant : forall B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len x sc pc r ktag,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r ktag).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r ktag Htb Hx Hsc
    Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb8 : tbl_below (B+8) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_substquant.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or.
  { apply FOdelta0_and; apply FOd0_eq. }
  apply FOdelta0_and.
  { apply FOdelta0_neg. apply FOd0_eq. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; lia | apply FOin_tm_above; lia |].
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; apply FOdelta0_FOcpairF.
Qed.

Lemma FOsat_FOSTEP_substquant : forall e B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len x sc pc r ktag,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r ktag)
   <-> exists p, p < S (FOeval e pc) /\
       cpair ktag p = FOeval e pc /\
       exists y, y < S p /\ exists pb, pb < S p /\
         cpair y pb = p /\
         ((y = FOeval e x /\ FOeval e r = FOeval e pc)
          \/ (y <> FOeval e x /\
              exists rb, rb < FOeval e r /\
                (exists j, j < FOeval e len /\
                   beta (FOeval e ct) (FOeval e dt) j = 3 /\
                   beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
                   beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
                   beta (FOeval e c3) (FOeval e d3) j = pb /\
                   beta (FOeval e cr) (FOeval e dr) j = rb) /\
                exists q, q < S (FOeval e r) /\ cpair y rb = q /\
                  cpair ktag q = FOeval e r))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r ktag Htb Hx
    Hsc Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb8 : tbl_below (B+8) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E26 : Nat.eqb (B+2) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E46 : Nat.eqb (B+4) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E230 : Nat.eqb (B+2) (B+30) = false)
    by (apply Nat.eqb_neq; lia).
  assert (E630 : Nat.eqb (B+6) (B+30) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc pc) = S (FOeval e pc)) by reflexivity.
  unfold FOSTEP_substquant.
  rewrite (FOsat_FOBexC e B (FOSucc pc) _
             (FOin_tm_above (FOSucc pc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc pc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above pc e B p Hpc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [y [Hy Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [pb [Hpb Hin]].
    exists y. split; [exact Hy|].
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb)
      in *.
    assert (Eu3 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB3 : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB23 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB43 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB3, EvB23, EvB43 in Hcp2.
    split; [exact Hcp2|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
      destruct Hc as [Hq1 Hq2].
    + left.
      change (FOeval e3 (FOVar (B+2)) = FOeval e3 x) in Hq1.
      change (FOeval e3 r = FOeval e3 pc) in Hq2.
      rewrite EvB23, (Eu3 x Hx) in Hq1.
      rewrite (Eu3 r Hr), (Eu3 pc Hpc) in Hq2.
      split; assumption.
    + right.
      change ((FOeval e3 (FOVar (B+2)) = FOeval e3 x) -> False) in Hq1.
      rewrite EvB23, (Eu3 x Hx) in Hq1.
      split; [exact Hq1|].
      rewrite (FOsat_FOBexC _ (B+6) r _
                 (FOin_tm_above r (B+6) ltac:(lia))
                 (FOin_tm_above r (S (B+6)) ltac:(lia))) in Hq2.
      rewrite (Eu3 r Hr) in Hq2.
      destruct Hq2 as [rb [Hrb Hq2]].
      set (e4 := FOupdate e3 (B+6) rb) in *.
      assert (Eu4 : forall t0, FOmax_var_tm t0 < B ->
          FOeval e4 t0 = FOeval e t0).
      { intros t0 Ht0. unfold e4.
        rewrite (FOeval_upd_above t0 _ (B+6) rb ltac:(lia)).
        exact (Eu3 t0 Ht0). }
      assert (EvB44 : FOeval e4 (FOVar (B+4)) = pb).
      { unfold e4, e3. cbn. unfold FOupdate.
        rewrite E46, Nat.eqb_refl. reflexivity. }
      assert (EvB64 : FOeval e4 (FOVar (B+6)) = rb).
      { unfold e4. cbn. unfold FOupdate.
        rewrite Nat.eqb_refl. reflexivity. }
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hq2.
      destruct Hq2 as [Hlk Hq3].
      apply (proj1 (FOsat_FOlookup e4 (B+8) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral 3) x sc (FOVar (B+4))
                      (FOVar (B+6)) Htb8
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))) in Hlk.
      destruct Hlk as [j [Hj Hf]].
      rewrite (Eu4 ct Hct), (Eu4 dt Hdt), (Eu4 c1 Hc1), (Eu4 d1 Hd1),
        (Eu4 c2 Hc2), (Eu4 d2 Hd2), (Eu4 c3 Hc3), (Eu4 d3 Hd3),
        (Eu4 cr Hcr), (Eu4 dr Hdr), (Eu4 x Hx), (Eu4 sc Hsc), EvB44,
        EvB64, FOeval_numeral in Hf.
      rewrite (Eu4 len Hlen) in Hj.
      exists rb. split; [exact Hrb|].
      split; [exists j; split; [exact Hj | exact Hf]|].
      rewrite (FOsat_FOBexC _ (B+30) (FOSucc r) _
                 (FOin_tm_above (FOSucc r) (B+30) ltac:(cbn; lia))
                 (FOin_tm_above (FOSucc r) (S (B+30))
                    ltac:(cbn; lia))) in Hq3.
      assert (EbS : FOeval e4 (FOSucc r) = S (FOeval e r)).
      { change (S (FOeval e4 r) = S (FOeval e r)).
        rewrite (Eu4 r Hr). reflexivity. }
      rewrite EbS in Hq3.
      destruct Hq3 as [q [Hq Hq3]].
      set (e5 := FOupdate e4 (B+30) q) in *.
      assert (EvB25 : FOeval e5 (FOVar (B+2)) = y).
      { unfold e5, e4, e3. cbn. unfold FOupdate.
        rewrite E230, E26, E24, Nat.eqb_refl. reflexivity. }
      assert (EvB65 : FOeval e5 (FOVar (B+6)) = rb).
      { unfold e5, e4. cbn. unfold FOupdate.
        rewrite E630, Nat.eqb_refl. reflexivity. }
      assert (EvQ5 : FOeval e5 (FOVar (B+30)) = q).
      { unfold e5. cbn. unfold FOupdate.
        rewrite Nat.eqb_refl. reflexivity. }
      assert (Er5 : FOeval e5 r = FOeval e r).
      { unfold e5.
        rewrite (FOeval_upd_above r _ (B+30) q ltac:(lia)).
        exact (Eu4 r Hr). }
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hq3.
      destruct Hq3 as [Hc1' Hc2'].
      apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hc1'.
      apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hc2'.
      rewrite EvB25, EvB65, EvQ5 in Hc1'.
      rewrite FOeval_numeral, EvQ5, Er5 in Hc2'.
      exists q. split; [exact Hq|]. split; [exact Hc1' | exact Hc2'].
  - intros [p [Hp [Hcp [y [Hy [pb [Hpb [Hcp2 Hca]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above pc e B p Hpc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists y. split; [exact Hy|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb).
    assert (Eu3 : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB3 : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB23 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB43 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB3, EvB23, EvB43. exact Hcp2. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[He1 He2]|[He1 [rb [Hrb [Hlk [q [Hq [Hq1 Hq2]]]]]]]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change (FOeval e3 (FOVar (B+2)) = FOeval e3 x).
        rewrite EvB23, (Eu3 x Hx). exact He1.
      * change (FOeval e3 r = FOeval e3 pc).
        rewrite (Eu3 r Hr), (Eu3 pc Hpc). exact He2.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { change ((FOeval e3 (FOVar (B+2)) = FOeval e3 x) -> False).
        rewrite EvB23, (Eu3 x Hx). exact He1. }
      rewrite (FOsat_FOBexC _ (B+6) r _
                 (FOin_tm_above r (B+6) ltac:(lia))
                 (FOin_tm_above r (S (B+6)) ltac:(lia))).
      rewrite (Eu3 r Hr).
      exists rb. split; [exact Hrb|].
      set (e4 := FOupdate e3 (B+6) rb).
      assert (Eu4 : forall t0, FOmax_var_tm t0 < B ->
          FOeval e4 t0 = FOeval e t0).
      { intros t0 Ht0. unfold e4.
        rewrite (FOeval_upd_above t0 _ (B+6) rb ltac:(lia)).
        exact (Eu3 t0 Ht0). }
      assert (EvB44 : FOeval e4 (FOVar (B+4)) = pb).
      { unfold e4, e3. cbn. unfold FOupdate.
        rewrite E46, Nat.eqb_refl. reflexivity. }
      assert (EvB64 : FOeval e4 (FOVar (B+6)) = rb).
      { unfold e4. cbn. unfold FOupdate.
        rewrite Nat.eqb_refl. reflexivity. }
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { apply (proj2 (FOsat_FOlookup e4 (B+8) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 3) x sc (FOVar (B+4))
                        (FOVar (B+6)) Htb8
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                        ltac:(cbn; lia))).
        destruct Hlk as [j [Hj Hf]].
        exists j.
        rewrite (Eu4 len Hlen), (Eu4 ct Hct), (Eu4 dt Hdt),
          (Eu4 c1 Hc1), (Eu4 d1 Hd1), (Eu4 c2 Hc2), (Eu4 d2 Hd2),
          (Eu4 c3 Hc3), (Eu4 d3 Hd3), (Eu4 cr Hcr), (Eu4 dr Hdr),
          (Eu4 x Hx), (Eu4 sc Hsc), EvB44, EvB64, FOeval_numeral.
        split; [exact Hj | exact Hf]. }
      rewrite (FOsat_FOBexC _ (B+30) (FOSucc r) _
                 (FOin_tm_above (FOSucc r) (B+30) ltac:(cbn; lia))
                 (FOin_tm_above (FOSucc r) (S (B+30))
                    ltac:(cbn; lia))).
      assert (EbS : FOeval e4 (FOSucc r) = S (FOeval e r)).
      { change (S (FOeval e4 r) = S (FOeval e r)).
        rewrite (Eu4 r Hr). reflexivity. }
      rewrite EbS.
      exists q. split; [exact Hq|].
      set (e5 := FOupdate e4 (B+30) q).
      assert (EvB25 : FOeval e5 (FOVar (B+2)) = y).
      { unfold e5, e4, e3. cbn. unfold FOupdate.
        rewrite E230, E26, E24, Nat.eqb_refl. reflexivity. }
      assert (EvB65 : FOeval e5 (FOVar (B+6)) = rb).
      { unfold e5, e4. cbn. unfold FOupdate.
        rewrite E630, Nat.eqb_refl. reflexivity. }
      assert (EvQ5 : FOeval e5 (FOVar (B+30)) = q).
      { unfold e5. cbn. unfold FOupdate.
        rewrite Nat.eqb_refl. reflexivity. }
      assert (Er5 : FOeval e5 r = FOeval e r).
      { unfold e5.
        rewrite (FOeval_upd_above r _ (B+30) q ltac:(lia)).
        exact (Eu4 r Hr). }
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * apply (proj2 (FOsat_FOcpairF _ _ _ _)).
        rewrite EvB25, EvB65, EvQ5. exact Hq1.
      * apply (proj2 (FOsat_FOcpairF _ _ _ _)).
        rewrite FOeval_numeral, EvQ5, Er5. exact Hq2.
Qed.

Definition step3_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (x sc pc r : nat) : Prop :=
  (exists p, p < S pc /\ cpair 0 p = pc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\ cpair ta tb = p /\
      exists ra, ra < S r /\ exists rb, rb < S r /\
        L 2 x sc ta ra /\ L 2 x sc tb rb /\
        exists q, q < S r /\ cpair ra rb = q /\ cpair 0 q = r)
  \/ (cpair 1 0 = pc /\ r = pc)
  \/ (exists p, p < S pc /\ cpair 2 p = pc /\
      exists ta, ta < S p /\ exists tb, tb < S p /\ cpair ta tb = p /\
      exists ra, ra < S r /\ exists rb, rb < S r /\
        L 3 x sc ta ra /\ L 3 x sc tb rb /\
        exists q, q < S r /\ cpair ra rb = q /\ cpair 2 q = r)
  \/ (exists p, p < S pc /\ cpair 3 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\ cpair y pb = p /\
        ((y = x /\ r = pc)
         \/ (y <> x /\
             exists rb, rb < r /\ L 3 x sc pb rb /\
               exists q, q < S r /\ cpair y rb = q /\ cpair 3 q = r)))
  \/ (exists p, p < S pc /\ cpair 4 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\ cpair y pb = p /\
        ((y = x /\ r = pc)
         \/ (y <> x /\
             exists rb, rb < r /\ L 3 x sc pb rb /\
               exists q, q < S r /\ cpair y rb = q /\ cpair 4 q = r))).

Lemma FOdelta0_FOSTEP3 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP3 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc Hpc
    Hr.
  unfold FOSTEP3.
  apply FOdelta0_or; [apply FOdelta0_FOSTEP_substbin; assumption|].
  apply FOdelta0_or;
    [apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]|].
  apply FOdelta0_or; [apply FOdelta0_FOSTEP_substbin; assumption|].
  apply FOdelta0_or; apply FOdelta0_FOSTEP_substquant; assumption.
Qed.

Lemma FOsat_FOSTEP3 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP3 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r)
   <-> step3_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e x) (FOeval e sc) (FOeval e pc) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc
    Hpc Hr.
  unfold FOSTEP3, step3_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOSTEP_substbin e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 0 2 0 Htb Hx Hsc Hpc Hr).
  rewrite (FOsat_STEP_substzero_case e pc r).
  rewrite (FOsat_FOSTEP_substbin e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 2 3 2 Htb Hx Hsc Hpc Hr).
  rewrite (FOsat_FOSTEP_substquant e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 3 Htb Hx Hsc Hpc Hr).
  rewrite (FOsat_FOSTEP_substquant e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 4 Htb Hx Hsc Hpc Hr).
  reflexivity.
Qed.

Lemma FOdelta0_FOSTEP_subokbin : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP_subokbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc Hpc
    Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_subokbin.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or; apply FOdelta0_and.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOd0_eq.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOsat_FOSTEP_subokbin : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP_subokbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r)
   <-> exists p, p < S (FOeval e pc) /\
       cpair 2 p = FOeval e pc /\
       exists pa, pa < S p /\ exists pb, pb < S p /\
         cpair pa pb = p /\
         (((exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = 4 /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
              beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
              beta (FOeval e c3) (FOeval e d3) j = pa /\
              beta (FOeval e cr) (FOeval e dr) j = 0)
           /\ FOeval e r = 0)
          \/ ((exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = 4 /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
              beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
              beta (FOeval e c3) (FOeval e d3) j = pa /\
              beta (FOeval e cr) (FOeval e dr) j = 1)
           /\ (exists j, j < FOeval e len /\
              beta (FOeval e ct) (FOeval e dt) j = 4 /\
              beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
              beta (FOeval e c2) (FOeval e d2) j = FOeval e sc /\
              beta (FOeval e c3) (FOeval e d3) j = pb /\
              beta (FOeval e cr) (FOeval e dr) j = FOeval e r)))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc
    Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc pc) = S (FOeval e pc)) by reflexivity.
  unfold FOSTEP_subokbin.
  rewrite (FOsat_FOBexC e B (FOSucc pc) _
             (FOin_tm_above (FOSucc pc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc pc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above pc e B p Hpc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [pa [Hpa Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) pa)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [pb [Hpb Hin]].
    exists pa. split; [exact Hpa|].
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) pa) (B+4) pb)
      in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) pa ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = pa).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB, EvB2, EvB4 in Hcp2.
    split; [exact Hcp2|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
      destruct Hc as [Hl1 Hl2].
    + left.
      apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral 4) x sc (FOVar (B+2)) FOZero
                      Htb6
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))) in Hl1.
      destruct Hl1 as [j [Hj Hf]].
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
        (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
        (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc), EvB2,
        FOeval_numeral in Hf.
      rewrite (Eu len Hlen) in Hj.
      change (FOeval e3 FOZero) with 0 in Hf.
      split.
      * exists j. split; [exact Hj | exact Hf].
      * change (FOeval e3 r = FOeval e3 FOZero) in Hl2.
        change (FOeval e3 FOZero) with 0 in Hl2.
        rewrite (Eu r Hr) in Hl2. exact Hl2.
    + right.
      apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                      dr len (FOnumeral 4) x sc (FOVar (B+2))
                      (FOnumeral 1) Htb6
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(rewrite FOmax_var_numeral; lia))) in Hl1.
      apply (proj1 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 4) x sc (FOVar (B+4)) r
                      Htb28
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(lia)
                      ltac:(lia) ltac:(cbn; lia)
                      ltac:(lia))) in Hl2.
      destruct Hl1 as [j [Hj Hf]].
      destruct Hl2 as [j' [Hj' Hf']].
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
        (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
        (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc), EvB2,
        !FOeval_numeral in Hf.
      rewrite (Eu len Hlen) in Hj.
      rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
        (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
        (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc), (Eu r Hr),
        EvB4, FOeval_numeral in Hf'.
      rewrite (Eu len Hlen) in Hj'.
      split.
      * exists j. split; [exact Hj | exact Hf].
      * exists j'. split; [exact Hj' | exact Hf'].
  - intros [p [Hp [Hcp [pa [Hpa [pb [Hpb [Hcp2 Hca]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above pc e B p Hpc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists pa. split; [exact Hpa|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) pa)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) pa) (B+4) pb).
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) pa ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = pa).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB, EvB2, EvB4. exact Hcp2. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[Hlk Hre]|[Hlk1 Hlk2]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 4) x sc (FOVar (B+2))
                        FOZero Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                        ltac:(cbn; lia))).
        destruct Hlk as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx),
          (Eu sc Hsc), EvB2, FOeval_numeral.
        change (FOeval e3 FOZero) with 0.
        split; [exact Hj | exact Hf].
      * change (FOeval e3 r = FOeval e3 FOZero).
        change (FOeval e3 FOZero) with 0.
        rewrite (Eu r Hr). exact Hre.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 4) x sc (FOVar (B+2))
                        (FOnumeral 1) Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                        ltac:(rewrite FOmax_var_numeral; lia))).
        destruct Hlk1 as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx),
          (Eu sc Hsc), EvB2, !FOeval_numeral.
        split; [exact Hj | exact Hf].
      * apply (proj2 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 4) x sc (FOVar (B+4)) r
                        Htb28
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                        ltac:(lia))).
        destruct Hlk2 as [j [Hj Hf]].
        exists j.
        rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1),
          (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3),
          (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx),
          (Eu sc Hsc), (Eu r Hr), EvB4, FOeval_numeral.
        split; [exact Hj | exact Hf].
Qed.

Lemma FOdelta0_FOSTEP_subokquant : forall B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len x sc pc r k,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r k).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r k Htb Hx Hsc
    Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb50 : tbl_below (B+50) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEP_subokquant.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_or.
  { apply FOdelta0_and; apply FOd0_eq. }
  apply FOdelta0_and.
  { apply FOdelta0_neg. apply FOd0_eq. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [|apply FOd0_eq].
    apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_or; apply FOdelta0_and.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOd0_eq.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOsat_FOSTEP_subokquant : forall e B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len x sc pc r k,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              x sc pc r k)
   <-> exists p, p < S (FOeval e pc) /\
       cpair k p = FOeval e pc /\
       exists y, y < S p /\ exists pb, pb < S p /\
         cpair y pb = p /\
         ((y = FOeval e x /\ FOeval e r = 1)
          \/ (y <> FOeval e x /\
              (((exists j, j < FOeval e len /\
                   beta (FOeval e ct) (FOeval e dt) j = 1 /\
                   beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
                   beta (FOeval e c2) (FOeval e d2) j = pb /\
                   beta (FOeval e c3) (FOeval e d3) j = 0 /\
                   beta (FOeval e cr) (FOeval e dr) j = 0)
                /\ FOeval e r = 1)
               \/ ((exists j, j < FOeval e len /\
                   beta (FOeval e ct) (FOeval e dt) j = 1 /\
                   beta (FOeval e c1) (FOeval e d1) j = FOeval e x /\
                   beta (FOeval e c2) (FOeval e d2) j = pb /\
                   beta (FOeval e c3) (FOeval e d3) j = 0 /\
                   beta (FOeval e cr) (FOeval e dr) j = 1)
                /\ (((exists j, j < FOeval e len /\
                        beta (FOeval e ct) (FOeval e dt) j = 0 /\
                        beta (FOeval e c1) (FOeval e d1) j = y /\
                        beta (FOeval e c2) (FOeval e d2) j
                          = FOeval e sc /\
                        beta (FOeval e c3) (FOeval e d3) j = 0 /\
                        beta (FOeval e cr) (FOeval e dr) j = 1)
                     /\ FOeval e r = 0)
                    \/ ((exists j, j < FOeval e len /\
                        beta (FOeval e ct) (FOeval e dt) j = 0 /\
                        beta (FOeval e c1) (FOeval e d1) j = y /\
                        beta (FOeval e c2) (FOeval e d2) j
                          = FOeval e sc /\
                        beta (FOeval e c3) (FOeval e d3) j = 0 /\
                        beta (FOeval e cr) (FOeval e dr) j = 0)
                     /\ (exists j, j < FOeval e len /\
                        beta (FOeval e ct) (FOeval e dt) j = 4 /\
                        beta (FOeval e c1) (FOeval e d1) j
                          = FOeval e x /\
                        beta (FOeval e c2) (FOeval e d2) j
                          = FOeval e sc /\
                        beta (FOeval e c3) (FOeval e d3) j = pb /\
                        beta (FOeval e cr) (FOeval e dr) j
                          = FOeval e r)))))))).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r k Htb Hx Hsc
    Hpc Hr.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb50 : tbl_below (B+50) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (Esucc : FOeval e (FOSucc pc) = S (FOeval e pc)) by reflexivity.
  unfold FOSTEP_subokquant.
  rewrite (FOsat_FOBexC e B (FOSucc pc) _
             (FOin_tm_above (FOSucc pc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc pc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  setoid_rewrite (FOsat_FOAnd).
  split.
  - intros [p [Hp [Hcp Hin]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    rewrite FOeval_numeral, EB,
      (FOeval_upd_above pc e B p Hpc) in Hcp.
    exists p. split; [exact Hp|]. split; [exact Hcp|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1 in Hin.
    destruct Hin as [y [Hy Hin]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))) in Hin.
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2 in Hin.
    destruct Hin as [pb [Hpb Hin]].
    exists y. split; [exact Hy|].
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb)
      in *.
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hin.
    destruct Hin as [Hcp2 Hor].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    rewrite EvB, EvB2, EvB4 in Hcp2.
    split; [exact Hcp2|].
    apply (proj1 (FOsat_FOOr _ _ _)) in Hor.
    destruct Hor as [Hc|Hc];
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
      destruct Hc as [Hq1 Hq2].
    + left.
      change (FOeval e3 (FOVar (B+2)) = FOeval e3 x) in Hq1.
      change (FOeval e3 r = FOeval e3 (FOnumeral 1)) in Hq2.
      rewrite EvB2, (Eu x Hx) in Hq1.
      rewrite (Eu r Hr), FOeval_numeral in Hq2.
      split; assumption.
    + right.
      change ((FOeval e3 (FOVar (B+2)) = FOeval e3 x) -> False) in Hq1.
      rewrite EvB2, (Eu x Hx) in Hq1.
      split; [exact Hq1|].
      apply (proj1 (FOsat_FOOr _ _ _)) in Hq2.
      destruct Hq2 as [Hc|Hc];
        apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
        destruct Hc as [Hl1 Hl2].
      * left.
        apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 1) x (FOVar (B+4)) FOZero
                        FOZero Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(cbn; lia))) in Hl1.
        destruct Hl1 as [j [Hj Hf]].
        rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
          (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
          (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), EvB4,
          FOeval_numeral in Hf.
        rewrite (Eu len Hlen) in Hj.
        change (FOeval e3 FOZero) with 0 in Hf.
        change (FOeval e3 r = FOeval e3 (FOnumeral 1)) in Hl2.
        rewrite (Eu r Hr), FOeval_numeral in Hl2.
        split; [exists j; split; [exact Hj | exact Hf] | exact Hl2].
      * right.
        apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                        cr dr len (FOnumeral 1) x (FOVar (B+4)) FOZero
                        (FOnumeral 1) Htb6
                        ltac:(rewrite FOmax_var_numeral; lia)
                        ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                        ltac:(rewrite FOmax_var_numeral; lia)))
          in Hl1.
        destruct Hl1 as [j [Hj Hf]].
        rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
          (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
          (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), EvB4,
          !FOeval_numeral in Hf.
        rewrite (Eu len Hlen) in Hj.
        change (FOeval e3 FOZero) with 0 in Hf.
        split; [exists j; split; [exact Hj | exact Hf]|].
        apply (proj1 (FOsat_FOOr _ _ _)) in Hl2.
        destruct Hl2 as [Hc|Hc];
          apply (proj1 (FOsat_FOAnd _ _ _)) in Hc;
          destruct Hc as [Hm1 Hm2].
        -- left.
           apply (proj1 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3
                           d3 cr dr len (FOnumeral 0) (FOVar (B+2)) sc
                           FOZero (FOnumeral 1) Htb28
                           ltac:(rewrite FOmax_var_numeral; lia)
                           ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)
                           ltac:(rewrite FOmax_var_numeral; lia)))
             in Hm1.
           destruct Hm1 as [j' [Hj' Hf']].
           rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
             (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
             (Eu cr Hcr), (Eu dr Hdr), (Eu sc Hsc), EvB2,
             !FOeval_numeral in Hf'.
           rewrite (Eu len Hlen) in Hj'.
           change (FOeval e3 FOZero) with 0 in Hf'.
           change (FOeval e3 r = FOeval e3 FOZero) in Hm2.
           change (FOeval e3 FOZero) with 0 in Hm2.
           rewrite (Eu r Hr) in Hm2.
           split; [exists j'; split; [exact Hj' | exact Hf'] | exact Hm2].
        -- right.
           apply (proj1 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3
                           d3 cr dr len (FOnumeral 0) (FOVar (B+2)) sc
                           FOZero FOZero Htb28
                           ltac:(rewrite FOmax_var_numeral; lia)
                           ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)
                           ltac:(cbn; lia))) in Hm1.
           apply (proj1 (FOsat_FOlookup e3 (B+50) ct dt c1 d1 c2 d2 c3
                           d3 cr dr len (FOnumeral 4) x sc
                           (FOVar (B+4)) r Htb50
                           ltac:(rewrite FOmax_var_numeral; lia)
                           ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                           ltac:(lia))) in Hm2.
           destruct Hm1 as [j' [Hj' Hf']].
           destruct Hm2 as [j'' [Hj'' Hf'']].
           rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
             (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
             (Eu cr Hcr), (Eu dr Hdr), (Eu sc Hsc), EvB2,
             FOeval_numeral in Hf'.
           rewrite (Eu len Hlen) in Hj'.
           change (FOeval e3 FOZero) with 0 in Hf'.
           rewrite (Eu ct Hct), (Eu dt Hdt), (Eu c1 Hc1), (Eu d1 Hd1),
             (Eu c2 Hc2), (Eu d2 Hd2), (Eu c3 Hc3), (Eu d3 Hd3),
             (Eu cr Hcr), (Eu dr Hdr), (Eu x Hx), (Eu sc Hsc),
             (Eu r Hr), EvB4, FOeval_numeral in Hf''.
           rewrite (Eu len Hlen) in Hj''.
           split;
             [exists j'; split; [exact Hj' | exact Hf']
             |exists j''; split; [exact Hj'' | exact Hf'']].
  - intros [p [Hp [Hcp [y [Hy [pb [Hpb [Hcp2 Hca]]]]]]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|]. split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite FOeval_numeral, EB,
        (FOeval_upd_above pc e B p Hpc). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+2) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+2))
                  ltac:(cbn; lia))).
    assert (Eb1 : FOeval (FOupdate e B p) (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    rewrite Eb1.
    exists y. split; [exact Hy|].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc (FOVar B)) _
               (FOin_tm_above (FOSucc (FOVar B)) (B+4) ltac:(cbn; lia))
               (FOin_tm_above (FOSucc (FOVar B)) (S (B+4))
                  ltac:(cbn; lia))).
    assert (Eb2 : FOeval (FOupdate (FOupdate e B p) (B+2) y)
                    (FOSucc (FOVar B)) = S p)
      by (cbn; unfold FOupdate; rewrite E02, Nat.eqb_refl; reflexivity).
    rewrite Eb2.
    exists pb. split; [exact Hpb|].
    set (e3 := FOupdate (FOupdate (FOupdate e B p) (B+2) y) (B+4) pb).
    assert (Eu : forall t0, FOmax_var_tm t0 < B ->
        FOeval e3 t0 = FOeval e t0).
    { intros t0 Ht0. unfold e3.
      rewrite (FOeval_upd_above t0 _ (B+4) pb ltac:(lia)).
      rewrite (FOeval_upd_above t0 _ (B+2) y ltac:(lia)).
      exact (FOeval_upd_above t0 e B p Ht0). }
    assert (EvB : FOeval e3 (FOVar B) = p).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E04, E02, Nat.eqb_refl. reflexivity. }
    assert (EvB2 : FOeval e3 (FOVar (B+2)) = y).
    { unfold e3. cbn. unfold FOupdate.
      rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (EvB4 : FOeval e3 (FOVar (B+4)) = pb).
    { unfold e3. cbn. unfold FOupdate.
      rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      rewrite EvB, EvB2, EvB4. exact Hcp2. }
    apply (proj2 (FOsat_FOOr _ _ _)).
    destruct Hca as [[He1 He2]|[He1 Hca]].
    + left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * change (FOeval e3 (FOVar (B+2)) = FOeval e3 x).
        rewrite EvB2, (Eu x Hx). exact He1.
      * change (FOeval e3 r = FOeval e3 (FOnumeral 1)).
        rewrite (Eu r Hr), FOeval_numeral. exact He2.
    + right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { change ((FOeval e3 (FOVar (B+2)) = FOeval e3 x) -> False).
        rewrite EvB2, (Eu x Hx). exact He1. }
      apply (proj2 (FOsat_FOOr _ _ _)).
      destruct Hca as [[Hlk Hre]|[Hlk Hca]].
      * left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
        -- apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3
                           d3 cr dr len (FOnumeral 1) x (FOVar (B+4))
                           FOZero FOZero Htb6
                           ltac:(rewrite FOmax_var_numeral; lia)
                           ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                           ltac:(cbn; lia))).
           destruct Hlk as [j [Hj Hf]].
           exists j.
           rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt),
             (Eu c1 Hc1), (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2),
             (Eu c3 Hc3), (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr),
             (Eu x Hx), EvB4, FOeval_numeral.
           change (FOeval e3 FOZero) with 0.
           split; [exact Hj | exact Hf].
        -- change (FOeval e3 r = FOeval e3 (FOnumeral 1)).
           rewrite (Eu r Hr), FOeval_numeral. exact Hre.
      * right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
        { apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3
                          d3 cr dr len (FOnumeral 1) x (FOVar (B+4))
                          FOZero (FOnumeral 1) Htb6
                          ltac:(rewrite FOmax_var_numeral; lia)
                          ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                          ltac:(rewrite FOmax_var_numeral; lia))).
          destruct Hlk as [j [Hj Hf]].
          exists j.
          rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt),
            (Eu c1 Hc1), (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2),
            (Eu c3 Hc3), (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr),
            (Eu x Hx), EvB4, !FOeval_numeral.
          change (FOeval e3 FOZero) with 0.
          split; [exact Hj | exact Hf]. }
        apply (proj2 (FOsat_FOOr _ _ _)).
        destruct Hca as [[Hlk' Hre]|[Hlk' Hlk'']].
        -- left. apply (proj2 (FOsat_FOAnd _ _ _)). split.
           ++ apply (proj2 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2
                              c3 d3 cr dr len (FOnumeral 0)
                              (FOVar (B+2)) sc FOZero (FOnumeral 1)
                              Htb28
                              ltac:(rewrite FOmax_var_numeral; lia)
                              ltac:(cbn; lia) ltac:(lia)
                              ltac:(cbn; lia)
                              ltac:(rewrite FOmax_var_numeral; lia))).
              destruct Hlk' as [j [Hj Hf]].
              exists j.
              rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt),
                (Eu c1 Hc1), (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2),
                (Eu c3 Hc3), (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr),
                (Eu sc Hsc), EvB2, !FOeval_numeral.
              change (FOeval e3 FOZero) with 0.
              split; [exact Hj | exact Hf].
           ++ change (FOeval e3 r = FOeval e3 FOZero).
              change (FOeval e3 FOZero) with 0.
              rewrite (Eu r Hr). exact Hre.
        -- right. apply (proj2 (FOsat_FOAnd _ _ _)). split.
           ++ apply (proj2 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2
                              c3 d3 cr dr len (FOnumeral 0)
                              (FOVar (B+2)) sc FOZero FOZero Htb28
                              ltac:(rewrite FOmax_var_numeral; lia)
                              ltac:(cbn; lia) ltac:(lia)
                              ltac:(cbn; lia) ltac:(cbn; lia))).
              destruct Hlk' as [j [Hj Hf]].
              exists j.
              rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt),
                (Eu c1 Hc1), (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2),
                (Eu c3 Hc3), (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr),
                (Eu sc Hsc), EvB2, FOeval_numeral.
              change (FOeval e3 FOZero) with 0.
              split; [exact Hj | exact Hf].
           ++ apply (proj2 (FOsat_FOlookup e3 (B+50) ct dt c1 d1 c2 d2
                              c3 d3 cr dr len (FOnumeral 4) x sc
                              (FOVar (B+4)) r Htb50
                              ltac:(rewrite FOmax_var_numeral; lia)
                              ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                              ltac:(lia))).
              destruct Hlk'' as [j [Hj Hf]].
              exists j.
              rewrite (Eu len Hlen), (Eu ct Hct), (Eu dt Hdt),
                (Eu c1 Hc1), (Eu d1 Hd1), (Eu c2 Hc2), (Eu d2 Hd2),
                (Eu c3 Hc3), (Eu d3 Hd3), (Eu cr Hcr), (Eu dr Hdr),
                (Eu x Hx), (Eu sc Hsc), (Eu r Hr), EvB4,
                FOeval_numeral.
              split; [exact Hj | exact Hf].
Qed.

Lemma FOsat_STEP_subokatom_case : forall e B pc r,
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e
     (FOBexC B (FOSucc pc)
        (FOAnd (FOcpairF FOZero (FOVar B) pc)
           (FOEq r (FOnumeral 1))))
   <-> exists p, p < S (FOeval e pc) /\ cpair 0 p = FOeval e pc /\
       FOeval e r = 1).
Proof.
  intros e B pc r Hpc Hr.
  assert (Esucc : FOeval e (FOSucc pc) = S (FOeval e pc)) by reflexivity.
  rewrite (FOsat_FOBexC e B (FOSucc pc) _
             (FOin_tm_above (FOSucc pc) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc pc) (S B) ltac:(cbn; lia))).
  rewrite Esucc.
  split.
  - intros [p [Hp Hb]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb. destruct Hb as [Hcp Hre].
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    change (FOeval (FOupdate e B p) FOZero) with 0 in Hcp.
    rewrite EB, (FOeval_upd_above pc e B p Hpc) in Hcp.
    change (FOeval (FOupdate e B p) r
            = FOeval (FOupdate e B p) (FOnumeral 1)) in Hre.
    rewrite (FOeval_upd_above r e B p Hr), FOeval_numeral in Hre.
    exists p. split; [exact Hp|]. split; [exact Hcp | exact Hre].
  - intros [p [Hp [Hcp Hre]]].
    assert (EB : FOeval (FOupdate e B p) (FOVar B) = p)
      by (cbn; unfold FOupdate; rewrite Nat.eqb_refl; reflexivity).
    exists p. split; [exact Hp|].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    + apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      change (FOeval (FOupdate e B p) FOZero) with 0.
      rewrite EB, (FOeval_upd_above pc e B p Hpc). exact Hcp.
    + change (FOeval (FOupdate e B p) r
              = FOeval (FOupdate e B p) (FOnumeral 1)).
      rewrite (FOeval_upd_above r e B p Hr), FOeval_numeral. exact Hre.
Qed.

Lemma FOsat_STEP_subokfalse_case : forall e pc r,
  (FOsat e (FOAnd (FOcpairF (FOnumeral 1) FOZero pc)
              (FOEq r (FOnumeral 1)))
   <-> (cpair 1 0 = FOeval e pc /\ FOeval e r = 1)).
Proof.
  intros e pc r.
  rewrite (FOsat_FOAnd e _ _).
  rewrite (FOsat_FOcpairF e _ _ _).
  change (FOsat e (FOEq r (FOnumeral 1)))
    with (FOeval e r = FOeval e (FOnumeral 1)).
  change (FOeval e FOZero) with 0.
  rewrite !FOeval_numeral.
  tauto.
Qed.

Definition step4_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (x sc pc r : nat) : Prop :=
  (exists p, p < S pc /\ cpair 0 p = pc /\ r = 1)
  \/ (cpair 1 0 = pc /\ r = 1)
  \/ (exists p, p < S pc /\ cpair 2 p = pc /\
      exists pa, pa < S p /\ exists pb, pb < S p /\ cpair pa pb = p /\
        ((L 4 x sc pa 0 /\ r = 0) \/ (L 4 x sc pa 1 /\ L 4 x sc pb r)))
  \/ (exists p, p < S pc /\ cpair 3 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\ cpair y pb = p /\
        ((y = x /\ r = 1)
         \/ (y <> x /\
             ((L 1 x pb 0 0 /\ r = 1)
              \/ (L 1 x pb 0 1 /\
                  ((L 0 y sc 0 1 /\ r = 0)
                   \/ (L 0 y sc 0 0 /\ L 4 x sc pb r)))))))
  \/ (exists p, p < S pc /\ cpair 4 p = pc /\
      exists y, y < S p /\ exists pb, pb < S p /\ cpair y pb = p /\
        ((y = x /\ r = 1)
         \/ (y <> x /\
             ((L 1 x pb 0 0 /\ r = 1)
              \/ (L 1 x pb 0 1 /\
                  ((L 0 y sc 0 1 /\ r = 0)
                   \/ (L 0 y sc 0 0 /\ L 4 x sc pb r))))))).

Lemma FOdelta0_FOSTEP4 : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  FOdelta0 (FOSTEP4 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc Hpc
    Hr.
  unfold FOSTEP4.
  apply FOdelta0_or.
  { apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOdelta0_FOcpairF | apply FOd0_eq]. }
  apply FOdelta0_or; [apply FOdelta0_FOSTEP_subokbin; assumption|].
  apply FOdelta0_or; apply FOdelta0_FOSTEP_subokquant; assumption.
Qed.

Lemma FOsat_FOSTEP4 : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    x sc pc r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm x < B -> FOmax_var_tm sc < B ->
  FOmax_var_tm pc < B -> FOmax_var_tm r < B ->
  (FOsat e (FOSTEP4 B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r)
   <-> step4_sem
         (fun tg x1 x2 x3 rr => exists j, j < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j = tg /\
            beta (FOeval e c1) (FOeval e d1) j = x1 /\
            beta (FOeval e c2) (FOeval e d2) j = x2 /\
            beta (FOeval e c3) (FOeval e d3) j = x3 /\
            beta (FOeval e cr) (FOeval e dr) j = rr)
         (FOeval e x) (FOeval e sc) (FOeval e pc) (FOeval e r)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r Htb Hx Hsc
    Hpc Hr.
  unfold FOSTEP4, step4_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_STEP_subokatom_case e B pc r Hpc Hr).
  rewrite (FOsat_STEP_subokfalse_case e pc r).
  rewrite (FOsat_FOSTEP_subokbin e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r Htb Hx Hsc Hpc Hr).
  rewrite (FOsat_FOSTEP_subokquant e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 3 Htb Hx Hsc Hpc Hr).
  rewrite (FOsat_FOSTEP_subokquant e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len x sc pc r 4 Htb Hx Hsc Hpc Hr).
  reflexivity.
Qed.

Definition dispatch_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vj : nat) : Prop :=
  exists tg, tg < S vct /\ exists a1, a1 < S vc1 /\
  exists a2, a2 < S vc2 /\ exists a3, a3 < S vc3 /\
  exists rr, rr < S vcr /\
  beta vct vdt vj = tg /\ beta vc1 vd1 vj = a1 /\
  beta vc2 vd2 vj = a2 /\ beta vc3 vd3 vj = a3 /\
  beta vcr vdr vj = rr /\
  ((tg = 0 /\ step0_sem L a1 a2 rr)
   \/ (tg = 1 /\ step1_sem L a1 a2 rr)
   \/ (tg = 2 /\ step2_sem L a1 a2 a3 rr)
   \/ (tg = 3 /\ step3_sem L a1 a2 a3 rr)
   \/ (tg = 4 /\ step4_sem L a1 a2 a3 rr)
   \/ (tg = 5 /\ step5_sem L a1 rr)).

Lemma FOdelta0_FOSTEPDISPATCH : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len j,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm j < B ->
  FOdelta0 (FOSTEPDISPATCH B ct dt c1 d1 c2 d2 c3 d3 cr dr len j).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len j Htb Hj.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOSTEPDISPATCH.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and; [apply FOdelta0_FObetaF; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FObetaF; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FObetaF; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FObetaF; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FObetaF; cbn; lia|].
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP0; try assumption; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP1; try assumption; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP2; try assumption; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP3; try assumption; cbn; lia. }
  apply FOdelta0_or.
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP4; try assumption; cbn; lia. }
  { apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOSTEP5; try assumption; cbn; lia. }
Qed.

(** The step semantics are extensional in the lookup relation. *)

Lemma step0_sem_ext : forall L L' w tc r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step0_sem L w tc r <-> step0_sem L' w tc r).
Proof.
  intros L L' w tc r HL. unfold step0_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|H]]]];
    [left | right; left | right; right; left
    | right; right; right; left | right; right; right; right
    | left | right; left | right; right; left
    | right; right; right; left | right; right; right; right];
    try exact H.
  - destruct H as [tc' [H1 [H2 H3]]].
    exists tc'. split; [exact H1|]. split; [exact H2|].
    rewrite <- (HL 0 w tc' 0 r). exact H3.
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite <- (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite <- (HL 0 w ta 0 0); exact Ha
                    |rewrite <- (HL 0 w tb 0 r); exact Hb].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite <- (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite <- (HL 0 w ta 0 0); exact Ha
                    |rewrite <- (HL 0 w tb 0 r); exact Hb].
  - destruct H as [tc' [H1 [H2 H3]]].
    exists tc'. split; [exact H1|]. split; [exact H2|].
    rewrite (HL 0 w tc' 0 r). exact H3.
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite (HL 0 w ta 0 0); exact Ha
                    |rewrite (HL 0 w tb 0 r); exact Hb].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite (HL 0 w ta 0 0); exact Ha
                    |rewrite (HL 0 w tb 0 r); exact Hb].
Qed.

Lemma step1_sem_ext : forall L L' w pc r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step1_sem L w pc r <-> step1_sem L' w pc r).
Proof.
  intros L L' w pc r HL. unfold step1_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|H]]]];
    [left | right; left | right; right; left
    | right; right; right; left | right; right; right; right
    | left | right; left | right; right; left
    | right; right; right; left | right; right; right; right];
    try exact H;
    destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 H6]]]]]]]];
    exists p; (split; [exact H1|]); (split; [exact H2|]);
    exists ta; (split; [exact H3|]); exists tb; (split; [exact H4|]);
    (split; [exact H5|]).
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite <- (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite <- (HL 0 w ta 0 0); exact Ha
                    |rewrite <- (HL 0 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite <- (HL 1 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite <- (HL 1 w ta 0 0); exact Ha
                    |rewrite <- (HL 1 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; assumption.
    + right. split; [exact Ha | rewrite <- (HL 1 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; assumption.
    + right. split; [exact Ha | rewrite <- (HL 1 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite (HL 0 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite (HL 0 w ta 0 0); exact Ha
                    |rewrite (HL 0 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite (HL 1 w ta 0 1); exact Ha | exact Hb].
    + right. split; [rewrite (HL 1 w ta 0 0); exact Ha
                    |rewrite (HL 1 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; assumption.
    + right. split; [exact Ha | rewrite (HL 1 w tb 0 r); exact Hb].
  - destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; assumption.
    + right. split; [exact Ha | rewrite (HL 1 w tb 0 r); exact Hb].
Qed.

Lemma step2_sem_ext : forall L L' x sc tc r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step2_sem L x sc tc r <-> step2_sem L' x sc tc r).
Proof.
  intros L L' x sc tc r HL. unfold step2_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|H]]]];
    [left | right; left | right; right; left
    | right; right; right; left | right; right; right; right
    | left | right; left | right; right; left
    | right; right; right; left | right; right; right; right];
    try exact H.
  - destruct H as [tc' [H1 [H2 [r' [H3 [H4 H5]]]]]].
    exists tc'. split; [exact H1|]. split; [exact H2|].
    exists r'. split; [exact H3|].
    split; [rewrite <- (HL 2 x sc tc' r'); exact H4 | exact H5].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite <- (HL 2 x sc ta ra); exact H8|].
    split; [rewrite <- (HL 2 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite <- (HL 2 x sc ta ra); exact H8|].
    split; [rewrite <- (HL 2 x sc tb rb); exact H9 | exact H10].
  - destruct H as [tc' [H1 [H2 [r' [H3 [H4 H5]]]]]].
    exists tc'. split; [exact H1|]. split; [exact H2|].
    exists r'. split; [exact H3|].
    split; [rewrite (HL 2 x sc tc' r'); exact H4 | exact H5].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite (HL 2 x sc ta ra); exact H8|].
    split; [rewrite (HL 2 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite (HL 2 x sc ta ra); exact H8|].
    split; [rewrite (HL 2 x sc tb rb); exact H9 | exact H10].
Qed.

Lemma step3_sem_ext : forall L L' x sc pc r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step3_sem L x sc pc r <-> step3_sem L' x sc pc r).
Proof.
  intros L L' x sc pc r HL. unfold step3_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|H]]]];
    [left | right; left | right; right; left
    | right; right; right; left | right; right; right; right
    | left | right; left | right; right; left
    | right; right; right; left | right; right; right; right];
    try exact H.
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite <- (HL 2 x sc ta ra); exact H8|].
    split; [rewrite <- (HL 2 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite <- (HL 3 x sc ta ra); exact H8|].
    split; [rewrite <- (HL 3 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha [rb [H7 [H8 [q [H9 [H10 H11]]]]]]]].
    + left. exact H6.
    + right. split; [exact Ha|].
      exists rb. split; [exact H7|].
      split; [rewrite <- (HL 3 x sc pb rb); exact H8|].
      exists q. split; [exact H9|]. split; [exact H10 | exact H11].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha [rb [H7 [H8 [q [H9 [H10 H11]]]]]]]].
    + left. exact H6.
    + right. split; [exact Ha|].
      exists rb. split; [exact H7|].
      split; [rewrite <- (HL 3 x sc pb rb); exact H8|].
      exists q. split; [exact H9|]. split; [exact H10 | exact H11].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite (HL 2 x sc ta ra); exact H8|].
    split; [rewrite (HL 2 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [ta [H3 [tb [H4 [H5 [ra [H6 [rb [H7
      [H8 [H9 H10]]]]]]]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists ta. split; [exact H3|]. exists tb. split; [exact H4|].
    split; [exact H5|].
    exists ra. split; [exact H6|]. exists rb. split; [exact H7|].
    split; [rewrite (HL 3 x sc ta ra); exact H8|].
    split; [rewrite (HL 3 x sc tb rb); exact H9 | exact H10].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha [rb [H7 [H8 [q [H9 [H10 H11]]]]]]]].
    + left. exact H6.
    + right. split; [exact Ha|].
      exists rb. split; [exact H7|].
      split; [rewrite (HL 3 x sc pb rb); exact H8|].
      exists q. split; [exact H9|]. split; [exact H10 | exact H11].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha [rb [H7 [H8 [q [H9 [H10 H11]]]]]]]].
    + left. exact H6.
    + right. split; [exact Ha|].
      exists rb. split; [exact H7|].
      split; [rewrite (HL 3 x sc pb rb); exact H8|].
      exists q. split; [exact H9|]. split; [exact H10 | exact H11].
Qed.

Lemma step4_sem_ext : forall L L' x sc pc r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step4_sem L x sc pc r <-> step4_sem L' x sc pc r).
Proof.
  intros L L' x sc pc r HL. unfold step4_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|H]]]];
    [left | right; left | right; right; left
    | right; right; right; left | right; right; right; right
    | left | right; left | right; right; left
    | right; right; right; left | right; right; right; right];
    try exact H.
  - destruct H as [p [H1 [H2 [pa [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists pa. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite <- (HL 4 x sc pa 0); exact Ha | exact Hb].
    + right. split; [rewrite <- (HL 4 x sc pa 1); exact Ha
                    |rewrite <- (HL 4 x sc pb r); exact Hb].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha H6]]; [left; exact H6|].
    right. split; [exact Ha|].
    destruct H6 as [[Hb Hc]|[Hb H6]].
    + left. split; [rewrite <- (HL 1 x pb 0 0); exact Hb | exact Hc].
    + right. split; [rewrite <- (HL 1 x pb 0 1); exact Hb|].
      destruct H6 as [[Hd He]|[Hd He]].
      * left. split; [rewrite <- (HL 0 y sc 0 1); exact Hd | exact He].
      * right. split; [rewrite <- (HL 0 y sc 0 0); exact Hd
                      |rewrite <- (HL 4 x sc pb r); exact He].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha H6]]; [left; exact H6|].
    right. split; [exact Ha|].
    destruct H6 as [[Hb Hc]|[Hb H6]].
    + left. split; [rewrite <- (HL 1 x pb 0 0); exact Hb | exact Hc].
    + right. split; [rewrite <- (HL 1 x pb 0 1); exact Hb|].
      destruct H6 as [[Hd He]|[Hd He]].
      * left. split; [rewrite <- (HL 0 y sc 0 1); exact Hd | exact He].
      * right. split; [rewrite <- (HL 0 y sc 0 0); exact Hd
                      |rewrite <- (HL 4 x sc pb r); exact He].
  - destruct H as [p [H1 [H2 [pa [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists pa. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [[Ha Hb]|[Ha Hb]].
    + left. split; [rewrite (HL 4 x sc pa 0); exact Ha | exact Hb].
    + right. split; [rewrite (HL 4 x sc pa 1); exact Ha
                    |rewrite (HL 4 x sc pb r); exact Hb].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha H6]]; [left; exact H6|].
    right. split; [exact Ha|].
    destruct H6 as [[Hb Hc]|[Hb H6]].
    + left. split; [rewrite (HL 1 x pb 0 0); exact Hb | exact Hc].
    + right. split; [rewrite (HL 1 x pb 0 1); exact Hb|].
      destruct H6 as [[Hd He]|[Hd He]].
      * left. split; [rewrite (HL 0 y sc 0 1); exact Hd | exact He].
      * right. split; [rewrite (HL 0 y sc 0 0); exact Hd
                      |rewrite (HL 4 x sc pb r); exact He].
  - destruct H as [p [H1 [H2 [y [H3 [pb [H4 [H5 H6]]]]]]]].
    exists p. split; [exact H1|]. split; [exact H2|].
    exists y. split; [exact H3|]. exists pb. split; [exact H4|].
    split; [exact H5|].
    destruct H6 as [H6|[Ha H6]]; [left; exact H6|].
    right. split; [exact Ha|].
    destruct H6 as [[Hb Hc]|[Hb H6]].
    + left. split; [rewrite (HL 1 x pb 0 0); exact Hb | exact Hc].
    + right. split; [rewrite (HL 1 x pb 0 1); exact Hb|].
      destruct H6 as [[Hd He]|[Hd He]].
      * left. split; [rewrite (HL 0 y sc 0 1); exact Hd | exact He].
      * right. split; [rewrite (HL 0 y sc 0 0); exact Hd
                      |rewrite (HL 4 x sc pb r); exact He].
Qed.

Lemma step5_sem_ext : forall L L' a1 r,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (step5_sem L a1 r <-> step5_sem L' a1 r).
Proof.
  intros L L' a1 r HL. unfold step5_sem.
  split; intro H; destruct H as [H|H]; [left; exact H | right
                                       |left; exact H | right];
    destruct H as [k' [H1 [H2 [r' [H3 [H4 H5]]]]]];
    exists k'; (split; [exact H1|]); (split; [exact H2|]);
    exists r'; (split; [exact H3|]).
  - split; [rewrite <- (HL 5 k' 0 0 r'); exact H4 | exact H5].
  - split; [rewrite (HL 5 k' 0 0 r'); exact H4 | exact H5].
Qed.

Lemma FOsat_FOSTEPDISPATCH : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len j,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm j < B ->
  (FOsat e (FOSTEPDISPATCH B ct dt c1 d1 c2 d2 c3 d3 cr dr len j)
   <-> dispatch_sem
         (fun tg x1 x2 x3 rr => exists j', j' < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j' = tg /\
            beta (FOeval e c1) (FOeval e d1) j' = x1 /\
            beta (FOeval e c2) (FOeval e d2) j' = x2 /\
            beta (FOeval e c3) (FOeval e d3) j' = x3 /\
            beta (FOeval e cr) (FOeval e dr) j' = rr)
         (FOeval e ct) (FOeval e dt) (FOeval e c1) (FOeval e d1)
         (FOeval e c2) (FOeval e d2) (FOeval e c3) (FOeval e d3)
         (FOeval e cr) (FOeval e dr) (FOeval e j)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len j Htb Hj.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (E02 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (E04 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E06 : Nat.eqb B (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E08 : Nat.eqb B (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E26 : Nat.eqb (B+2) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E28 : Nat.eqb (B+2) (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E46 : Nat.eqb (B+4) (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E48 : Nat.eqb (B+4) (B+8) = false) by (apply Nat.eqb_neq; lia).
  assert (E68 : Nat.eqb (B+6) (B+8) = false) by (apply Nat.eqb_neq; lia).
  unfold FOSTEPDISPATCH, dispatch_sem.
  rewrite (FOsat_FOBexC e B (FOSucc ct) _
             (FOin_tm_above (FOSucc ct) B ltac:(cbn; lia))
             (FOin_tm_above (FOSucc ct) (S B) ltac:(cbn; lia))).
  assert (Es0 : FOeval e (FOSucc ct) = S (FOeval e ct)) by reflexivity.
  rewrite Es0.
  apply Morphisms_Prop.ex_iff_morphism. intro tg.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  set (e1 := FOupdate e B tg).
  assert (Eu1 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e1 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e1. exact (FOeval_upd_above t0 e B tg Ht0). }
  rewrite (FOsat_FOBexC e1 (B+2) (FOSucc c1) _
             (FOin_tm_above (FOSucc c1) (B+2) ltac:(cbn; lia))
             (FOin_tm_above (FOSucc c1) (S (B+2)) ltac:(cbn; lia))).
  assert (Es1 : FOeval e1 (FOSucc c1) = S (FOeval e c1)).
  { change (S (FOeval e1 c1) = S (FOeval e c1)).
    rewrite (Eu1 c1 Hc1). reflexivity. }
  rewrite Es1.
  apply Morphisms_Prop.ex_iff_morphism. intro a1.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  set (e2 := FOupdate e1 (B+2) a1).
  assert (Eu2 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e2 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e2.
    rewrite (FOeval_upd_above t0 _ (B+2) a1 ltac:(lia)).
    exact (Eu1 t0 Ht0). }
  rewrite (FOsat_FOBexC e2 (B+4) (FOSucc c2) _
             (FOin_tm_above (FOSucc c2) (B+4) ltac:(cbn; lia))
             (FOin_tm_above (FOSucc c2) (S (B+4)) ltac:(cbn; lia))).
  assert (Es2 : FOeval e2 (FOSucc c2) = S (FOeval e c2)).
  { change (S (FOeval e2 c2) = S (FOeval e c2)).
    rewrite (Eu2 c2 Hc2). reflexivity. }
  rewrite Es2.
  apply Morphisms_Prop.ex_iff_morphism. intro a2.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  set (e3 := FOupdate e2 (B+4) a2).
  assert (Eu3 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e3 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e3.
    rewrite (FOeval_upd_above t0 _ (B+4) a2 ltac:(lia)).
    exact (Eu2 t0 Ht0). }
  rewrite (FOsat_FOBexC e3 (B+6) (FOSucc c3) _
             (FOin_tm_above (FOSucc c3) (B+6) ltac:(cbn; lia))
             (FOin_tm_above (FOSucc c3) (S (B+6)) ltac:(cbn; lia))).
  assert (Es3 : FOeval e3 (FOSucc c3) = S (FOeval e c3)).
  { change (S (FOeval e3 c3) = S (FOeval e c3)).
    rewrite (Eu3 c3 Hc3). reflexivity. }
  rewrite Es3.
  apply Morphisms_Prop.ex_iff_morphism. intro a3.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  set (e4 := FOupdate e3 (B+6) a3).
  assert (Eu4 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e4 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e4.
    rewrite (FOeval_upd_above t0 _ (B+6) a3 ltac:(lia)).
    exact (Eu3 t0 Ht0). }
  rewrite (FOsat_FOBexC e4 (B+8) (FOSucc cr) _
             (FOin_tm_above (FOSucc cr) (B+8) ltac:(cbn; lia))
             (FOin_tm_above (FOSucc cr) (S (B+8)) ltac:(cbn; lia))).
  assert (Es4 : FOeval e4 (FOSucc cr) = S (FOeval e cr)).
  { change (S (FOeval e4 cr) = S (FOeval e cr)).
    rewrite (Eu4 cr Hcr). reflexivity. }
  rewrite Es4.
  apply Morphisms_Prop.ex_iff_morphism. intro rr.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  set (e5 := FOupdate e4 (B+8) rr).
  assert (Eu5 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e5 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e5.
    rewrite (FOeval_upd_above t0 _ (B+8) rr ltac:(lia)).
    exact (Eu4 t0 Ht0). }
  assert (EvB : FOeval e5 (FOVar B) = tg).
  { unfold e5, e4, e3, e2, e1. cbn. unfold FOupdate.
    rewrite E08, E06, E04, E02, Nat.eqb_refl. reflexivity. }
  assert (EvB2 : FOeval e5 (FOVar (B+2)) = a1).
  { unfold e5, e4, e3, e2. cbn. unfold FOupdate.
    rewrite E28, E26, E24, Nat.eqb_refl. reflexivity. }
  assert (EvB4 : FOeval e5 (FOVar (B+4)) = a2).
  { unfold e5, e4, e3. cbn. unfold FOupdate.
    rewrite E48, E46, Nat.eqb_refl. reflexivity. }
  assert (EvB6 : FOeval e5 (FOVar (B+6)) = a3).
  { unfold e5, e4. cbn. unfold FOupdate.
    rewrite E68, Nat.eqb_refl. reflexivity. }
  assert (EvB8 : FOeval e5 (FOVar (B+8)) = rr).
  { unfold e5. cbn. unfold FOupdate.
    rewrite Nat.eqb_refl. reflexivity. }
  rewrite (FOsat_FOAnd e5 _ _).
  rewrite (FOsat_FObetaF e5 (B+10) ct dt j (FOVar B)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)).
  rewrite (Eu5 ct Hct), (Eu5 dt Hdt), (Eu5 j Hj), EvB.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  rewrite (FOsat_FOAnd e5 _ _).
  rewrite (FOsat_FObetaF e5 (B+14) c1 d1 j (FOVar (B+2))
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)).
  rewrite (Eu5 c1 Hc1), (Eu5 d1 Hd1), (Eu5 j Hj), EvB2.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  rewrite (FOsat_FOAnd e5 _ _).
  rewrite (FOsat_FObetaF e5 (B+18) c2 d2 j (FOVar (B+4))
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)).
  rewrite (Eu5 c2 Hc2), (Eu5 d2 Hd2), (Eu5 j Hj), EvB4.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  rewrite (FOsat_FOAnd e5 _ _).
  rewrite (FOsat_FObetaF e5 (B+22) c3 d3 j (FOVar (B+6))
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)).
  rewrite (Eu5 c3 Hc3), (Eu5 d3 Hd3), (Eu5 j Hj), EvB6.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  rewrite (FOsat_FOAnd e5 _ _).
  rewrite (FOsat_FObetaF e5 (B+26) cr dr j (FOVar (B+8))
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)).
  rewrite (Eu5 cr Hcr), (Eu5 dr Hdr), (Eu5 j Hj), EvB8.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  rewrite (FOsat_FOOr e5 _ _).
  apply Morphisms_Prop.or_iff_morphism.
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) FOZero))
      with (FOeval e5 (FOVar B) = FOeval e5 FOZero).
    change (FOeval e5 FOZero) with 0.
    rewrite EvB.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP0 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+8)) Htb30
               ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)).
    rewrite EvB2, EvB4, EvB8.
    apply step0_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
  rewrite (FOsat_FOOr e5 _ _).
  apply Morphisms_Prop.or_iff_morphism.
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) (FOnumeral 1)))
      with (FOeval e5 (FOVar B) = FOeval e5 (FOnumeral 1)).
    rewrite EvB, FOeval_numeral.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP1 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+8)) Htb30
               ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)).
    rewrite EvB2, EvB4, EvB8.
    apply step1_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
  rewrite (FOsat_FOOr e5 _ _).
  apply Morphisms_Prop.or_iff_morphism.
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) (FOnumeral 2)))
      with (FOeval e5 (FOVar B) = FOeval e5 (FOnumeral 2)).
    rewrite EvB, FOeval_numeral.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP2 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6)) (FOVar (B+8))
               Htb30 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
               ltac:(cbn; lia)).
    rewrite EvB2, EvB4, EvB6, EvB8.
    apply step2_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
  rewrite (FOsat_FOOr e5 _ _).
  apply Morphisms_Prop.or_iff_morphism.
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) (FOnumeral 3)))
      with (FOeval e5 (FOVar B) = FOeval e5 (FOnumeral 3)).
    rewrite EvB, FOeval_numeral.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP3 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6)) (FOVar (B+8))
               Htb30 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
               ltac:(cbn; lia)).
    rewrite EvB2, EvB4, EvB6, EvB8.
    apply step3_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
  rewrite (FOsat_FOOr e5 _ _).
  apply Morphisms_Prop.or_iff_morphism.
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) (FOnumeral 4)))
      with (FOeval e5 (FOVar B) = FOeval e5 (FOnumeral 4)).
    rewrite EvB, FOeval_numeral.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP4 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6)) (FOVar (B+8))
               Htb30 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
               ltac:(cbn; lia)).
    rewrite EvB2, EvB4, EvB6, EvB8.
    apply step4_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
  { rewrite (FOsat_FOAnd e5 _ _).
    change (FOsat e5 (FOEq (FOVar B) (FOnumeral 5)))
      with (FOeval e5 (FOVar B) = FOeval e5 (FOnumeral 5)).
    rewrite EvB, FOeval_numeral.
    apply Morphisms_Prop.and_iff_morphism; [tauto|].
    rewrite (FOsat_FOSTEP5 e5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+8)) Htb30
               ltac:(cbn; lia) ltac:(cbn; lia)).
    rewrite EvB2, EvB8.
    apply step5_sem_ext.
    intros a b c d f.
    setoid_rewrite (Eu5 len Hlen).
    setoid_rewrite (Eu5 ct Hct). setoid_rewrite (Eu5 dt Hdt).
    setoid_rewrite (Eu5 c1 Hc1). setoid_rewrite (Eu5 d1 Hd1).
    setoid_rewrite (Eu5 c2 Hc2). setoid_rewrite (Eu5 d2 Hd2).
    setoid_rewrite (Eu5 c3 Hc3). setoid_rewrite (Eu5 d3 Hd3).
    setoid_rewrite (Eu5 cr Hcr). setoid_rewrite (Eu5 dr Hdr).
    reflexivity. }
Qed.

Lemma dispatch_sem_ext : forall L L' vct vdt vc1 vd1 vc2 vd2 vc3 vd3
    vcr vdr vj,
  (forall a b c d f, L a b c d f <-> L' a b c d f) ->
  (dispatch_sem L vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vj
   <-> dispatch_sem L' vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vj).
Proof.
  intros L L' vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vj HL.
  unfold dispatch_sem.
  apply Morphisms_Prop.ex_iff_morphism. intro tg.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.ex_iff_morphism. intro a1.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.ex_iff_morphism. intro a2.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.ex_iff_morphism. intro a3.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.ex_iff_morphism. intro rr.
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.and_iff_morphism; [tauto|].
  apply Morphisms_Prop.or_iff_morphism.
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step0_sem_ext. exact HL. }
  apply Morphisms_Prop.or_iff_morphism.
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step1_sem_ext. exact HL. }
  apply Morphisms_Prop.or_iff_morphism.
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step2_sem_ext. exact HL. }
  apply Morphisms_Prop.or_iff_morphism.
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step3_sem_ext. exact HL. }
  apply Morphisms_Prop.or_iff_morphism.
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step4_sem_ext. exact HL. }
  { apply Morphisms_Prop.and_iff_morphism; [tauto|].
    apply step5_sem_ext. exact HL. }
Qed.

Lemma FOdelta0_FOTBLVALID : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOdelta0 (FOTBLVALID B ct dt c1 d1 c2 d2 c3 d3 cr dr len).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len Htb.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOTBLVALID.
  apply FOdelta0_FOBallC;
    [apply FOin_tm_above; lia | apply FOin_tm_above; lia |].
  apply FOdelta0_FOSTEPDISPATCH; [exact Htb2 | cbn; lia].
Qed.

(** ** The derivation checker is Delta_0; the matrix is Sigma_1. *)

Lemma FOdelta0_FOGUARDC : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B -> FOmax_var_tm i < B ->
  FOdelta0 (FOGUARDC B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i Htb Hcs Hds Hi.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOGUARDC.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia | apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and.
  - apply FOdelta0_FObetaF; cbn; lia.
  - apply FOdelta0_FOBexC;
      [apply FOin_tm_above; cbn; lia
      |apply FOin_tm_above; cbn; lia |].
    apply FOdelta0_FOlookup;
      [unfold tbl_below; repeat split; lia
      |cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia].
Qed.

Lemma FOdelta0_FOPRDER : forall cores, FOdelta0 (FOPRDER cores).
Proof.
  intro cores. unfold FOPRDER.
  apply FOdelta0_and.
  { apply FOdelta0_FOTBLVALID.
    unfold tbl_below; repeat split; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOBexC; [reflexivity | reflexivity |].
    apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOBallC; [reflexivity | reflexivity |].
    apply FOdelta0_FOJUSTCK;
      [unfold tbl_below; repeat split; cbn; lia
      |cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia]. }
  { apply FOdelta0_FOBallC; [reflexivity | reflexivity |].
    apply FOdelta0_FOGUARDC;
      [unfold tbl_below; repeat split; cbn; lia
      |cbn; lia | cbn; lia | cbn; lia]. }
Qed.

Lemma FOsigma1_FOPRMAT : forall cores, FOsigma1 (FOPRMAT cores).
Proof.
  intro cores. unfold FOPRMAT.
  do 16 apply FOs1_ex.
  apply FOs1_d0. apply FOdelta0_FOPRDER.
Qed.

Lemma FOsigma1_FOProvSentence : forall n A,
  FOsigma1 (FOProvSentence n A).
Proof.
  intros n A. unfold FOProvSentence.
  apply FOsigma1_subst_num. apply FOsigma1_subst_num.
  apply FOsigma1_FOPRMAT.
Qed.

Lemma FOsat_FOTBLVALID : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  (FOsat e (FOTBLVALID B ct dt c1 d1 c2 d2 c3 d3 cr dr len)
   <-> forall vj, vj < FOeval e len ->
       dispatch_sem
         (fun tg x1 x2 x3 rr => exists j', j' < FOeval e len /\
            beta (FOeval e ct) (FOeval e dt) j' = tg /\
            beta (FOeval e c1) (FOeval e d1) j' = x1 /\
            beta (FOeval e c2) (FOeval e d2) j' = x2 /\
            beta (FOeval e c3) (FOeval e d3) j' = x3 /\
            beta (FOeval e cr) (FOeval e dr) j' = rr)
         (FOeval e ct) (FOeval e dt) (FOeval e c1) (FOeval e d1)
         (FOeval e c2) (FOeval e d2) (FOeval e c3) (FOeval e d3)
         (FOeval e cr) (FOeval e dr) vj).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len Htb.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOTBLVALID.
  rewrite (FOsat_FOBallC e B len _
             (FOin_tm_above len B ltac:(lia))
             (FOin_tm_above len (S B) ltac:(lia))).
  apply Morphisms_Prop.all_iff_morphism. intro vj.
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; [tauto|].
  set (e1 := FOupdate e B vj).
  assert (Eu1 : forall t0, FOmax_var_tm t0 < B ->
      FOeval e1 t0 = FOeval e t0).
  { intros t0 Ht0. unfold e1. exact (FOeval_upd_above t0 e B vj Ht0). }
  assert (EvB : FOeval e1 (FOVar B) = vj).
  { unfold e1. cbn. unfold FOupdate.
    rewrite Nat.eqb_refl. reflexivity. }
  rewrite (FOsat_FOSTEPDISPATCH e1 (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr
             len (FOVar B) Htb2 ltac:(cbn; lia)).
  rewrite (Eu1 ct Hct), (Eu1 dt Hdt), (Eu1 c1 Hc1), (Eu1 d1 Hd1),
    (Eu1 c2 Hc2), (Eu1 d2 Hd2), (Eu1 c3 Hc3), (Eu1 d3 Hd3),
    (Eu1 cr Hcr), (Eu1 dr Hdr), EvB.
  apply dispatch_sem_ext.
  intros a b c d f.
  setoid_rewrite (Eu1 len Hlen).
  reflexivity.
Qed.

(** ** Decode equations on paired codes. *)

Lemma cunpair_bound : forall n,
  fst (cunpair n) + snd (cunpair n) <= n.
Proof.
  intro n. pose proof (cpair_cunpair n) as H.
  pose proof (cpair_bound (fst (cunpair n)) (snd (cunpair n))) as Hb.
  lia.
Qed.

Lemma FOdecode_tm_b_stable : forall c d d',
  c < d -> c < d' ->
  FOdecode_tm_b d c = FOdecode_tm_b d' c.
Proof.
  intro c. induction c as [c IH] using lt_wf_ind. intros d d' Hd Hd'.
  destruct d as [|d]; [lia|]. destruct d' as [|d']; [lia|].
  cbn [FOdecode_tm_b].
  pose proof (cunpair_bound c) as Hcb.
  pose proof (cunpair_bound (snd (cunpair c))) as Hpb.
  destruct (fst (cunpair c)) as [|[|[|[|[|t5]]]]] eqn:Etag.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH; lia.
  - f_equal; apply IH; lia.
  - f_equal; apply IH; lia.
  - reflexivity.
Qed.

Lemma FOdecode_tm_var : forall y, FOdecode_tm (cpair 0 y) = FOVar y.
Proof.
  intro y. unfold FOdecode_tm. cbn [FOdecode_tm_b].
  rewrite cunpair_cpair. reflexivity.
Qed.

Lemma FOdecode_tm_zero : forall z, FOdecode_tm (cpair 1 z) = FOZero.
Proof.
  intro z. unfold FOdecode_tm. cbn [FOdecode_tm_b].
  rewrite cunpair_cpair. reflexivity.
Qed.

Lemma FOdecode_tm_succ : forall p,
  FOdecode_tm (cpair 2 p) = FOSucc (FOdecode_tm p).
Proof.
  intro p. unfold FOdecode_tm at 1. cbn [FOdecode_tm_b].
  rewrite cunpair_cpair. cbn [fst snd].
  f_equal. unfold FOdecode_tm.
  apply FOdecode_tm_b_stable.
  - pose proof (cpair_bound 2 p). lia.
  - lia.
Qed.

Lemma FOdecode_tm_b_plus_step : forall d a b,
  FOdecode_tm_b (S d) (cpair 3 (cpair a b))
  = FOPlus (FOdecode_tm_b d a) (FOdecode_tm_b d b).
Proof.
  intros d a b. cbn [FOdecode_tm_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma FOdecode_tm_plus : forall a b,
  FOdecode_tm (cpair 3 (cpair a b))
  = FOPlus (FOdecode_tm a) (FOdecode_tm b).
Proof.
  intros a b. unfold FOdecode_tm.
  rewrite FOdecode_tm_b_plus_step.
  pose proof (cpair_bound 3 (cpair a b)).
  pose proof (cpair_bound a b).
  f_equal; apply FOdecode_tm_b_stable; lia.
Qed.

Lemma FOdecode_tm_b_mult_step : forall d a b,
  FOdecode_tm_b (S d) (cpair 4 (cpair a b))
  = FOMult (FOdecode_tm_b d a) (FOdecode_tm_b d b).
Proof.
  intros d a b. cbn [FOdecode_tm_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma FOdecode_tm_mult : forall a b,
  FOdecode_tm (cpair 4 (cpair a b))
  = FOMult (FOdecode_tm a) (FOdecode_tm b).
Proof.
  intros a b. unfold FOdecode_tm.
  rewrite FOdecode_tm_b_mult_step.
  pose proof (cpair_bound 4 (cpair a b)).
  pose proof (cpair_bound a b).
  f_equal; apply FOdecode_tm_b_stable; lia.
Qed.

Lemma FOdecode_f_b_stable : forall c d d',
  c < d -> c < d' ->
  FOdecode_f_b d c = FOdecode_f_b d' c.
Proof.
  intro c. induction c as [c IH] using lt_wf_ind. intros d d' Hd Hd'.
  destruct d as [|d]; [lia|]. destruct d' as [|d']; [lia|].
  cbn [FOdecode_f_b].
  pose proof (cunpair_bound c) as Hcb.
  pose proof (cunpair_bound (snd (cunpair c))) as Hpb.
  destruct (fst (cunpair c)) as [|[|[|[|[|t5]]]]] eqn:Etag.
  - reflexivity.
  - reflexivity.
  - f_equal; apply IH; lia.
  - f_equal; apply IH; lia.
  - f_equal; apply IH; lia.
  - reflexivity.
Qed.

Lemma FOdecode_f_eq : forall a b,
  FOdecode_f (cpair 0 (cpair a b))
  = FOEq (FOdecode_tm a) (FOdecode_tm b).
Proof.
  intros a b. unfold FOdecode_f. cbn [FOdecode_f_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. reflexivity.
Qed.

Lemma FOdecode_f_false : forall z, FOdecode_f (cpair 1 z) = FOFalseF.
Proof.
  intro z. unfold FOdecode_f. cbn [FOdecode_f_b].
  rewrite cunpair_cpair. reflexivity.
Qed.

Lemma FOdecode_f_b_impl_step : forall d a b,
  FOdecode_f_b (S d) (cpair 2 (cpair a b))
  = FOImplF (FOdecode_f_b d a) (FOdecode_f_b d b).
Proof.
  intros d a b. cbn [FOdecode_f_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma FOdecode_f_impl : forall a b,
  FOdecode_f (cpair 2 (cpair a b))
  = FOImplF (FOdecode_f a) (FOdecode_f b).
Proof.
  intros a b. unfold FOdecode_f.
  rewrite FOdecode_f_b_impl_step.
  pose proof (cpair_bound 2 (cpair a b)).
  pose proof (cpair_bound a b).
  f_equal; apply FOdecode_f_b_stable; lia.
Qed.

Lemma FOdecode_f_b_forall_step : forall d y b,
  FOdecode_f_b (S d) (cpair 3 (cpair y b))
  = FOForall y (FOdecode_f_b d b).
Proof.
  intros d y b. cbn [FOdecode_f_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma FOdecode_f_forall : forall y b,
  FOdecode_f (cpair 3 (cpair y b)) = FOForall y (FOdecode_f b).
Proof.
  intros y b. unfold FOdecode_f.
  rewrite FOdecode_f_b_forall_step.
  pose proof (cpair_bound 3 (cpair y b)).
  pose proof (cpair_bound y b).
  f_equal. apply FOdecode_f_b_stable; lia.
Qed.

Lemma FOdecode_f_b_exists_step : forall d y b,
  FOdecode_f_b (S d) (cpair 4 (cpair y b))
  = FOExists y (FOdecode_f_b d b).
Proof.
  intros d y b. cbn [FOdecode_f_b].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma FOdecode_f_exists : forall y b,
  FOdecode_f (cpair 4 (cpair y b)) = FOExists y (FOdecode_f b).
Proof.
  intros y b. unfold FOdecode_f.
  rewrite FOdecode_f_b_exists_step.
  pose proof (cpair_bound 4 (cpair y b)).
  pose proof (cpair_bound y b).
  f_equal. apply FOdecode_f_b_stable; lia.
Qed.

Lemma cpair_inj : forall a b c d,
  cpair a b = cpair c d -> a = c /\ b = d.
Proof.
  intros a b c d H.
  pose proof (cunpair_cpair a b) as Ha.
  pose proof (cunpair_cpair c d) as Hc.
  rewrite H in Ha. rewrite Hc in Ha.
  injection Ha. intros. split; congruence.
Qed.

(** The per-tag specification a sound table entry meets: at genuine
    codes, the result is the represented function's value. *)

Definition mspec (tg a1 a2 a3 r : nat) : Prop :=
  match tg with
  | 0 => forall t, a2 = FOcode_tm t ->
         r = (if FOin_tm a1 t then 1 else 0)
  | 1 => forall A, a2 = FOcode_f A ->
         r = (if FOfree_in a1 A then 1 else 0)
  | 2 => forall s t, a2 = FOcode_tm s -> a3 = FOcode_tm t ->
         r = FOcode_tm (FOsubst_t a1 s t)
  | 3 => forall s A, a2 = FOcode_tm s -> a3 = FOcode_f A ->
         r = FOcode_f (FOsubst_f a1 s A)
  | 4 => forall s A, a2 = FOcode_tm s -> a3 = FOcode_f A ->
         r = (if FOsubst_ok a1 s A then 1 else 0)
  | 5 => r = FOcode_tm (FOnumeral a1)
  | _ => True
  end.

Definition tblL (vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen : nat)
    : nat -> nat -> nat -> nat -> nat -> Prop :=
  fun tg a1 a2 a3 r => exists j, j < vlen /\
    beta vct vdt j = tg /\ beta vc1 vd1 j = a1 /\
    beta vc2 vd2 j = a2 /\ beta vc3 vd3 j = a3 /\
    beta vcr vdr j = r.

Definition mw (tg : nat) : nat :=
  match tg with
  | 1 => 1
  | 3 => 1
  | 4 => 1
  | _ => 0
  end.

Ltac mlia :=
  repeat match goal with
         | H : context[mw _] |- _ => cbn [mw] in H
         end;
  cbn [mw]; lia.

Theorem tbl_sound : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
    vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall tg a1 a2 a3 r,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen tg a1 a2 a3 r ->
    mspec tg a1 a2 a3 r.
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid.
  assert (MAIN : forall m tg a1 a2 a3 r,
      a1 + a2 + a3 + mw tg < m ->
      tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen tg a1 a2 a3 r ->
      mspec tg a1 a2 a3 r).
  { induction m as [|m IHm].
    { intros; lia. }
    intros tg a1 a2 a3 r Hm Hmem.
    destruct Hmem as [j [Hj Hf]].
    pose proof (Hvalid j Hj) as Hd.
    unfold dispatch_sem in Hd.
    destruct Hd as [tg' [Htgb [a1' [Ha1b [a2' [Ha2b [a3' [Ha3b [rr'
      [Hrrb [Hbt [Hb1 [Hb2 [Hb3 [Hbr Hsw]]]]]]]]]]]]]]].
    destruct Hf as [Hft [Hf1 [Hf2 [Hf3 Hfr]]]].
    assert (Etg : tg' = tg) by congruence.
    assert (Ea1 : a1' = a1) by congruence.
    assert (Ea2 : a2' = a2) by congruence.
    assert (Ea3 : a3' = a3) by congruence.
    assert (Err : rr' = r) by congruence.
    clear Hbt Hb1 Hb2 Hb3 Hbr Hft Hf1 Hf2 Hf3 Hfr Htgb Ha1b Ha2b Ha3b
      Hrrb Hj.
    subst tg' a1' a2' a3' rr'.
    destruct Hsw as [[-> Hst]|[[-> Hst]|[[-> Hst]|[[-> Hst]|[[-> Hst]
      |[-> Hst]]]]]].
    - (* occurrence *)
      cbn [mspec]. intros t Ht2.
      unfold step0_sem in Hst.
      destruct Hst as [C|[C|[C|[C|C]]]].
      + destruct C as [y [Hyb [Hcp Hca]]].
        rewrite Ht2 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        subst v0.
        cbn [FOin_tm].
        destruct Hca as [[-> ->]|[Hne ->]].
        * rewrite Nat.eqb_refl. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne). reflexivity.
      + destruct C as [Hcp ->].
        rewrite Ht2 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 _];
          try discriminate Hcp1.
        reflexivity.
      + destruct C as [tc' [Htcb [Hcp HL]]].
        rewrite Ht2 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        assert (Hbnd : 2 + tc' <= a2).
        { rewrite Ht2. cbn [FOcode_tm]. rewrite Hcp2.
          apply cpair_bound. }
        pose proof (IHm 0 a1 tc' 0 r ltac:(mlia) HL) as IH1.
        cbn [mspec] in IH1.
        specialize (IH1 t' Hcp2).
        cbn [FOin_tm]. exact IH1.
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp Hca]]]]]]]].
        rewrite Ht2 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb < a2).
        { rewrite Ht2. cbn [FOcode_tm]. rewrite Hta, Htb.
          pose proof (cpair_bound 3
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        cbn [FOin_tm].
        destruct Hca as [[HL ->]|[HL0 HLr]].
        * pose proof (IHm 0 a1 ta 0 1 ltac:(mlia) HL) as IH1.
          cbn [mspec] in IH1.
          specialize (IH1 t1 Hta).
          destruct (FOin_tm a1 t1) eqn:E1; [|discriminate IH1].
          reflexivity.
        * pose proof (IHm 0 a1 ta 0 0 ltac:(mlia) HL0) as IH0.
          pose proof (IHm 0 a1 tb 0 r ltac:(mlia) HLr) as IHr.
          cbn [mspec] in IH0, IHr.
          specialize (IH0 t1 Hta). specialize (IHr t2 Htb).
          destruct (FOin_tm a1 t1) eqn:E1; [discriminate IH0|].
          exact IHr.
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp Hca]]]]]]]].
        rewrite Ht2 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb < a2).
        { rewrite Ht2. cbn [FOcode_tm]. rewrite Hta, Htb.
          pose proof (cpair_bound 4
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        cbn [FOin_tm].
        destruct Hca as [[HL ->]|[HL0 HLr]].
        * pose proof (IHm 0 a1 ta 0 1 ltac:(mlia) HL) as IH1.
          cbn [mspec] in IH1.
          specialize (IH1 t1 Hta).
          destruct (FOin_tm a1 t1) eqn:E1; [|discriminate IH1].
          reflexivity.
        * pose proof (IHm 0 a1 ta 0 0 ltac:(mlia) HL0) as IH0.
          pose proof (IHm 0 a1 tb 0 r ltac:(mlia) HLr) as IHr.
          cbn [mspec] in IH0, IHr.
          specialize (IH0 t1 Hta). specialize (IHr t2 Htb).
          destruct (FOin_tm a1 t1) eqn:E1; [discriminate IH0|].
          exact IHr.
    - (* free occurrence *)
      cbn [mspec]. intros A HA2.
      unfold step1_sem in Hst.
      destruct Hst as [C|[C|[C|[C|C]]]].
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp Hca]]]]]]]].
        rewrite HA2 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb <= a2).
        { rewrite HA2. cbn [FOcode_f]. rewrite Hta, Htb.
          pose proof (cpair_bound 0
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        cbn [FOfree_in].
        destruct Hca as [[HL ->]|[HL0 HLr]].
        * pose proof (IHm 0 a1 ta 0 1 ltac:(mlia) HL) as IH1.
          cbn [mspec] in IH1.
          specialize (IH1 t1 Hta).
          destruct (FOin_tm a1 t1) eqn:E1; [|discriminate IH1].
          reflexivity.
        * pose proof (IHm 0 a1 ta 0 0 ltac:(mlia) HL0) as IH0.
          pose proof (IHm 0 a1 tb 0 r ltac:(mlia) HLr) as IHr.
          cbn [mspec] in IH0, IHr.
          specialize (IH0 t1 Hta). specialize (IHr t2 Htb).
          destruct (FOin_tm a1 t1) eqn:E1; [discriminate IH0|].
          exact IHr.
      + destruct C as [Hcp ->].
        rewrite HA2 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 _]; try discriminate Hcp1.
        reflexivity.
      + destruct C as [p [Hpb [Hcp [pa [Hpab [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA2 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hpa Hpb'].
        assert (Hba : pa + pb < a2).
        { rewrite HA2. cbn [FOcode_f]. rewrite Hpa, Hpb'.
          pose proof (cpair_bound 2
            (cpair (FOcode_f A1) (FOcode_f A2))).
          pose proof (cpair_bound (FOcode_f A1) (FOcode_f A2)).
          lia. }
        cbn [FOfree_in].
        destruct Hca as [[HL ->]|[HL0 HLr]].
        * pose proof (IHm 1 a1 pa 0 1 ltac:(mlia) HL) as IH1.
          cbn [mspec] in IH1.
          specialize (IH1 A1 Hpa).
          destruct (FOfree_in a1 A1) eqn:E1; [|discriminate IH1].
          reflexivity.
        * pose proof (IHm 1 a1 pa 0 0 ltac:(mlia) HL0) as IH0.
          pose proof (IHm 1 a1 pb 0 r ltac:(mlia) HLr) as IHr.
          cbn [mspec] in IH0, IHr.
          specialize (IH0 A1 Hpa). specialize (IHr A2 Hpb').
          destruct (FOfree_in a1 A1) eqn:E1; [discriminate IH0|].
          exact IHr.
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA2 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : pb < a2).
        { rewrite HA2. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 3 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOfree_in].
        destruct Hca as [[-> ->]|[Hne HL]].
        * rewrite Nat.eqb_refl. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          pose proof (IHm 1 a1 pb 0 r ltac:(mlia) HL) as IHr.
          cbn [mspec] in IHr.
          exact (IHr A' Hpb').
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA2 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : pb < a2).
        { rewrite HA2. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 4 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOfree_in].
        destruct Hca as [[-> ->]|[Hne HL]].
        * rewrite Nat.eqb_refl. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          pose proof (IHm 1 a1 pb 0 r ltac:(mlia) HL) as IHr.
          cbn [mspec] in IHr.
          exact (IHr A' Hpb').
    - (* term substitution *)
      cbn [mspec]. intros s t Hs2 Ht3.
      unfold step2_sem in Hst.
      destruct Hst as [C|[C|[C|[C|C]]]].
      + destruct C as [y [Hyb [Hcp Hca]]].
        rewrite Ht3 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        subst v0.
        cbn [FOsubst_t].
        destruct Hca as [[-> ->]|[Hne ->]].
        * rewrite Nat.eqb_refl. exact Hs2.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          cbn [FOcode_tm]. exact Ht3.
      + destruct C as [Hcp ->].
        rewrite Ht3 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 _];
          try discriminate Hcp1.
        cbn [FOsubst_t FOcode_tm]. exact Ht3.
      + destruct C as [tc' [Htcb [Hcp [r' [Hr'b [HL Hr]]]]]].
        rewrite Ht3 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        assert (Hbnd : 2 + tc' <= a3).
        { rewrite Ht3. cbn [FOcode_tm]. rewrite Hcp2.
          apply cpair_bound. }
        pose proof (IHm 2 a1 a2 tc' r' ltac:(mlia) HL) as IH1.
        cbn [mspec] in IH1.
        specialize (IH1 s t' Hs2 Hcp2).
        cbn [FOsubst_t FOcode_tm].
        rewrite <- IH1. symmetry. exact Hr.
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
          [rb [Hrbb [HLa [HLb [q [Hqb [Hq Hr]]]]]]]]]]]]]]]]].
        rewrite Ht3 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb < a3).
        { rewrite Ht3. cbn [FOcode_tm]. rewrite Hta, Htb.
          pose proof (cpair_bound 3
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        pose proof (IHm 2 a1 a2 ta ra ltac:(mlia) HLa) as IHa.
        pose proof (IHm 2 a1 a2 tb rb ltac:(mlia) HLb) as IHb.
        cbn [mspec] in IHa, IHb.
        specialize (IHa s t1 Hs2 Hta). specialize (IHb s t2 Hs2 Htb).
        cbn [FOsubst_t FOcode_tm].
        rewrite <- IHa, <- IHb, Hq. symmetry. exact Hr.
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
          [rb [Hrbb [HLa [HLb [q [Hqb [Hq Hr]]]]]]]]]]]]]]]]].
        rewrite Ht3 in Hcp.
        destruct t as [v0| |t'|t1 t2|t1 t2]; cbn [FOcode_tm] in Hcp;
          apply cpair_inj in Hcp; destruct Hcp as [Hcp1 Hcp2];
          try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb < a3).
        { rewrite Ht3. cbn [FOcode_tm]. rewrite Hta, Htb.
          pose proof (cpair_bound 4
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        pose proof (IHm 2 a1 a2 ta ra ltac:(mlia) HLa) as IHa.
        pose proof (IHm 2 a1 a2 tb rb ltac:(mlia) HLb) as IHb.
        cbn [mspec] in IHa, IHb.
        specialize (IHa s t1 Hs2 Hta). specialize (IHb s t2 Hs2 Htb).
        cbn [FOsubst_t FOcode_tm].
        rewrite <- IHa, <- IHb, Hq. symmetry. exact Hr.
    - (* formula substitution *)
      cbn [mspec]. intros s A Hs2 HA3.
      unfold step3_sem in Hst.
      destruct Hst as [C|[C|[C|[C|C]]]].
      + destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
          [rb [Hrbb [HLa [HLb [q [Hqb [Hq Hr]]]]]]]]]]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hta Htb].
        assert (Hba : ta + tb <= a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hta, Htb.
          pose proof (cpair_bound 0
            (cpair (FOcode_tm t1) (FOcode_tm t2))).
          pose proof (cpair_bound (FOcode_tm t1) (FOcode_tm t2)).
          lia. }
        pose proof (IHm 2 a1 a2 ta ra ltac:(mlia) HLa) as IHa.
        pose proof (IHm 2 a1 a2 tb rb ltac:(mlia) HLb) as IHb.
        cbn [mspec] in IHa, IHb.
        specialize (IHa s t1 Hs2 Hta). specialize (IHb s t2 Hs2 Htb).
        cbn [FOsubst_f FOcode_f].
        rewrite <- IHa, <- IHb, Hq. symmetry. exact Hr.
      + destruct C as [Hcp ->].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 _]; try discriminate Hcp1.
        cbn [FOsubst_f FOcode_f]. exact HA3.
      + destruct C as [p [Hpb [Hcp [pa [Hpab [pb [Hpbb [Hp [ra [Hrab
          [rb [Hrbb [HLa [HLb [q [Hqb [Hq Hr]]]]]]]]]]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hpa Hpb'].
        assert (Hba : pa + pb < a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpa, Hpb'.
          pose proof (cpair_bound 2
            (cpair (FOcode_f A1) (FOcode_f A2))).
          pose proof (cpair_bound (FOcode_f A1) (FOcode_f A2)).
          lia. }
        pose proof (IHm 3 a1 a2 pa ra ltac:(mlia) HLa) as IHa.
        pose proof (IHm 3 a1 a2 pb rb ltac:(mlia) HLb) as IHb.
        cbn [mspec] in IHa, IHb.
        specialize (IHa s A1 Hs2 Hpa). specialize (IHb s A2 Hs2 Hpb').
        cbn [FOsubst_f FOcode_f].
        rewrite <- IHa, <- IHb, Hq. symmetry. exact Hr.
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : pb < a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 3 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOsubst_f].
        destruct Hca as [[-> ->]|[Hne [rb [Hrbb [HL [q [Hqb
          [Hq Hr]]]]]]]].
        * rewrite Nat.eqb_refl. exact HA3.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          pose proof (IHm 3 a1 a2 pb rb ltac:(mlia) HL) as IHr.
          cbn [mspec] in IHr.
          specialize (IHr s A' Hs2 Hpb').
          cbn [FOcode_f].
          rewrite <- IHr, Hq. symmetry. exact Hr.
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : pb < a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 4 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOsubst_f].
        destruct Hca as [[-> ->]|[Hne [rb [Hrbb [HL [q [Hqb
          [Hq Hr]]]]]]]].
        * rewrite Nat.eqb_refl. exact HA3.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          pose proof (IHm 3 a1 a2 pb rb ltac:(mlia) HL) as IHr.
          cbn [mspec] in IHr.
          specialize (IHr s A' Hs2 Hpb').
          cbn [FOcode_f].
          rewrite <- IHr, Hq. symmetry. exact Hr.
    - (* capture test *)
      cbn [mspec]. intros s A Hs2 HA3.
      unfold step4_sem in Hst.
      destruct Hst as [C|[C|[C|[C|C]]]].
      + destruct C as [p [Hpb [Hcp ->]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 _]; try discriminate Hcp1.
        reflexivity.
      + destruct C as [Hcp ->].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 _]; try discriminate Hcp1.
        reflexivity.
      + destruct C as [p [Hpb [Hcp [pa [Hpab [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hpa Hpb'].
        assert (Hba : pa + pb < a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpa, Hpb'.
          pose proof (cpair_bound 2
            (cpair (FOcode_f A1) (FOcode_f A2))).
          pose proof (cpair_bound (FOcode_f A1) (FOcode_f A2)).
          lia. }
        cbn [FOsubst_ok].
        destruct Hca as [[HL ->]|[HL1 HLr]].
        * pose proof (IHm 4 a1 a2 pa 0 ltac:(mlia) HL) as IH0.
          cbn [mspec] in IH0.
          specialize (IH0 s A1 Hs2 Hpa).
          destruct (FOsubst_ok a1 s A1) eqn:E1; [discriminate IH0|].
          reflexivity.
        * pose proof (IHm 4 a1 a2 pa 1 ltac:(mlia) HL1) as IH1.
          pose proof (IHm 4 a1 a2 pb r ltac:(mlia) HLr) as IHr.
          cbn [mspec] in IH1, IHr.
          specialize (IH1 s A1 Hs2 Hpa).
          specialize (IHr s A2 Hs2 Hpb').
          destruct (FOsubst_ok a1 s A1) eqn:E1; [|discriminate IH1].
          exact IHr.
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : y + pb + 3 <= a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 3 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOsubst_ok].
        destruct Hca as [[-> ->]|[Hne Hca]].
        * rewrite Nat.eqb_refl. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          destruct Hca as [[HLf ->]|[HLf Hca]].
          -- pose proof (IHm 1 a1 pb 0 0 ltac:(mlia) HLf) as IHf.
             cbn [mspec] in IHf.
             specialize (IHf A' Hpb').
             destruct (FOfree_in a1 A') eqn:Ef; [discriminate IHf|].
             reflexivity.
          -- pose proof (IHm 1 a1 pb 0 1 ltac:(mlia) HLf) as IHf.
             cbn [mspec] in IHf.
             specialize (IHf A' Hpb').
             destruct (FOfree_in a1 A') eqn:Ef; [|discriminate IHf].
             destruct Hca as [[HLg ->]|[HLg HLr]].
             ++ pose proof (IHm 0 y a2 0 1 ltac:(mlia) HLg) as IHg.
                cbn [mspec] in IHg.
                specialize (IHg s Hs2).
                destruct (FOin_tm y s) eqn:Eg; [|discriminate IHg].
                reflexivity.
             ++ pose proof (IHm 0 y a2 0 0 ltac:(mlia) HLg) as IHg.
                pose proof (IHm 4 a1 a2 pb r ltac:(mlia) HLr) as IHr.
                cbn [mspec] in IHg, IHr.
                specialize (IHg s Hs2).
                specialize (IHr s A' Hs2 Hpb').
                destruct (FOin_tm y s) eqn:Eg; [discriminate IHg|].
                exact IHr.
      + destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hca]]]]]]]].
        rewrite HA3 in Hcp.
        destruct A as [t1 t2| |A1 A2|y0 A'|y0 A']; cbn [FOcode_f]
          in Hcp; apply cpair_inj in Hcp;
          destruct Hcp as [Hcp1 Hcp2]; try discriminate Hcp1.
        rewrite Hcp2 in Hp.
        apply cpair_inj in Hp. destruct Hp as [Hy Hpb'].
        subst y0.
        assert (Hba : y + pb + 3 <= a3).
        { rewrite HA3. cbn [FOcode_f]. rewrite Hpb'.
          pose proof (cpair_bound 4 (cpair y (FOcode_f A'))).
          pose proof (cpair_bound y (FOcode_f A')).
          lia. }
        cbn [FOsubst_ok].
        destruct Hca as [[-> ->]|[Hne Hca]].
        * rewrite Nat.eqb_refl. reflexivity.
        * rewrite (proj2 (Nat.eqb_neq y a1) Hne).
          destruct Hca as [[HLf ->]|[HLf Hca]].
          -- pose proof (IHm 1 a1 pb 0 0 ltac:(mlia) HLf) as IHf.
             cbn [mspec] in IHf.
             specialize (IHf A' Hpb').
             destruct (FOfree_in a1 A') eqn:Ef; [discriminate IHf|].
             reflexivity.
          -- pose proof (IHm 1 a1 pb 0 1 ltac:(mlia) HLf) as IHf.
             cbn [mspec] in IHf.
             specialize (IHf A' Hpb').
             destruct (FOfree_in a1 A') eqn:Ef; [|discriminate IHf].
             destruct Hca as [[HLg ->]|[HLg HLr]].
             ++ pose proof (IHm 0 y a2 0 1 ltac:(mlia) HLg) as IHg.
                cbn [mspec] in IHg.
                specialize (IHg s Hs2).
                destruct (FOin_tm y s) eqn:Eg; [|discriminate IHg].
                reflexivity.
             ++ pose proof (IHm 0 y a2 0 0 ltac:(mlia) HLg) as IHg.
                pose proof (IHm 4 a1 a2 pb r ltac:(mlia) HLr) as IHr.
                cbn [mspec] in IHg, IHr.
                specialize (IHg s Hs2).
                specialize (IHr s A' Hs2 Hpb').
                destruct (FOin_tm y s) eqn:Eg; [discriminate IHg|].
                exact IHr.
    - (* numeral coding *)
      cbn [mspec].
      unfold step5_sem in Hst.
      destruct Hst as [[-> Hr]|[k' [Hk'b [-> [r' [Hr'b [HL Hr]]]]]]].
      + cbn [FOnumeral FOcode_tm]. symmetry. exact Hr.
      + pose proof (IHm 5 k' 0 0 r' ltac:(mlia) HL) as IH1.
        cbn [mspec] in IH1.
        cbn [FOnumeral FOcode_tm].
        rewrite <- IH1. symmetry. exact Hr.
  }
  intros tg a1 a2 a3 r Hmem.
  exact (MAIN (S (a1 + a2 + a3 + mw tg)) tg a1 a2 a3 r
           (Nat.lt_succ_diag_r _) Hmem).
Qed.

(** ** Genuineness from table rows.

    The step relations are partial: a substitution row exists only
    when the recursion completes through valid constructor tags.  A
    term-substitution row therefore forces its input to be a genuine
    term code.  A formula-substitution row forces its input to be a
    genuine formula code provided the substitution variable exceeds
    the input code, since every binder payload inside the code is
    below the code itself and the shadowing stop can never fire. *)

Lemma tbl_genuine_tm : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
    vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall x sc tc r,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 2 x sc tc r ->
    exists t, tc = FOcode_tm t.
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid.
  assert (MAIN : forall m x sc tc r,
      tc < m ->
      tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 2 x sc tc r ->
      exists t, tc = FOcode_tm t).
  { induction m as [|m IHm].
    { intros; lia. }
    intros x sc tc r Hm Hmem.
    destruct Hmem as [j [Hj Hf]].
    pose proof (Hvalid j Hj) as Hd.
    unfold dispatch_sem in Hd.
    destruct Hd as [tg' [Htgb [a1' [Ha1b [a2' [Ha2b [a3' [Ha3b [rr'
      [Hrrb [Hbt [Hb1 [Hb2 [Hb3 [Hbr Hsw]]]]]]]]]]]]]]].
    destruct Hf as [Hft [Hf1 [Hf2 [Hf3 Hfr]]]].
    assert (Etg : tg' = 2) by congruence.
    assert (Ea1 : a1' = x) by congruence.
    assert (Ea2 : a2' = sc) by congruence.
    assert (Ea3 : a3' = tc) by congruence.
    assert (Err : rr' = r) by congruence.
    clear Hbt Hb1 Hb2 Hb3 Hbr Hft Hf1 Hf2 Hf3 Hfr Htgb Ha1b Ha2b
      Ha3b Hrrb Hj.
    subst tg' a1' a2' a3' rr'.
    destruct Hsw as [[E _]|[[E _]|[[_ Hst]|[[E _]|[[E _]|[E _]]]]]];
      try discriminate E.
    unfold step2_sem in Hst.
    destruct Hst as [C|[C|[C|[C|C]]]].
    - destruct C as [y [Hyb [Hcp Hca]]].
      exists (FOVar y). cbn [FOcode_tm]. symmetry. exact Hcp.
    - destruct C as [Hcp Hr].
      exists FOZero. cbn [FOcode_tm]. symmetry. exact Hcp.
    - destruct C as [tc' [Htcb [Hcp [r' [Hr'b [Hsub Hcr]]]]]].
      pose proof (cpair_bound 2 tc') as Hgrow. rewrite Hcp in Hgrow.
      destruct (IHm x sc tc' r' ltac:(lia) Hsub) as [t' Ht'].
      exists (FOSucc t'). cbn [FOcode_tm].
      rewrite <- Ht', Hcp. reflexivity.
    - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
        [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
      pose proof (cpair_bound 3 p) as Hg1. rewrite Hcp in Hg1.
      pose proof (cpair_bound ta tb) as Hg2. rewrite Hp in Hg2.
      destruct (IHm x sc ta ra ltac:(lia) Hsa) as [t1 Ht1].
      destruct (IHm x sc tb rb ltac:(lia) Hsb) as [t2 Ht2].
      exists (FOPlus t1 t2). cbn [FOcode_tm].
      rewrite <- Ht1, <- Ht2, Hp, Hcp. reflexivity.
    - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
        [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
      pose proof (cpair_bound 4 p) as Hg1. rewrite Hcp in Hg1.
      pose proof (cpair_bound ta tb) as Hg2. rewrite Hp in Hg2.
      destruct (IHm x sc ta ra ltac:(lia) Hsa) as [t1 Ht1].
      destruct (IHm x sc tb rb ltac:(lia) Hsb) as [t2 Ht2].
      exists (FOMult t1 t2). cbn [FOcode_tm].
      rewrite <- Ht1, <- Ht2, Hp, Hcp. reflexivity. }
  intros x sc tc r Hmem.
  exact (MAIN (S tc) x sc tc r (Nat.lt_succ_diag_r tc) Hmem).
Qed.

Lemma tbl_genuine_f : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
    vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall x sc pc r,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 3 x sc pc r ->
    pc < x ->
    exists A, pc = FOcode_f A.
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid.
  assert (MAIN : forall m x sc pc r,
      pc < m -> pc < x ->
      tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 3 x sc pc r ->
      exists A, pc = FOcode_f A).
  { induction m as [|m IHm].
    { intros; lia. }
    intros x sc pc r Hm Hx Hmem.
    destruct Hmem as [j [Hj Hf]].
    pose proof (Hvalid j Hj) as Hd.
    unfold dispatch_sem in Hd.
    destruct Hd as [tg' [Htgb [a1' [Ha1b [a2' [Ha2b [a3' [Ha3b [rr'
      [Hrrb [Hbt [Hb1 [Hb2 [Hb3 [Hbr Hsw]]]]]]]]]]]]]]].
    destruct Hf as [Hft [Hf1 [Hf2 [Hf3 Hfr]]]].
    assert (Etg : tg' = 3) by congruence.
    assert (Ea1 : a1' = x) by congruence.
    assert (Ea2 : a2' = sc) by congruence.
    assert (Ea3 : a3' = pc) by congruence.
    assert (Err : rr' = r) by congruence.
    clear Hbt Hb1 Hb2 Hb3 Hbr Hft Hf1 Hf2 Hf3 Hfr Htgb Ha1b Ha2b
      Ha3b Hrrb Hj.
    subst tg' a1' a2' a3' rr'.
    destruct Hsw as [[E _]|[[E _]|[[E _]|[[_ Hst]|[[E _]|[E _]]]]]];
      try discriminate E.
    unfold step3_sem in Hst.
    destruct Hst as [C|[C|[C|[C|C]]]].
    - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
        [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
      destruct (tbl_genuine_tm vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr
                  vdr vlen Hvalid x sc ta ra Hsa) as [t1 Ht1].
      destruct (tbl_genuine_tm vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr
                  vdr vlen Hvalid x sc tb rb Hsb) as [t2 Ht2].
      exists (FOEq t1 t2). cbn [FOcode_f].
      rewrite <- Ht1, <- Ht2, Hp, Hcp. reflexivity.
    - destruct C as [Hcp Hr].
      exists FOFalseF. cbn [FOcode_f]. symmetry. exact Hcp.
    - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
        [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
      pose proof (cpair_bound 2 p) as Hg1. rewrite Hcp in Hg1.
      pose proof (cpair_bound ta tb) as Hg2. rewrite Hp in Hg2.
      destruct (IHm x sc ta ra ltac:(lia) ltac:(lia) Hsa) as [B1 HB1].
      destruct (IHm x sc tb rb ltac:(lia) ltac:(lia) Hsb) as [B2 HB2].
      exists (FOImplF B1 B2). cbn [FOcode_f].
      rewrite <- HB1, <- HB2, Hp, Hcp. reflexivity.
    - destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hcase]]]]]]]].
      pose proof (cpair_bound 3 p) as Hg1. rewrite Hcp in Hg1.
      pose proof (cpair_bound y pb) as Hg2. rewrite Hp in Hg2.
      destruct Hcase as [[Exy Hr]|[Hneq [rb [Hrbb [Hsub Hq]]]]].
      { exfalso. lia. }
      destruct (IHm x sc pb rb ltac:(lia) ltac:(lia) Hsub) as [B HB].
      exists (FOForall y B). cbn [FOcode_f].
      rewrite <- HB, Hp, Hcp. reflexivity.
    - destruct C as [p [Hpb [Hcp [y [Hyb [pb [Hpbb [Hp Hcase]]]]]]]].
      pose proof (cpair_bound 4 p) as Hg1. rewrite Hcp in Hg1.
      pose proof (cpair_bound y pb) as Hg2. rewrite Hp in Hg2.
      destruct Hcase as [[Exy Hr]|[Hneq [rb [Hrbb [Hsub Hq]]]]].
      { exfalso. lia. }
      destruct (IHm x sc pb rb ltac:(lia) ltac:(lia) Hsub) as [B HB].
      exists (FOExists y B). cbn [FOcode_f].
      rewrite <- HB, Hp, Hcp. reflexivity. }
  intros x sc pc r Hmem Hx.
  exact (MAIN (S pc) x sc pc r (Nat.lt_succ_diag_r pc) Hx Hmem).
Qed.

(** ** Substitution-row inversion and the substitution witness.

    A validated table makes every tag-2 and tag-3 row satisfy its
    step relation.  At genuine input and output codes, a substitution
    row either touches no occurrence — the variable is not free and
    the output equals the input — or it places the substituted code
    into the output, forcing it to be a genuine term code. *)

Lemma tblL_step2 : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
    vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall x sc tc r,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 2 x sc tc r ->
    step2_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
      x sc tc r.
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid
    x sc tc r Hmem.
  destruct Hmem as [j [Hj Hf]].
  pose proof (Hvalid j Hj) as Hd.
  unfold dispatch_sem in Hd.
  destruct Hd as [tg' [Htgb [a1' [Ha1b [a2' [Ha2b [a3' [Ha3b [rr'
    [Hrrb [Hbt [Hb1 [Hb2 [Hb3 [Hbr Hsw]]]]]]]]]]]]]]].
  destruct Hf as [Hft [Hf1 [Hf2 [Hf3 Hfr]]]].
  assert (Etg : tg' = 2) by congruence.
  assert (Ea1 : a1' = x) by congruence.
  assert (Ea2 : a2' = sc) by congruence.
  assert (Ea3 : a3' = tc) by congruence.
  assert (Err : rr' = r) by congruence.
  clear Hbt Hb1 Hb2 Hb3 Hbr Hft Hf1 Hf2 Hf3 Hfr Htgb Ha1b Ha2b
    Ha3b Hrrb Hj.
  subst tg' a1' a2' a3' rr'.
  destruct Hsw as [[E _]|[[E _]|[[_ Hst]|[[E _]|[[E _]|[E _]]]]]];
    try discriminate E.
  exact Hst.
Qed.

Lemma tblL_step3 : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
    vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall x sc pc r,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 3 x sc pc r ->
    step3_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
      x sc pc r.
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid
    x sc pc r Hmem.
  destruct Hmem as [j [Hj Hf]].
  pose proof (Hvalid j Hj) as Hd.
  unfold dispatch_sem in Hd.
  destruct Hd as [tg' [Htgb [a1' [Ha1b [a2' [Ha2b [a3' [Ha3b [rr'
    [Hrrb [Hbt [Hb1 [Hb2 [Hb3 [Hbr Hsw]]]]]]]]]]]]]]].
  destruct Hf as [Hft [Hf1 [Hf2 [Hf3 Hfr]]]].
  assert (Etg : tg' = 3) by congruence.
  assert (Ea1 : a1' = x) by congruence.
  assert (Ea2 : a2' = sc) by congruence.
  assert (Ea3 : a3' = pc) by congruence.
  assert (Err : rr' = r) by congruence.
  clear Hbt Hb1 Hb2 Hb3 Hbr Hft Hf1 Hf2 Hf3 Hfr Htgb Ha1b Ha2b
    Ha3b Hrrb Hj.
  subst tg' a1' a2' a3' rr'.
  destruct Hsw as [[E _]|[[E _]|[[E _]|[[_ Hst]|[[E _]|[E _]]]]]];
    try discriminate E.
  exact Hst.
Qed.

Lemma tbl_subst_tm_witness : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3
    vcr vdr vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall t' r' x sc,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 2 x sc
      (FOcode_tm t') (FOcode_tm r') ->
    (FOin_tm x t' = false /\ FOcode_tm r' = FOcode_tm t')
    \/ (exists s, sc = FOcode_tm s).
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid.
  induction t' as [y| |t1 IH|t1 IH1 t2 IH2|t1 IH1 t2 IH2];
    intros r' x sc Hrow;
    apply (tblL_step2 _ _ _ _ _ _ _ _ _ _ _ Hvalid) in Hrow;
    unfold step2_sem in Hrow;
    cbn [FOcode_tm] in Hrow;
    destruct Hrow as [C|[C|[C|[C|C]]]].
  - destruct C as [y0 [Hyb [Hcp Hca]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hy0]. subst y0.
    destruct Hca as [[Exy Hr]|[Hne Hr]].
    + right. exists r'. symmetry. exact Hr.
    + left. split.
      * cbn [FOin_tm]. exact (proj2 (Nat.eqb_neq y x) Hne).
      * cbn [FOcode_tm]. exact Hr.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [tc' [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [y0 [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [_ Hr].
    left. split; [reflexivity|]. exact Hr.
  - destruct C as [tc' [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [y0 [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [tc' [Htcb [Hcp [rsub [Hrb [Hsubrow Hcr]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Htc']. subst tc'.
    destruct r' as [ry| |r1|r1 r2|r1 r2]; cbn [FOcode_tm] in Hcr;
      apply cpair_inj in Hcr; destruct Hcr as [Ecr Hrs];
      try discriminate Ecr.
    subst rsub.
    destruct (IH r1 x sc Hsubrow) as [[Hin Heq]|Hgen].
    + left. split.
      * cbn [FOin_tm]. exact Hin.
      * cbn [FOcode_tm]. rewrite Heq. reflexivity.
    + right. exact Hgen.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [y0 [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [tc' [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
      [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hta Htb2]. subst ta tb.
    destruct r' as [ry| |r1|r1 r2|r1 r2]; cbn [FOcode_tm] in Hcr;
      apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
      try discriminate Ecr.
    rewrite Hq2 in Hq.
    apply cpair_inj in Hq. destruct Hq as [Hra Hrb2]. subst ra rb.
    destruct (IH1 r1 x sc Hsa) as [[Hin1 Heq1]|Hgen];
      [|right; exact Hgen].
    destruct (IH2 r2 x sc Hsb) as [[Hin2 Heq2]|Hgen];
      [|right; exact Hgen].
    left. split.
    + cbn [FOin_tm]. rewrite Hin1, Hin2. reflexivity.
    + cbn [FOcode_tm]. rewrite Heq1, Heq2. reflexivity.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [y0 [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [tc' [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
      [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hta Htb2]. subst ta tb.
    destruct r' as [ry| |r1|r1 r2|r1 r2]; cbn [FOcode_tm] in Hcr;
      apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
      try discriminate Ecr.
    rewrite Hq2 in Hq.
    apply cpair_inj in Hq. destruct Hq as [Hra Hrb2]. subst ra rb.
    destruct (IH1 r1 x sc Hsa) as [[Hin1 Heq1]|Hgen];
      [|right; exact Hgen].
    destruct (IH2 r2 x sc Hsb) as [[Hin2 Heq2]|Hgen];
      [|right; exact Hgen].
    left. split.
    + cbn [FOin_tm]. rewrite Hin1, Hin2. reflexivity.
    + cbn [FOcode_tm]. rewrite Heq1, Heq2. reflexivity.
Qed.

Lemma tbl_subst_f_witness : forall vct vdt vc1 vd1 vc2 vd2 vc3 vd3
    vcr vdr vlen,
  (forall j, j < vlen ->
     dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
       vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) ->
  forall P' Q' x sc,
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen 3 x sc
      (FOcode_f P') (FOcode_f Q') ->
    (FOfree_in x P' = false /\ FOcode_f Q' = FOcode_f P')
    \/ (exists s, sc = FOcode_tm s).
Proof.
  intros vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hvalid.
  induction P' as [a b| |B IHB Cf IHC|y B IHB|y B IHB];
    intros Q' x sc Hrow;
    apply (tblL_step3 _ _ _ _ _ _ _ _ _ _ _ Hvalid) in Hrow;
    unfold step3_sem in Hrow;
    cbn [FOcode_f] in Hrow;
    destruct Hrow as [C|[C|[C|[C|C]]]].
  - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
      [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hta Htb2]. subst ta tb.
    destruct Q' as [a2 b2| |Q1 Q2|y2 B2|y2 B2]; cbn [FOcode_f] in Hcr;
      apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
      try discriminate Ecr.
    rewrite Hq2 in Hq.
    apply cpair_inj in Hq. destruct Hq as [Hra Hrb2]. subst ra rb.
    destruct (tbl_subst_tm_witness _ _ _ _ _ _ _ _ _ _ _ Hvalid
                a a2 x sc Hsa) as [[Hin1 Heq1]|Hgen];
      [|right; exact Hgen].
    destruct (tbl_subst_tm_witness _ _ _ _ _ _ _ _ _ _ _ Hvalid
                b b2 x sc Hsb) as [[Hin2 Heq2]|Hgen];
      [|right; exact Hgen].
    left. split.
    + cbn [FOfree_in]. rewrite Hin1, Hin2. reflexivity.
    + cbn [FOcode_f]. rewrite Heq1, Heq2. reflexivity.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [_ Hr].
    left. split; [reflexivity|]. exact Hr.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [Hpb [Hcp [ta [Htab [tb [Htbb [Hp [ra [Hrab
      [rb [Hrbb [Hsa [Hsb [q [Hqb [Hq Hcr]]]]]]]]]]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hta Htb2]. subst ta tb.
    destruct Q' as [a2 b2| |Q1 Q2|y2 B2|y2 B2]; cbn [FOcode_f] in Hcr;
      apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
      try discriminate Ecr.
    rewrite Hq2 in Hq.
    apply cpair_inj in Hq. destruct Hq as [Hra Hrb2]. subst ra rb.
    destruct (IHB Q1 x sc Hsa) as [[Hin1 Heq1]|Hgen];
      [|right; exact Hgen].
    destruct (IHC Q2 x sc Hsb) as [[Hin2 Heq2]|Hgen];
      [|right; exact Hgen].
    left. split.
    + cbn [FOfree_in]. rewrite Hin1, Hin2. reflexivity.
    + cbn [FOcode_f]. rewrite Heq1, Heq2. reflexivity.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [Hpb [Hcp [y0 [Hyb [pb [Hpbb [Hp Hcase]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hy0 Hpb2]. subst y0 pb.
    destruct Hcase as [[Exy Hr]|[Hne [rb [Hrbb [Hsub [q [Hqb
      [Hq Hcr]]]]]]]].
    + left. split.
      * cbn [FOfree_in]. rewrite Exy, Nat.eqb_refl. reflexivity.
      * exact Hr.
    + destruct Q' as [a2 b2| |Q1 Q2|y2 B2|y2 B2];
        cbn [FOcode_f] in Hcr;
        apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
        try discriminate Ecr.
      rewrite Hq2 in Hq.
      apply cpair_inj in Hq. destruct Hq as [Hy2 Hrb2]. subst y2 rb.
      destruct (IHB B2 x sc Hsub) as [[Hin Heq]|Hgen];
        [|right; exact Hgen].
      left. split.
      * cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y x) Hne).
        exact Hin.
      * cbn [FOcode_f]. rewrite Heq. reflexivity.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [Hcp _].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [_ [Hcp _]]].
    apply cpair_inj in Hcp. destruct Hcp as [E _]. discriminate E.
  - destruct C as [p [Hpb [Hcp [y0 [Hyb [pb [Hpbb [Hp Hcase]]]]]]]].
    apply cpair_inj in Hcp. destruct Hcp as [_ Hpe]. subst p.
    apply cpair_inj in Hp. destruct Hp as [Hy0 Hpb2]. subst y0 pb.
    destruct Hcase as [[Exy Hr]|[Hne [rb [Hrbb [Hsub [q [Hqb
      [Hq Hcr]]]]]]]].
    + left. split.
      * cbn [FOfree_in]. rewrite Exy, Nat.eqb_refl. reflexivity.
      * exact Hr.
    + destruct Q' as [a2 b2| |Q1 Q2|y2 B2|y2 B2];
        cbn [FOcode_f] in Hcr;
        apply cpair_inj in Hcr; destruct Hcr as [Ecr Hq2];
        try discriminate Ecr.
      rewrite Hq2 in Hq.
      apply cpair_inj in Hq. destruct Hq as [Hy2 Hrb2]. subst y2 rb.
      destruct (IHB B2 x sc Hsub) as [[Hin Heq]|Hgen];
        [|right; exact Hgen].
      left. split.
      * cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y x) Hne).
        exact Hin.
      * cbn [FOcode_f]. rewrite Heq. reflexivity.
Qed.

(** ** Trace builders: completeness of the master table.

    For each represented function, a structurally recursive builder
    collects the entries of the recursion's call tree.  [entry_ok]
    states an entry's per-tag justification over the membership
    relation of a list; each builder's entries are justified within
    any superset of the builder's own output, with the seed entry
    present carrying the function's value. *)

Record TEntry : Type := mkTE {
  te_tg : nat;
  te_a1 : nat;
  te_a2 : nat;
  te_a3 : nat;
  te_r : nat
}.

Definition listL (L : list TEntry)
    : nat -> nat -> nat -> nat -> nat -> Prop :=
  fun tg a1 a2 a3 r => In (mkTE tg a1 a2 a3 r) L.

Definition entry_ok (L : list TEntry) (e : TEntry) : Prop :=
  match e with
  | mkTE 0 a1 a2 _ r => step0_sem (listL L) a1 a2 r
  | mkTE 1 a1 a2 _ r => step1_sem (listL L) a1 a2 r
  | mkTE 2 a1 a2 a3 r => step2_sem (listL L) a1 a2 a3 r
  | mkTE 3 a1 a2 a3 r => step3_sem (listL L) a1 a2 a3 r
  | mkTE 4 a1 a2 a3 r => step4_sem (listL L) a1 a2 a3 r
  | mkTE 5 a1 _ _ r => step5_sem (listL L) a1 r
  | mkTE _ _ _ _ _ => False
  end.

Lemma entry_ok_0 : forall L a1 a2 a3 r,
  step0_sem (listL L) a1 a2 r -> entry_ok L (mkTE 0 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma entry_ok_1 : forall L a1 a2 a3 r,
  step1_sem (listL L) a1 a2 r -> entry_ok L (mkTE 1 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma entry_ok_2 : forall L a1 a2 a3 r,
  step2_sem (listL L) a1 a2 a3 r -> entry_ok L (mkTE 2 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma entry_ok_3 : forall L a1 a2 a3 r,
  step3_sem (listL L) a1 a2 a3 r -> entry_ok L (mkTE 3 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma entry_ok_4 : forall L a1 a2 a3 r,
  step4_sem (listL L) a1 a2 a3 r -> entry_ok L (mkTE 4 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma entry_ok_5 : forall L a1 a2 a3 r,
  step5_sem (listL L) a1 r -> entry_ok L (mkTE 5 a1 a2 a3 r).
Proof. intros L a1 a2 a3 r H. exact H. Qed.

Lemma in_last : forall (X : Type) (l : list X) (x : X), In x (l ++ [x]).
Proof. intros X l x. apply in_or_app. right. left. reflexivity. Qed.

Lemma incl_app_head : forall (X : Type) (l1 l2 L : list X),
  incl (l1 ++ l2) L -> incl l1 L.
Proof.
  intros X l1 l2 L H z Hz. apply H. apply in_or_app. left. exact Hz.
Qed.

Lemma incl_app_tail : forall (X : Type) (l1 l2 L : list X),
  incl (l1 ++ l2) L -> incl l2 L.
Proof.
  intros X l1 l2 L H z Hz. apply H. apply in_or_app. right. exact Hz.
Qed.

Definition t0E (w : nat) (t : FOTerm) : TEntry :=
  mkTE 0 w (FOcode_tm t) 0 (if FOin_tm w t then 1 else 0).

Definition t1E (w : nat) (A : FOFormula) : TEntry :=
  mkTE 1 w (FOcode_f A) 0 (if FOfree_in w A then 1 else 0).

Definition t2E (x : nat) (s t : FOTerm) : TEntry :=
  mkTE 2 x (FOcode_tm s) (FOcode_tm t) (FOcode_tm (FOsubst_t x s t)).

Definition t3E (x : nat) (s : FOTerm) (A : FOFormula) : TEntry :=
  mkTE 3 x (FOcode_tm s) (FOcode_f A) (FOcode_f (FOsubst_f x s A)).

Definition t4E (x : nat) (s : FOTerm) (A : FOFormula) : TEntry :=
  mkTE 4 x (FOcode_tm s) (FOcode_f A)
    (if FOsubst_ok x s A then 1 else 0).

Definition t5E (k : nat) : TEntry :=
  mkTE 5 k 0 0 (FOcode_tm (FOnumeral k)).

Fixpoint trace0 (w : nat) (t : FOTerm) : list TEntry :=
  match t with
  | FOVar y => [t0E w (FOVar y)]
  | FOZero => [t0E w FOZero]
  | FOSucc a => trace0 w a ++ [t0E w (FOSucc a)]
  | FOPlus a b => trace0 w a ++ trace0 w b ++ [t0E w (FOPlus a b)]
  | FOMult a b => trace0 w a ++ trace0 w b ++ [t0E w (FOMult a b)]
  end.

Fixpoint trace1 (w : nat) (A : FOFormula) : list TEntry :=
  match A with
  | FOEq a b => trace0 w a ++ trace0 w b ++ [t1E w (FOEq a b)]
  | FOFalseF => [t1E w FOFalseF]
  | FOImplF B C => trace1 w B ++ trace1 w C ++ [t1E w (FOImplF B C)]
  | FOForall y B => trace1 w B ++ [t1E w (FOForall y B)]
  | FOExists y B => trace1 w B ++ [t1E w (FOExists y B)]
  end.

Fixpoint trace2 (x : nat) (s t : FOTerm) : list TEntry :=
  match t with
  | FOVar y => [t2E x s (FOVar y)]
  | FOZero => [t2E x s FOZero]
  | FOSucc a => trace2 x s a ++ [t2E x s (FOSucc a)]
  | FOPlus a b => trace2 x s a ++ trace2 x s b ++ [t2E x s (FOPlus a b)]
  | FOMult a b => trace2 x s a ++ trace2 x s b ++ [t2E x s (FOMult a b)]
  end.

Fixpoint trace3 (x : nat) (s : FOTerm) (A : FOFormula) : list TEntry :=
  match A with
  | FOEq a b => trace2 x s a ++ trace2 x s b ++ [t3E x s (FOEq a b)]
  | FOFalseF => [t3E x s FOFalseF]
  | FOImplF B C =>
      trace3 x s B ++ trace3 x s C ++ [t3E x s (FOImplF B C)]
  | FOForall y B => trace3 x s B ++ [t3E x s (FOForall y B)]
  | FOExists y B => trace3 x s B ++ [t3E x s (FOExists y B)]
  end.

Fixpoint trace4 (x : nat) (s : FOTerm) (A : FOFormula) : list TEntry :=
  match A with
  | FOEq a b => [t4E x s (FOEq a b)]
  | FOFalseF => [t4E x s FOFalseF]
  | FOImplF B C =>
      trace4 x s B ++ trace4 x s C ++ [t4E x s (FOImplF B C)]
  | FOForall y B =>
      trace1 x B ++ trace0 y s ++ trace4 x s B
        ++ [t4E x s (FOForall y B)]
  | FOExists y B =>
      trace1 x B ++ trace0 y s ++ trace4 x s B
        ++ [t4E x s (FOExists y B)]
  end.

Fixpoint trace5 (k : nat) : list TEntry :=
  match k with
  | 0 => [t5E 0]
  | S k' => trace5 k' ++ [t5E (S k')]
  end.

Lemma trace0_seed : forall w t r,
  r = (if FOin_tm w t then 1 else 0) ->
  In (mkTE 0 w (FOcode_tm t) 0 r) (trace0 w t).
Proof.
  intros w t r ->.
  destruct t as [y | | a | a b | a b]; cbn [trace0].
  - left. reflexivity.
  - left. reflexivity.
  - apply in_last.
  - apply in_or_app. right. apply in_last.
  - apply in_or_app. right. apply in_last.
Qed.

Lemma trace1_seed : forall w A r,
  r = (if FOfree_in w A then 1 else 0) ->
  In (mkTE 1 w (FOcode_f A) 0 r) (trace1 w A).
Proof.
  intros w A r ->.
  destruct A as [a b | | B C | y B | y B]; cbn [trace1].
  - apply in_or_app. right. apply in_last.
  - left. reflexivity.
  - apply in_or_app. right. apply in_last.
  - apply in_last.
  - apply in_last.
Qed.

Lemma trace2_seed : forall x s t r,
  r = FOcode_tm (FOsubst_t x s t) ->
  In (mkTE 2 x (FOcode_tm s) (FOcode_tm t) r) (trace2 x s t).
Proof.
  intros x s t r ->.
  destruct t as [y | | a | a b | a b]; cbn [trace2].
  - left. reflexivity.
  - left. reflexivity.
  - apply in_last.
  - apply in_or_app. right. apply in_last.
  - apply in_or_app. right. apply in_last.
Qed.

Lemma trace3_seed : forall x s A r,
  r = FOcode_f (FOsubst_f x s A) ->
  In (mkTE 3 x (FOcode_tm s) (FOcode_f A) r) (trace3 x s A).
Proof.
  intros x s A r ->.
  destruct A as [a b | | B C | y B | y B]; cbn [trace3].
  - apply in_or_app. right. apply in_last.
  - left. reflexivity.
  - apply in_or_app. right. apply in_last.
  - apply in_last.
  - apply in_last.
Qed.

Lemma trace4_seed : forall x s A r,
  r = (if FOsubst_ok x s A then 1 else 0) ->
  In (mkTE 4 x (FOcode_tm s) (FOcode_f A) r) (trace4 x s A).
Proof.
  intros x s A r ->.
  destruct A as [a b | | B C | y B | y B]; cbn [trace4].
  - left. reflexivity.
  - left. reflexivity.
  - apply in_or_app. right. apply in_last.
  - apply in_or_app. right. apply in_or_app. right. apply in_last.
  - apply in_or_app. right. apply in_or_app. right. apply in_last.
Qed.

Lemma trace5_seed : forall k r,
  r = FOcode_tm (FOnumeral k) ->
  In (mkTE 5 k 0 0 r) (trace5 k).
Proof.
  intros k r ->.
  destruct k as [|k']; cbn [trace5].
  - left. reflexivity.
  - apply in_last.
Qed.

Lemma trace0_ok : forall w t L,
  incl (trace0 w t) L ->
  forall e, In e (trace0 w t) -> entry_ok L e.
Proof.
  intros w t. induction t as [y | | a IHa | a IHa b IHb | a IHa b IHb];
    intros L Hincl e HeIn; cbn [trace0] in HeIn.
  - destruct HeIn as [<- | []].
    apply entry_ok_0. cbn [FOin_tm FOcode_tm].
    unfold step0_sem. left.
    exists y. split.
    { pose proof (cpair_bound 0 y). lia. }
    split. { reflexivity. }
    destruct (Nat.eqb y w) eqn:Ey.
    + left. split. { apply Nat.eqb_eq. exact Ey. } { reflexivity. }
    + right. split. { apply Nat.eqb_neq. exact Ey. } { reflexivity. }
  - destruct HeIn as [<- | []].
    apply entry_ok_0. unfold step0_sem.
    right; left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_0. cbn [FOin_tm FOcode_tm].
      unfold step0_sem. right; right; left.
      exists (FOcode_tm a). split.
      { pose proof (cpair_bound 2 (FOcode_tm a)). lia. }
      split. { reflexivity. }
      apply Hincl. cbn [trace0]. apply in_or_app. left.
      apply trace0_seed. reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHb L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_0. cbn [FOin_tm FOcode_tm].
        unfold step0_sem. right; right; right; left.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 3 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        destruct (FOin_tm w a) eqn:E1; cbn [orb].
        -- left. split.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ reflexivity.
        -- right. split.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. right.
              apply in_or_app. left.
              apply trace0_seed. reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHb L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_0. cbn [FOin_tm FOcode_tm].
        unfold step0_sem. right; right; right; right.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 4 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        destruct (FOin_tm w a) eqn:E1; cbn [orb].
        -- left. split.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ reflexivity.
        -- right. split.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ apply Hincl. cbn [trace0]. apply in_or_app. right.
              apply in_or_app. left.
              apply trace0_seed. reflexivity.
Qed.

Lemma trace1_ok : forall w A L,
  incl (trace1 w A) L ->
  forall e, In e (trace1 w A) -> entry_ok L e.
Proof.
  intros w A. induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros L Hincl e HeIn; cbn [trace1] in HeIn.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (trace0_ok w a L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (trace0_ok w b L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_1. cbn [FOfree_in FOcode_f].
        unfold step1_sem. left.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 0 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        destruct (FOin_tm w a) eqn:E1; cbn [orb].
        -- left. split.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ reflexivity.
        -- right. split.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. left.
              apply trace0_seed. rewrite E1. reflexivity.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. right.
              apply in_or_app. left.
              apply trace0_seed. reflexivity.
  - destruct HeIn as [<- | []].
    apply entry_ok_1. unfold step1_sem.
    right; left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHC L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_1. cbn [FOfree_in FOcode_f].
        unfold step1_sem. right; right; left.
        exists (cpair (FOcode_f B) (FOcode_f C)). split.
        { pose proof (cpair_bound 2 (cpair (FOcode_f B) (FOcode_f C))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_f B). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        exists (FOcode_f C). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        split. { reflexivity. }
        destruct (FOfree_in w B) eqn:E1; cbn [orb].
        -- left. split.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. left.
              apply trace1_seed. rewrite E1. reflexivity.
           ++ reflexivity.
        -- right. split.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. left.
              apply trace1_seed. rewrite E1. reflexivity.
           ++ apply Hincl. cbn [trace1]. apply in_or_app. right.
              apply in_or_app. left.
              apply trace1_seed. reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_1. cbn [FOfree_in FOcode_f].
      unfold step1_sem. right; right; right; left.
      exists (cpair y (FOcode_f B)). split.
      { pose proof (cpair_bound 3 (cpair y (FOcode_f B))). lia. }
      split. { reflexivity. }
      exists y. split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      exists (FOcode_f B). split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      split. { reflexivity. }
      destruct (Nat.eqb y w) eqn:Ey.
      * left. split. { apply Nat.eqb_eq. exact Ey. } { reflexivity. }
      * right. split. { apply Nat.eqb_neq. exact Ey. }
        apply Hincl. cbn [trace1]. apply in_or_app. left.
        apply trace1_seed. reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_1. cbn [FOfree_in FOcode_f].
      unfold step1_sem. right; right; right; right.
      exists (cpair y (FOcode_f B)). split.
      { pose proof (cpair_bound 4 (cpair y (FOcode_f B))). lia. }
      split. { reflexivity. }
      exists y. split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      exists (FOcode_f B). split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      split. { reflexivity. }
      destruct (Nat.eqb y w) eqn:Ey.
      * left. split. { apply Nat.eqb_eq. exact Ey. } { reflexivity. }
      * right. split. { apply Nat.eqb_neq. exact Ey. }
        apply Hincl. cbn [trace1]. apply in_or_app. left.
        apply trace1_seed. reflexivity.
Qed.

Lemma trace2_ok : forall x s t L,
  incl (trace2 x s t) L ->
  forall e, In e (trace2 x s t) -> entry_ok L e.
Proof.
  intros x s t.
  induction t as [y | | a IHa | a IHa b IHb | a IHa b IHb];
    intros L Hincl e HeIn; cbn [trace2] in HeIn.
  - destruct HeIn as [<- | []].
    apply entry_ok_2. cbn [FOsubst_t FOcode_tm].
    unfold step2_sem. left.
    exists y. split.
    { pose proof (cpair_bound 0 y). lia. }
    split. { reflexivity. }
    destruct (Nat.eqb y x) eqn:Ey.
    + left. split. { apply Nat.eqb_eq. exact Ey. } { reflexivity. }
    + right. split. { apply Nat.eqb_neq. exact Ey. }
      cbn [FOcode_tm]. reflexivity.
  - destruct HeIn as [<- | []].
    apply entry_ok_2. unfold step2_sem.
    right; left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_2. cbn [FOsubst_t FOcode_tm].
      unfold step2_sem. right; right; left.
      exists (FOcode_tm a). split.
      { pose proof (cpair_bound 2 (FOcode_tm a)). lia. }
      split. { reflexivity. }
      exists (FOcode_tm (FOsubst_t x s a)). split.
      { pose proof (cpair_bound 2 (FOcode_tm (FOsubst_t x s a))). lia. }
      split.
      { apply Hincl. cbn [trace2]. apply in_or_app. left.
        apply trace2_seed. reflexivity. }
      reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHb L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_2. cbn [FOsubst_t FOcode_tm].
        unfold step2_sem. right; right; right; left.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 3 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        exists (FOcode_tm (FOsubst_t x s a)). split.
        { pose proof (cpair_bound 3
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        exists (FOcode_tm (FOsubst_t x s b)). split.
        { pose proof (cpair_bound 3
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        split.
        { apply Hincl. cbn [trace2]. apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        split.
        { apply Hincl. cbn [trace2]. apply in_or_app. right.
          apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        exists (cpair (FOcode_tm (FOsubst_t x s a))
                      (FOcode_tm (FOsubst_t x s b))).
        split.
        { pose proof (cpair_bound 3
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          lia. }
        split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHa L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHb L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_2. cbn [FOsubst_t FOcode_tm].
        unfold step2_sem. right; right; right; right.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 4 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        exists (FOcode_tm (FOsubst_t x s a)). split.
        { pose proof (cpair_bound 4
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        exists (FOcode_tm (FOsubst_t x s b)). split.
        { pose proof (cpair_bound 4
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        split.
        { apply Hincl. cbn [trace2]. apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        split.
        { apply Hincl. cbn [trace2]. apply in_or_app. right.
          apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        exists (cpair (FOcode_tm (FOsubst_t x s a))
                      (FOcode_tm (FOsubst_t x s b))).
        split.
        { pose proof (cpair_bound 4
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          lia. }
        split; reflexivity.
Qed.

Lemma trace3_ok : forall x s A L,
  incl (trace3 x s A) L ->
  forall e, In e (trace3 x s A) -> entry_ok L e.
Proof.
  intros x s A.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros L Hincl e HeIn; cbn [trace3] in HeIn.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (trace2_ok x s a L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (trace2_ok x s b L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_3. cbn [FOsubst_f FOcode_f].
        unfold step3_sem. left.
        exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
        { pose proof (cpair_bound 0 (cpair (FOcode_tm a) (FOcode_tm b))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_tm a). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        exists (FOcode_tm b). split.
        { pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia. }
        split. { reflexivity. }
        exists (FOcode_tm (FOsubst_t x s a)). split.
        { pose proof (cpair_bound 0
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        exists (FOcode_tm (FOsubst_t x s b)). split.
        { pose proof (cpair_bound 0
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          pose proof (cpair_bound (FOcode_tm (FOsubst_t x s a))
                        (FOcode_tm (FOsubst_t x s b))).
          lia. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. right.
          apply in_or_app. left.
          apply trace2_seed. reflexivity. }
        exists (cpair (FOcode_tm (FOsubst_t x s a))
                      (FOcode_tm (FOsubst_t x s b))).
        split.
        { pose proof (cpair_bound 0
            (cpair (FOcode_tm (FOsubst_t x s a))
                   (FOcode_tm (FOsubst_t x s b)))).
          lia. }
        split; reflexivity.
  - destruct HeIn as [<- | []].
    apply entry_ok_3. unfold step3_sem.
    right; left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHC L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_3. cbn [FOsubst_f FOcode_f].
        unfold step3_sem. right; right; left.
        exists (cpair (FOcode_f B) (FOcode_f C)). split.
        { pose proof (cpair_bound 2 (cpair (FOcode_f B) (FOcode_f C))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_f B). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        exists (FOcode_f C). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        split. { reflexivity. }
        exists (FOcode_f (FOsubst_f x s B)). split.
        { pose proof (cpair_bound 2
            (cpair (FOcode_f (FOsubst_f x s B))
                   (FOcode_f (FOsubst_f x s C)))).
          pose proof (cpair_bound (FOcode_f (FOsubst_f x s B))
                        (FOcode_f (FOsubst_f x s C))).
          lia. }
        exists (FOcode_f (FOsubst_f x s C)). split.
        { pose proof (cpair_bound 2
            (cpair (FOcode_f (FOsubst_f x s B))
                   (FOcode_f (FOsubst_f x s C)))).
          pose proof (cpair_bound (FOcode_f (FOsubst_f x s B))
                        (FOcode_f (FOsubst_f x s C))).
          lia. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. left.
          apply trace3_seed. reflexivity. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. right.
          apply in_or_app. left.
          apply trace3_seed. reflexivity. }
        exists (cpair (FOcode_f (FOsubst_f x s B))
                      (FOcode_f (FOsubst_f x s C))).
        split.
        { pose proof (cpair_bound 2
            (cpair (FOcode_f (FOsubst_f x s B))
                   (FOcode_f (FOsubst_f x s C)))).
          lia. }
        split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_3. cbn [FOsubst_f FOcode_f].
      unfold step3_sem. right; right; right; left.
      exists (cpair y (FOcode_f B)). split.
      { pose proof (cpair_bound 3 (cpair y (FOcode_f B))). lia. }
      split. { reflexivity. }
      exists y. split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      exists (FOcode_f B). split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      split. { reflexivity. }
      destruct (Nat.eqb y x) eqn:Ey.
      * left. split. { apply Nat.eqb_eq. exact Ey. }
        cbn [FOcode_f]. reflexivity.
      * right. split. { apply Nat.eqb_neq. exact Ey. }
        exists (FOcode_f (FOsubst_f x s B)). split.
        { cbn [FOcode_f].
          pose proof (cpair_bound 3
            (cpair y (FOcode_f (FOsubst_f x s B)))).
          pose proof (cpair_bound y (FOcode_f (FOsubst_f x s B))).
          lia. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. left.
          apply trace3_seed. reflexivity. }
        exists (cpair y (FOcode_f (FOsubst_f x s B))).
        split.
        { cbn [FOcode_f].
          pose proof (cpair_bound 3
            (cpair y (FOcode_f (FOsubst_f x s B)))).
          lia. }
        split. { reflexivity. }
        cbn [FOcode_f]. reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_3. cbn [FOsubst_f FOcode_f].
      unfold step3_sem. right; right; right; right.
      exists (cpair y (FOcode_f B)). split.
      { pose proof (cpair_bound 4 (cpair y (FOcode_f B))). lia. }
      split. { reflexivity. }
      exists y. split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      exists (FOcode_f B). split.
      { pose proof (cpair_bound y (FOcode_f B)). lia. }
      split. { reflexivity. }
      destruct (Nat.eqb y x) eqn:Ey.
      * left. split. { apply Nat.eqb_eq. exact Ey. }
        cbn [FOcode_f]. reflexivity.
      * right. split. { apply Nat.eqb_neq. exact Ey. }
        exists (FOcode_f (FOsubst_f x s B)). split.
        { cbn [FOcode_f].
          pose proof (cpair_bound 4
            (cpair y (FOcode_f (FOsubst_f x s B)))).
          pose proof (cpair_bound y (FOcode_f (FOsubst_f x s B))).
          lia. }
        split.
        { apply Hincl. cbn [trace3]. apply in_or_app. left.
          apply trace3_seed. reflexivity. }
        exists (cpair y (FOcode_f (FOsubst_f x s B))).
        split.
        { cbn [FOcode_f].
          pose proof (cpair_bound 4
            (cpair y (FOcode_f (FOsubst_f x s B)))).
          lia. }
        split. { reflexivity. }
        cbn [FOcode_f]. reflexivity.
Qed.

Lemma trace4_ok : forall x s A L,
  incl (trace4 x s A) L ->
  forall e, In e (trace4 x s A) -> entry_ok L e.
Proof.
  intros x s A.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros L Hincl e HeIn; cbn [trace4] in HeIn.
  - destruct HeIn as [<- | []].
    apply entry_ok_4. cbn [FOsubst_ok FOcode_f].
    unfold step4_sem. left.
    exists (cpair (FOcode_tm a) (FOcode_tm b)). split.
    { pose proof (cpair_bound 0 (cpair (FOcode_tm a) (FOcode_tm b))).
      lia. }
    split; reflexivity.
  - destruct HeIn as [<- | []].
    apply entry_ok_4. unfold step4_sem.
    right; left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IHB L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (IHC L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * destruct HeIn as [<- | []].
        apply entry_ok_4. cbn [FOsubst_ok FOcode_f].
        unfold step4_sem. right; right; left.
        exists (cpair (FOcode_f B) (FOcode_f C)). split.
        { pose proof (cpair_bound 2 (cpair (FOcode_f B) (FOcode_f C))).
          lia. }
        split. { reflexivity. }
        exists (FOcode_f B). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        exists (FOcode_f C). split.
        { pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia. }
        split. { reflexivity. }
        destruct (FOsubst_ok x s B) eqn:E1; cbn [andb].
        -- right. split.
           ++ apply Hincl. cbn [trace4]. apply in_or_app. left.
              apply trace4_seed. rewrite E1. reflexivity.
           ++ apply Hincl. cbn [trace4]. apply in_or_app. right.
              apply in_or_app. left.
              apply trace4_seed. reflexivity.
        -- left. split.
           ++ apply Hincl. cbn [trace4]. apply in_or_app. left.
              apply trace4_seed. rewrite E1. reflexivity.
           ++ reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (trace1_ok x B L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (trace0_ok y s L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
        -- apply (IHB L
             (incl_app_head _ _ _ _
               (incl_app_tail _ _ _ _ (incl_app_tail _ _ _ _ Hincl)))
             e HeIn).
        -- destruct HeIn as [<- | []].
           apply entry_ok_4. cbn [FOsubst_ok FOcode_f].
           unfold step4_sem. right; right; right; left.
           exists (cpair y (FOcode_f B)). split.
           { pose proof (cpair_bound 3 (cpair y (FOcode_f B))). lia. }
           split. { reflexivity. }
           exists y. split.
           { pose proof (cpair_bound y (FOcode_f B)). lia. }
           exists (FOcode_f B). split.
           { pose proof (cpair_bound y (FOcode_f B)). lia. }
           split. { reflexivity. }
           destruct (Nat.eqb y x) eqn:Eyx.
           ++ left. split. { apply Nat.eqb_eq. exact Eyx. }
              { reflexivity. }
           ++ right. split. { apply Nat.eqb_neq. exact Eyx. }
              destruct (FOfree_in x B) eqn:Ef.
              ** right. split.
                 { apply Hincl. cbn [trace4]. apply in_or_app. left.
                   apply trace1_seed. rewrite Ef. reflexivity. }
                 destruct (FOin_tm y s) eqn:Eys; cbn [negb andb].
                 --- left. split.
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace0_seed. rewrite Eys. reflexivity. }
                     { reflexivity. }
                 --- right. split.
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace0_seed. rewrite Eys. reflexivity. }
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace4_seed. reflexivity. }
              ** left. split.
                 { apply Hincl. cbn [trace4]. apply in_or_app. left.
                   apply trace1_seed. rewrite Ef. reflexivity. }
                 { reflexivity. }
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (trace1_ok x B L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
      * apply (trace0_ok y s L
          (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl)) e HeIn).
      * apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
        -- apply (IHB L
             (incl_app_head _ _ _ _
               (incl_app_tail _ _ _ _ (incl_app_tail _ _ _ _ Hincl)))
             e HeIn).
        -- destruct HeIn as [<- | []].
           apply entry_ok_4. cbn [FOsubst_ok FOcode_f].
           unfold step4_sem. right; right; right; right.
           exists (cpair y (FOcode_f B)). split.
           { pose proof (cpair_bound 4 (cpair y (FOcode_f B))). lia. }
           split. { reflexivity. }
           exists y. split.
           { pose proof (cpair_bound y (FOcode_f B)). lia. }
           exists (FOcode_f B). split.
           { pose proof (cpair_bound y (FOcode_f B)). lia. }
           split. { reflexivity. }
           destruct (Nat.eqb y x) eqn:Eyx.
           ++ left. split. { apply Nat.eqb_eq. exact Eyx. }
              { reflexivity. }
           ++ right. split. { apply Nat.eqb_neq. exact Eyx. }
              destruct (FOfree_in x B) eqn:Ef.
              ** right. split.
                 { apply Hincl. cbn [trace4]. apply in_or_app. left.
                   apply trace1_seed. rewrite Ef. reflexivity. }
                 destruct (FOin_tm y s) eqn:Eys; cbn [negb andb].
                 --- left. split.
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace0_seed. rewrite Eys. reflexivity. }
                     { reflexivity. }
                 --- right. split.
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace0_seed. rewrite Eys. reflexivity. }
                     { apply Hincl. cbn [trace4].
                       apply in_or_app. right.
                       apply in_or_app. right.
                       apply in_or_app. left.
                       apply trace4_seed. reflexivity. }
              ** left. split.
                 { apply Hincl. cbn [trace4]. apply in_or_app. left.
                   apply trace1_seed. rewrite Ef. reflexivity. }
                 { reflexivity. }
Qed.

Lemma trace5_ok : forall k L,
  incl (trace5 k) L ->
  forall e, In e (trace5 k) -> entry_ok L e.
Proof.
  intros k. induction k as [|k' IH]; intros L Hincl e HeIn;
    cbn [trace5] in HeIn.
  - destruct HeIn as [<- | []].
    apply entry_ok_5. unfold step5_sem.
    left. split; reflexivity.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn | HeIn].
    + apply (IH L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + destruct HeIn as [<- | []].
      apply entry_ok_5. cbn [FOnumeral FOcode_tm].
      unfold step5_sem. right.
      exists k'. split. { lia. }
      split. { reflexivity. }
      exists (FOcode_tm (FOnumeral k')). split.
      { pose proof (cpair_bound 2 (FOcode_tm (FOnumeral k'))). lia. }
      split.
      { apply Hincl. cbn [trace5]. apply in_or_app. left.
        apply trace5_seed. reflexivity. }
      reflexivity.
Qed.

(** ** Realizing a justified entry list as a beta-coded table.

    [beta_complete] codes the five projected tracks; membership in the
    list and membership in the coded table coincide pointwise, so the
    per-entry justifications transport across the step-semantics
    extensionality lemmas, giving table validity at every position. *)

Definition TEd0 : TEntry := mkTE 0 0 0 0 0.

Theorem table_realize : forall L,
  (forall e, In e L -> entry_ok L e) ->
  exists vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr,
    (forall tg a1 a2 a3 r,
       listL L tg a1 a2 a3 r <->
       tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr (length L)
         tg a1 a2 a3 r) /\
    (forall j, j < length L ->
       dispatch_sem
         (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr (length L))
         vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j).
Proof.
  intros L Hok.
  destruct (beta_complete (map te_tg L)) as [vct [vdt Hbt]].
  destruct (beta_complete (map te_a1 L)) as [vc1 [vd1 Hb1]].
  destruct (beta_complete (map te_a2 L)) as [vc2 [vd2 Hb2]].
  destruct (beta_complete (map te_a3 L)) as [vc3 [vd3 Hb3]].
  destruct (beta_complete (map te_r L)) as [vcr [vdr Hbr]].
  assert (Qt : forall i, i < length L ->
      beta vct vdt i = te_tg (nth i L TEd0)).
  { intros i Hi. rewrite <- (map_nth te_tg L TEd0 i).
    apply Hbt. rewrite length_map. exact Hi. }
  assert (Q1 : forall i, i < length L ->
      beta vc1 vd1 i = te_a1 (nth i L TEd0)).
  { intros i Hi. rewrite <- (map_nth te_a1 L TEd0 i).
    apply Hb1. rewrite length_map. exact Hi. }
  assert (Q2 : forall i, i < length L ->
      beta vc2 vd2 i = te_a2 (nth i L TEd0)).
  { intros i Hi. rewrite <- (map_nth te_a2 L TEd0 i).
    apply Hb2. rewrite length_map. exact Hi. }
  assert (Q3 : forall i, i < length L ->
      beta vc3 vd3 i = te_a3 (nth i L TEd0)).
  { intros i Hi. rewrite <- (map_nth te_a3 L TEd0 i).
    apply Hb3. rewrite length_map. exact Hi. }
  assert (Qr : forall i, i < length L ->
      beta vcr vdr i = te_r (nth i L TEd0)).
  { intros i Hi. rewrite <- (map_nth te_r L TEd0 i).
    apply Hbr. rewrite length_map. exact Hi. }
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr.
  assert (HIFF : forall tg a1 a2 a3 r,
      listL L tg a1 a2 a3 r <->
      tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr (length L)
        tg a1 a2 a3 r).
  { intros tg a1 a2 a3 r. split.
    - intro HIn. unfold listL in HIn.
      destruct (In_nth L _ TEd0 HIn) as [j [Hj Hnth]].
      exists j. split; [exact Hj|].
      rewrite (Qt j Hj), (Q1 j Hj), (Q2 j Hj), (Q3 j Hj), (Qr j Hj).
      rewrite Hnth. cbn [te_tg te_a1 te_a2 te_a3 te_r].
      repeat split; reflexivity.
    - intros [j [Hj [Et [E1 [E2 [E3 Er]]]]]].
      unfold listL.
      rewrite (Qt j Hj) in Et. rewrite (Q1 j Hj) in E1.
      rewrite (Q2 j Hj) in E2. rewrite (Q3 j Hj) in E3.
      rewrite (Qr j Hj) in Er.
      assert (Hnth : nth j L TEd0 = mkTE tg a1 a2 a3 r).
      { destruct (nth j L TEd0) as [g b1 b2 b3 br].
        cbn [te_tg te_a1 te_a2 te_a3 te_r] in Et, E1, E2, E3, Er.
        subst. reflexivity. }
      rewrite <- Hnth. apply nth_In. exact Hj. }
  split; [exact HIFF|].
  intros j Hj.
  pose proof (Hok (nth j L TEd0) (nth_In L TEd0 Hj)) as He.
  unfold dispatch_sem.
  exists (te_tg (nth j L TEd0)). split.
  { rewrite <- (Qt j Hj). unfold beta.
    pose proof (Nat.Div0.mod_le vct (vdt * S j + 1)). lia. }
  exists (te_a1 (nth j L TEd0)). split.
  { rewrite <- (Q1 j Hj). unfold beta.
    pose proof (Nat.Div0.mod_le vc1 (vd1 * S j + 1)). lia. }
  exists (te_a2 (nth j L TEd0)). split.
  { rewrite <- (Q2 j Hj). unfold beta.
    pose proof (Nat.Div0.mod_le vc2 (vd2 * S j + 1)). lia. }
  exists (te_a3 (nth j L TEd0)). split.
  { rewrite <- (Q3 j Hj). unfold beta.
    pose proof (Nat.Div0.mod_le vc3 (vd3 * S j + 1)). lia. }
  exists (te_r (nth j L TEd0)). split.
  { rewrite <- (Qr j Hj). unfold beta.
    pose proof (Nat.Div0.mod_le vcr (vdr * S j + 1)). lia. }
  split. { exact (Qt j Hj). }
  split. { exact (Q1 j Hj). }
  split. { exact (Q2 j Hj). }
  split. { exact (Q3 j Hj). }
  split. { exact (Qr j Hj). }
  destruct (nth j L TEd0) as [tg a1 a2 a3 r] eqn:Ee.
  cbn [te_tg te_a1 te_a2 te_a3 te_r].
  destruct tg as [|[|[|[|[|[|t7]]]]]].
  - left. split. { reflexivity. }
    exact (proj1 (step0_sem_ext (listL L) _ a1 a2 r HIFF) He).
  - right; left. split. { reflexivity. }
    exact (proj1 (step1_sem_ext (listL L) _ a1 a2 r HIFF) He).
  - right; right; left. split. { reflexivity. }
    exact (proj1 (step2_sem_ext (listL L) _ a1 a2 a3 r HIFF) He).
  - right; right; right; left. split. { reflexivity. }
    exact (proj1 (step3_sem_ext (listL L) _ a1 a2 a3 r HIFF) He).
  - right; right; right; right; left. split. { reflexivity. }
    exact (proj1 (step4_sem_ext (listL L) _ a1 a2 a3 r HIFF) He).
  - right; right; right; right; right. split. { reflexivity. }
    exact (proj1 (step5_sem_ext (listL L) _ a1 r HIFF) He).
  - exfalso. exact He.
Qed.

(** ** Satisfaction of the provability sentence.

    [provmat_sem cores u f]: some master table validates every
    dispatch position, some derivation pair of tracks ends at the
    target code [f], and every derivation position carries a
    justification accepted against the table, the core list, and the
    self template code [u].  The three lemmas walk the conjunction,
    the sixteen-variable prefix, and the two numeral substitutions. *)

Definition provmat_sem (cores : list nat) (u f : nat) : Prop :=
  exists vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen vcs vds vcj vdj
    vdlen,
    (forall vj, vj < vlen ->
       dispatch_sem
         (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
         vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vj) /\
    (exists m, vdlen = S m /\ beta vcs vds m = f) /\
    (forall ii, ii < vdlen ->
       justck_sem
         (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
         cores u vcs vds vcj vdj ii) /\
    (forall ii, ii < vdlen ->
       exists rg,
         tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen
           3 (S (beta vcs vds ii)) 0 (beta vcs vds ii) rg).

Lemma FOsat_FOGUARDC : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm i < B ->
  (FOsat e (FOGUARDC B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i)
   <->
   exists rg,
     tblL (FOeval e ct) (FOeval e dt) (FOeval e c1) (FOeval e d1)
       (FOeval e c2) (FOeval e d2) (FOeval e c3) (FOeval e d3)
       (FOeval e cr) (FOeval e dr) (FOeval e len)
       3 (S (beta (FOeval e cs) (FOeval e ds) (FOeval e i))) 0
       (beta (FOeval e cs) (FOeval e ds) (FOeval e i)) rg).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i Htb Hcs Hds Hi.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb8 : tbl_below (B+8) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc cs) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB6 : FOin_tm (B+6) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB6 : FOin_tm (S (B+6)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (H3m : FOmax_var_tm (FOnumeral 3) < B+8)
    by (rewrite FOmax_var_numeral; lia).
  assert (HSvB : FOmax_var_tm (FOSucc (FOVar B)) < B+8) by (cbn; lia).
  assert (HzB : FOmax_var_tm FOZero < B+8) by (cbn; lia).
  assert (HvB : FOmax_var_tm (FOVar B) < B+8) by (cbn; lia).
  assert (HvB6 : FOmax_var_tm (FOVar (B+6)) < B+8) by (cbn; lia).
  unfold FOGUARDC.
  rewrite (FOsat_FOBexC e B (FOSucc cs) _ HinB HinSB).
  split.
  - intros [vd [Hvdb Hb1]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb1.
    destruct Hb1 as [Hbeta Hb2].
    set (e1 := FOupdate e B vd) in *.
    apply (proj1 (FOsat_FObetaF e1 (B+2) cs ds i (FOVar B)
                    ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(cbn; lia))) in Hbeta.
    cbn [FOeval] in Hbeta.
    unfold e1 in Hbeta.
    rewrite (FOeval_update_above cs e B vd Hcs) in Hbeta.
    rewrite (FOeval_update_above ds e B vd Hds) in Hbeta.
    rewrite (FOeval_update_above i e B vd Hi) in Hbeta.
    rewrite (FOupdate_eq _ _ _) in Hbeta.
    apply (proj1 (FOsat_FOBexC _ (B+6) (FOSucc cr) _ HinB6 HinSB6))
      in Hb2.
    destruct Hb2 as [rg [Hrgb Hlk]].
    set (e2 := FOupdate e1 (B+6) rg) in *.
    apply (proj1 (FOsat_FOlookup e2 (B+8) ct dt c1 d1 c2 d2 c3 d3 cr
                    dr len (FOnumeral 3) (FOSucc (FOVar B)) FOZero
                    (FOVar B) (FOVar (B+6))
                    Htb8 H3m HSvB HzB HvB HvB6)) in Hlk.
    destruct Hlk as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e2 t = FOeval e t).
    { intros t Ht. unfold e2, e1.
      rewrite (FOeval_update_above t _ (B+6) rg ltac:(lia)).
      exact (FOeval_update_above t e B vd Ht). }
    assert (EvB : e2 B = vd).
    { unfold e2, e1.
      rewrite (FOupdate_neq _ (B+6) rg B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e2 (B+6) = rg).
    { unfold e2. apply FOupdate_eq. }
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4, Hf5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6 in Hf5.
    rewrite <- Hbeta in Hf2, Hf4.
    exists rg, j.
    repeat split; assumption.
  - intros [rg Hrow].
    destruct Hrow as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    set (vd := beta (FOeval e cs) (FOeval e ds) (FOeval e i)) in *.
    exists vd. split.
    { cbn [FOeval]. unfold vd, beta.
      pose proof (Nat.Div0.mod_le (FOeval e cs)
        ((FOeval e ds) * S (FOeval e i) + 1)). lia. }
    set (e1 := FOupdate e B vd).
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF e1 (B+2) cs ds i (FOVar B)
                      ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(cbn; lia))).
      cbn [FOeval].
      unfold e1.
      rewrite (FOeval_update_above cs e B vd Hcs).
      rewrite (FOeval_update_above ds e B vd Hds).
      rewrite (FOeval_update_above i e B vd Hi).
      rewrite (FOupdate_eq _ _ _).
      reflexivity. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc cr) _ HinB6 HinSB6).
    exists rg. split.
    { cbn [FOeval]. unfold e1.
      rewrite (FOeval_update_above cr e B vd Hcr).
      pose proof (Nat.Div0.mod_le (FOeval e cr)
        ((FOeval e dr) * S j + 1)) as Hmle.
      unfold beta in Hf5. lia. }
    set (e2 := FOupdate e1 (B+6) rg).
    apply (proj2 (FOsat_FOlookup e2 (B+8) ct dt c1 d1 c2 d2 c3 d3 cr
                    dr len (FOnumeral 3) (FOSucc (FOVar B)) FOZero
                    (FOVar B) (FOVar (B+6))
                    Htb8 H3m HSvB HzB HvB HvB6)).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e2 t = FOeval e t).
    { intros t Ht. unfold e2, e1.
      rewrite (FOeval_update_above t _ (B+6) rg ltac:(lia)).
      exact (FOeval_update_above t e B vd Ht). }
    assert (EvB : e2 B = vd).
    { unfold e2, e1.
      rewrite (FOupdate_neq _ (B+6) rg B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e2 (B+6) = rg).
    { unfold e2. apply FOupdate_eq. }
    exists j. split.
    { rewrite (Hstab len Hlen). exact Hj. }
    split.
    { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
      exact Hf1. }
    split.
    { cbn [FOeval]. rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB.
      exact Hf2. }
    split.
    { cbn [FOeval]. rewrite (Hstab c2 Hc2), (Hstab d2 Hd2').
      exact Hf3. }
    split.
    { cbn [FOeval]. rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB.
      exact Hf4. }
    cbn [FOeval]. rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6.
    exact Hf5.
Qed.

Lemma FOsat_FOPRDER : forall e cores,
  (FOsat e (FOPRDER cores) <->
   ((forall vj, vj < e 12 ->
       dispatch_sem
         (tblL (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
            (e 10) (e 11) (e 12))
         (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9) (e 10)
         (e 11) vj) /\
    (exists m, e 17 = S m /\ beta (e 13) (e 14) m = e 1) /\
    (forall ii, ii < e 17 ->
       justck_sem
         (tblL (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
            (e 10) (e 11) (e 12))
         cores (e 0) (e 13) (e 14) (e 15) (e 16) ii) /\
    (forall ii, ii < e 17 ->
       exists rg,
         tblL (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
           (e 10) (e 11) (e 12)
           3 (S (beta (e 13) (e 14) ii)) 0 (beta (e 13) (e 14) ii)
           rg))).
Proof.
  intros e cores.
  assert (Htb18 : tbl_below 18 (FOVar 2) (FOVar 3) (FOVar 4)
            (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
            (FOVar 10) (FOVar 11) (FOVar 12))
    by (unfold tbl_below; cbn; lia).
  assert (Htb20 : tbl_below 20 (FOVar 2) (FOVar 3) (FOVar 4)
            (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
            (FOVar 10) (FOVar 11) (FOVar 12))
    by (unfold tbl_below; cbn; lia).
  assert (Hin18 : FOin_tm 18 (FOVar 17) = false) by reflexivity.
  assert (HinS18 : FOin_tm 19 (FOVar 17) = false) by reflexivity.
  unfold FOPRDER.
  split.
  - intro H.
    apply (proj1 (FOsat_FOAnd _ _ _)) in H.
    destruct H as [Htv H].
    apply (proj1 (FOsat_FOAnd _ _ _)) in H.
    destruct H as [Hmid H].
    apply (proj1 (FOsat_FOAnd _ _ _)) in H.
    destruct H as [Hball Hguard].
    split.
    { exact (proj1 (FOsat_FOTBLVALID e 18 (FOVar 2) (FOVar 3)
                      (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7)
                      (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                      (FOVar 12) Htb18) Htv). }
    split.
    { rewrite (FOsat_FOBexC e 18 (FOVar 17) _ Hin18 HinS18) in Hmid.
      destruct Hmid as [m [Hm Hbody]].
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
      destruct Hbody as [HEq Hbeta].
      apply (proj1 (FOsat_FObetaF _ 20 (FOVar 13) (FOVar 14)
                      (FOVar 18) (FOVar 1) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))) in Hbeta.
      exists m. split; [exact HEq | exact Hbeta]. }
    split.
    { intros ii Hii.
      rewrite (FOsat_FOBallC e 18 (FOVar 17) _ Hin18 HinS18) in Hball.
      pose proof (Hball ii Hii) as HJ.
      apply (proj1 (FOsat_FOJUSTCK _ 20 cores (FOVar 2) (FOVar 3)
                      (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8)
                      (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                      (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16)
                      (FOVar 18) Htb20 ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))) in HJ.
      exact HJ. }
    intros ii Hii.
    rewrite (FOsat_FOBallC e 18 (FOVar 17) _ Hin18 HinS18) in Hguard.
    pose proof (Hguard ii Hii) as HG.
    apply (proj1 (FOsat_FOGUARDC _ 20 (FOVar 2) (FOVar 3) (FOVar 4)
                    (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
                    (FOVar 10) (FOVar 11) (FOVar 12) (FOVar 13)
                    (FOVar 14) (FOVar 18) Htb20 ltac:(cbn; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))) in HG.
    exact HG.
  - intros [Htv [Hmid [Hball Hguard]]].
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { exact (proj2 (FOsat_FOTBLVALID e 18 (FOVar 2) (FOVar 3)
                      (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7)
                      (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                      (FOVar 12) Htb18) Htv). }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { rewrite (FOsat_FOBexC e 18 (FOVar 17) _ Hin18 HinS18).
      destruct Hmid as [m [Hm Hbeta]].
      exists m. split; [cbn; lia|].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      { exact Hm. }
      apply (proj2 (FOsat_FObetaF _ 20 (FOVar 13) (FOVar 14)
                      (FOVar 18) (FOVar 1) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      exact Hbeta. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { rewrite (FOsat_FOBallC e 18 (FOVar 17) _ Hin18 HinS18).
      intros w Hw.
      apply (proj2 (FOsat_FOJUSTCK _ 20 cores (FOVar 2) (FOVar 3)
                      (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8)
                      (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                      (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16)
                      (FOVar 18) Htb20 ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; lia))).
      exact (Hball w Hw). }
    rewrite (FOsat_FOBallC e 18 (FOVar 17) _ Hin18 HinS18).
    intros w Hw.
    apply (proj2 (FOsat_FOGUARDC _ 20 (FOVar 2) (FOVar 3) (FOVar 4)
                    (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
                    (FOVar 10) (FOVar 11) (FOVar 12) (FOVar 13)
                    (FOVar 14) (FOVar 18) Htb20 ltac:(cbn; lia)
                    ltac:(cbn; lia) ltac:(cbn; lia))).
    exact (Hguard w Hw).
Qed.

Lemma FOsat_FOPRMAT : forall e cores,
  (FOsat e (FOPRMAT cores) <-> provmat_sem cores (e 0) (e 1)).
Proof.
  intros e cores.
  unfold FOPRMAT, provmat_sem.
  cbn [FOsat].
  split.
  - intros [v2 [v3 [v4 [v5 [v6 [v7 [v8 [v9 [v10 [v11 [v12 [v13 [v14
      [v15 [v16 [v17 H]]]]]]]]]]]]]]]].
    apply (proj1 (FOsat_FOPRDER _ cores)) in H.
    exists v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
      v15, v16, v17.
    exact H.
  - intros [v2 [v3 [v4 [v5 [v6 [v7 [v8 [v9 [v10 [v11 [v12 [v13 [v14
      [v15 [v16 [v17 H]]]]]]]]]]]]]]]].
    exists v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14,
      v15, v16, v17.
    apply (proj2 (FOsat_FOPRDER _ cores)).
    exact H.
Qed.

Lemma FOsat_FOProvSentence : forall e n A,
  (FOsat e (FOProvSentence n A) <->
   provmat_sem (FOPrCores n)
     (FOcode_f (FOPRMAT (FOPrCores n))) (FOcode_f A)).
Proof.
  intros e n A.
  unfold FOProvSentence.
  rewrite (FOsat_subst_num _ 1 (FOcode_f A) e).
  rewrite (FOsat_subst_num _ 0
             (FOcode_f (FOPRMAT (FOPrCores n))) _).
  rewrite (FOsat_FOPRMAT _ (FOPrCores n)).
  reflexivity.
Qed.

(** ** Membership and inversion for the derivability recognizers,
    and the indexed cores. *)

Lemma d2s_sem_of : forall L cores c d,
  In c cores -> d2one_sem L c d -> d2s_sem L cores d.
Proof.
  intros L cores c d HIn Hr. revert HIn.
  induction cores as [|c0 rest IH]; cbn [d2s_sem]; intros HIn.
  - destruct HIn.
  - destruct HIn as [->|HIn].
    + left. exact Hr.
    + right. exact (IH HIn).
Qed.

Lemma d2s_sem_in : forall L cores d,
  d2s_sem L cores d -> exists c, In c cores /\ d2one_sem L c d.
Proof.
  intros L cores d.
  induction cores as [|c0 rest IH]; cbn [d2s_sem].
  - intros [].
  - intros [H|H].
    + exists c0. split; [left; reflexivity|exact H].
    + destruct (IH H) as [c [Hin Hr]].
      exists c. split; [right; exact Hin|exact Hr].
Qed.

Lemma d3s_sem_of : forall L cores c d,
  In c cores -> d3one_sem L c d -> d3s_sem L cores d.
Proof.
  intros L cores c d HIn Hr. revert HIn.
  induction cores as [|c0 rest IH]; cbn [d3s_sem]; intros HIn.
  - destruct HIn.
  - destruct HIn as [->|HIn].
    + left. exact Hr.
    + right. exact (IH HIn).
Qed.

Lemma d3s_sem_in : forall L cores d,
  d3s_sem L cores d -> exists c, In c cores /\ d3one_sem L c d.
Proof.
  intros L cores d.
  induction cores as [|c0 rest IH]; cbn [d3s_sem].
  - intros [].
  - intros [H|H].
    + exists c0. split; [left; reflexivity|exact H].
    + destruct (IH H) as [c [Hin Hr]].
      exists c. split; [right; exact Hin|exact Hr].
Qed.

Lemma dmons1_sem_of : forall L c cs c' d,
  In c' cs -> dmonone_sem L c c' d -> dmons1_sem L c cs d.
Proof.
  intros L c cs c' d HIn Hr. revert HIn.
  induction cs as [|c0 rest IH]; cbn [dmons1_sem]; intros HIn.
  - destruct HIn.
  - destruct HIn as [->|HIn].
    + left. exact Hr.
    + right. exact (IH HIn).
Qed.

Lemma dmons1_sem_in : forall L c cs d,
  dmons1_sem L c cs d ->
  exists c', In c' cs /\ dmonone_sem L c c' d.
Proof.
  intros L c cs d.
  induction cs as [|c0 rest IH]; cbn [dmons1_sem].
  - intros [].
  - intros [H|H].
    + exists c0. split; [left; reflexivity|exact H].
    + destruct (IH H) as [c' [Hin Hr]].
      exists c'. split; [right; exact Hin|exact Hr].
Qed.

Lemma dmons_sem_of_nth : forall L cores i i' c c' d,
  nth_error cores i = Some c ->
  nth_error cores i' = Some c' ->
  i <= i' ->
  dmonone_sem L c c' d ->
  dmons_sem L cores d.
Proof.
  intros L cores. revert L.
  induction cores as [|c0 rest IH];
    intros L i i' c c' d Hi Hi' Hle Hr.
  - destruct i; discriminate.
  - cbn [dmons_sem].
    destruct i as [|i0].
    + cbn in Hi. injection Hi as <-.
      left.
      apply (dmons1_sem_of L c0 (c0 :: rest) c' d); [|exact Hr].
      exact (nth_error_In _ _ Hi').
    + destruct i' as [|i0']; [lia|].
      cbn in Hi, Hi'.
      right.
      exact (IH L i0 i0' c c' d Hi Hi' ltac:(lia) Hr).
Qed.

Lemma dmons_sem_in_nth : forall L cores d,
  dmons_sem L cores d ->
  exists i i' c c', i <= i' /\
    nth_error cores i = Some c /\
    nth_error cores i' = Some c' /\
    dmonone_sem L c c' d.
Proof.
  intros L cores d.
  induction cores as [|c0 rest IH]; cbn [dmons_sem].
  - intros [].
  - intros [H|H].
    + destruct (dmons1_sem_in L c0 (c0 :: rest) d H)
        as [c' [HIn Hr]].
      destruct (In_nth_error _ _ HIn) as [i' Hi'].
      exists 0, i', c0, c'.
      split; [lia|]. split; [reflexivity|].
      split; [exact Hi'|exact Hr].
    + destruct (IH H) as [i [i' [c [c' [Hle [Hi [Hi' Hr]]]]]]].
      exists (S i), (S i'), c, c'.
      split; [lia|]. split; [exact Hi|].
      split; [exact Hi'|exact Hr].
Qed.

Lemma FOPrCores_length : forall n, length (FOPrCores n) = n.
Proof.
  induction n as [|n IH]; cbn [FOPrCores].
  - reflexivity.
  - rewrite length_app, IH. cbn [length]. lia.
Qed.

Lemma FOPrCores_nth : forall n k c,
  nth_error (FOPrCores n) k = Some c ->
  k < n /\
  c = FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
        (FOPRMAT (FOPrCores k))).
Proof.
  induction n as [|n IH]; intros k c Hc; cbn [FOPrCores] in Hc.
  - destruct k; discriminate.
  - destruct (Nat.lt_ge_cases k n) as [Hk|Hk].
    + rewrite nth_error_app1 in Hc
        by (rewrite FOPrCores_length; exact Hk).
      destruct (IH k c Hc) as [Hk' Hc'].
      split; [lia|exact Hc'].
    + rewrite nth_error_app2 in Hc
        by (rewrite FOPrCores_length; exact Hk).
      rewrite FOPrCores_length in Hc.
      destruct (Nat.eq_dec k n) as [->|Hne].
      * rewrite Nat.sub_diag in Hc. cbn [nth_error] in Hc.
        apply (f_equal (fun o => match o with
                                 | Some z => z
                                 | None => 0 end)) in Hc.
        split; [lia|exact (eq_sym Hc)].
      * destruct (k - n) as [|m] eqn:Em; [lia|].
        cbn [nth_error] in Hc. destruct m; cbn [nth_error] in Hc;
          discriminate.
Qed.

Lemma FOPrCores_nth_of : forall n k,
  k < n ->
  nth_error (FOPrCores n) k
  = Some (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
            (FOPRMAT (FOPrCores k)))).
Proof.
  induction n as [|n IH]; intros k Hk; [lia|].
  cbn [FOPrCores].
  destruct (Nat.lt_ge_cases k n) as [Hkn|Hkn].
  - rewrite nth_error_app1
      by (rewrite FOPrCores_length; exact Hkn).
    exact (IH k Hkn).
  - assert (k = n) by lia. subst k.
    rewrite nth_error_app2
      by (rewrite FOPrCores_length; lia).
    rewrite FOPrCores_length, Nat.sub_diag.
    reflexivity.
Qed.

(** ** Decoding an accepted matrix into a tower derivation.

    With the entry-code guard, every track entry of an accepted
    derivation is a genuine formula code, so a strong induction over
    positions converts each justified entry into an [FOProvesTn]
    derivation: shape disjuncts decode through the [FOdecode] shape
    equations, table rows convert through [tbl_sound]'s per-tag
    specification, and the substitution witness supplies the
    instantiating term for the quantifier axioms. *)

Lemma FOPrCores_in : forall n c,
  In c (FOPrCores n) ->
  exists k, k < n /\
    c = FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                    (FOPRMAT (FOPrCores k))).
Proof.
  induction n as [|n IH]; intros c Hc; cbn [FOPrCores] in Hc.
  - destruct Hc.
  - apply in_app_or in Hc. destruct Hc as [Hc|Hc].
    + destruct (IH c Hc) as [k [Hk Hck]].
      exists k. split; [lia|exact Hck].
    + destruct Hc as [<-|[]].
      exists n. split; [lia|reflexivity].
Qed.

Lemma refls_sem_in : forall L cores d,
  refls_sem L cores d ->
  exists c, In c cores /\ refl_sem L c d.
Proof.
  intros L cores d.
  induction cores as [|c0 rest IH]; cbn [refls_sem].
  - intros [].
  - intros [H|H].
    + exists c0. split; [left; reflexivity|exact H].
    + destruct (IH H) as [c [Hin Hr]].
      exists c. split; [right; exact Hin|exact Hr].
Qed.

Ltac decode_shape H :=
  do 3 (rewrite ?FOdecode_f_impl, ?FOdecode_f_eq,
    ?FOdecode_f_false, ?FOdecode_f_forall, ?FOdecode_f_exists,
    ?FOdecode_tm_succ, ?FOdecode_tm_plus, ?FOdecode_tm_mult,
    ?FOdecode_tm_var, ?FOdecode_tm_zero in H).

Theorem provmat_decode : forall n A,
  provmat_sem (FOPrCores n) (FOcode_f (FOPRMAT (FOPrCores n)))
    (FOcode_f A) ->
  FOProvesTn n A.
Proof.
  intros n A Hpm.
  destruct Hpm as [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr
    [vlen [vcs [vds [vcj [vdj [vdlen
    [Hdisp [Hlast [Hjust Hguard]]]]]]]]]]]]]]]]]]].
  assert (MAIN : forall m i, i < m -> i < vdlen ->
      forall B, beta vcs vds i = FOcode_f B -> FOProvesTn n B).
  { induction m as [|m IHm].
    { intros; lia. }
    intros i Him Hivd B HA.
    pose proof (Hjust i Hivd) as HJ.
    unfold justck_sem in HJ.
    destruct HJ as [vd [vj [tg [pl [Hvd [Hvj [Hcpv Hsw]]]]]]].
    assert (Evd : vd = FOcode_f B) by congruence.
    clear Hvd. subst vd.
    destruct Hsw as
      [[_ Hth]|[[_ Hlog]|[[_ Hj2]|[[_ Hj3]|[[_ Hj4]|[[_ Hj5]
        |[[_ Hj6]|[[_ Hj7]|[[_ Hj8]|[[_ Hj9]|[_ Hj10]]]]]]]]]]].
    - (* theory axiom *)
      unfold thax_sem in Hth. destruct Hth as [Haxq|Hrefl].
      + unfold axq_sem in Haxq.
        destruct Haxq as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|Hq]]]]]].
        * destruct Hq as [a [b Hsh]].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_S_inj.
        * destruct Hq as [a Hsh].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_S_nonzero.
        * destruct Hq as [x Hsh].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_zero_or_succ.
        * destruct Hq as [a Hsh].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_plus_zero.
        * destruct Hq as [a [b Hsh]].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_plus_succ.
        * destruct Hq as [a Hsh].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_mult_zero.
        * destruct Hq as [a [b Hsh]].
          pose proof (FOdecode_code_f B) as HD.
          rewrite Hsh in HD. decode_shape HD.
          rewrite <- HD.
          apply FOProvesTn_ax, FOAx_RQ, RQ_mult_succ.
      + apply refls_sem_in in Hrefl.
        destruct Hrefl as [c [HcIn Hrf]].
        destruct (FOPrCores_in n c HcIn) as [k [Hk Hc]].
        unfold refl_sem in Hrf.
        destruct Hrf as [aa [na [p [H5 [H3 Hsh]]]]].
        destruct B as [a0 b0| |A1 A2|y0 B0|y0 B0];
          cbn [FOcode_f] in Hsh;
          apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
          try discriminate Esh.
        apply cpair_inj in Hsh. destruct Hsh as [Hp Ha].
        subst p aa.
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      5 (FOcode_f A2) 0 0 na H5) as M5.
        cbn [mspec] in M5.
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      3 1 na c (FOcode_f A1) H3) as M3.
        cbn [mspec] in M3.
        specialize (M3 (FOnumeral (FOcode_f A2))
          (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
             (FOPRMAT (FOPrCores k))) M5 Hc).
        rewrite FOsubst_f_num in M3.
        apply FOcode_f_inj in M3.
        subst A1.
        apply FOProvesTn_ax.
        exact (FOAx_Refl n k A2 Hk).
    - (* logical axiom *)
      unfold logax_sem in Hlog.
      destruct Hlog as
        [HL|[HL|[HL|[HL|[HL|[HL|[HL|[HL|[HL|[HL|[HL|HL]]]]]]]]]]].
      + destruct HL as [P [Q Hsh]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_K.
      + destruct HL as [P [Q [R Hsh]]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_S.
      + destruct HL as [P Hsh].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_DN.
      + destruct HL as [aq Hsh].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_EqRefl.
      + destruct HL as [aq [bq Hsh]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_EqSym.
      + destruct HL as [aq [bq [cq Hsh]]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_EqTrans.
      + destruct HL as [aq [bq Hsh]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_CongS.
      + destruct HL as [aq [bq [cq [dq Hsh]]]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_CongPlus.
      + destruct HL as [aq [bq [cq [dq Hsh]]]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_CongMult.
      + destruct HL as [x [P [Q [Hsh HLrow]]]].
        destruct B as [a0 b0| |A1 A2|y0 B0|y0 B0];
          cbn [FOcode_f] in Hsh;
          apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
          try discriminate Esh.
        apply cpair_inj in Hsh. destruct Hsh as [Hsh1 Hsh2].
        destruct A1 as [a0 b0| |C1 C2|y1 B1|y1 B1];
          cbn [FOcode_f] in Hsh1;
          apply cpair_inj in Hsh1; destruct Hsh1 as [Esh1 Hsh1];
          try discriminate Esh1.
        apply cpair_inj in Hsh1. destruct Hsh1 as [Ey1 Hsh1].
        subst y1.
        destruct B1 as [a0 b0| |P1 Q1|y2 B2|y2 B2];
          cbn [FOcode_f] in Hsh1;
          apply cpair_inj in Hsh1; destruct Hsh1 as [Esh1b Hsh1];
          try discriminate Esh1b.
        apply cpair_inj in Hsh1. destruct Hsh1 as [HP HQ].
        subst P Q.
        destruct A2 as [a0 b0| |C1 C2|y3 B3|y3 B3];
          cbn [FOcode_f] in Hsh2;
          apply cpair_inj in Hsh2; destruct Hsh2 as [Esh2 Hsh2];
          try discriminate Esh2.
        apply cpair_inj in Hsh2. destruct Hsh2 as [Hsh2a Hsh2b].
        destruct C1 as [a0 b0| |D1 D2|y4 B4|y4 B4];
          cbn [FOcode_f] in Hsh2a;
          apply cpair_inj in Hsh2a; destruct Hsh2a as [Esh2a Hsh2a];
          try discriminate Esh2a.
        apply cpair_inj in Hsh2a. destruct Hsh2a as [Ey4 Hsh2a].
        subst y4.
        apply FOcode_f_inj in Hsh2a. subst B4.
        apply FOcode_f_inj in Hsh2b. subst C2.
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      1 x (FOcode_f Q1) 0 0 HLrow) as M1.
        cbn [mspec] in M1.
        specialize (M1 Q1 eq_refl).
        destruct (FOfree_in x Q1) eqn:EF; [discriminate M1|].
        apply FOProvesTn_ExElim. exact EF.
      + destruct HL as [x [P [Q Hsh]]].
        pose proof (FOdecode_code_f B) as HD.
        rewrite Hsh in HD. decode_shape HD.
        rewrite <- HD. apply FOProvesTn_AllK.
      + destruct HL as [x [P [Q [Hsh HLrow]]]].
        destruct B as [a0 b0| |A1 A2|y0 B0|y0 B0];
          cbn [FOcode_f] in Hsh;
          apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
          try discriminate Esh.
        apply cpair_inj in Hsh. destruct Hsh as [Hsh1 Hsh2].
        destruct A1 as [a0 b0| |C1 C2|y1 B1|y1 B1];
          cbn [FOcode_f] in Hsh1;
          apply cpair_inj in Hsh1; destruct Hsh1 as [Esh1 Hsh1];
          try discriminate Esh1.
        apply cpair_inj in Hsh1. destruct Hsh1 as [Ey1 Hsh1].
        subst y1.
        destruct B1 as [a0 b0| |P1 Q1|y2 B2|y2 B2];
          cbn [FOcode_f] in Hsh1;
          apply cpair_inj in Hsh1; destruct Hsh1 as [Esh1b Hsh1];
          try discriminate Esh1b.
        apply cpair_inj in Hsh1. destruct Hsh1 as [HP HQ].
        subst P Q.
        destruct A2 as [a0 b0| |C1 C2|y3 B3|y3 B3];
          cbn [FOcode_f] in Hsh2;
          apply cpair_inj in Hsh2; destruct Hsh2 as [Esh2 Hsh2];
          try discriminate Esh2.
        apply cpair_inj in Hsh2. destruct Hsh2 as [Hsh2a Hsh2b].
        apply FOcode_f_inj in Hsh2a. subst C1.
        destruct C2 as [a0 b0| |D1 D2|y4 B4|y4 B4];
          cbn [FOcode_f] in Hsh2b;
          apply cpair_inj in Hsh2b; destruct Hsh2b as [Esh2b Hsh2b];
          try discriminate Esh2b.
        apply cpair_inj in Hsh2b. destruct Hsh2b as [Ey4 Hsh2b].
        subst y4.
        apply FOcode_f_inj in Hsh2b. subst B4.
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      1 x (FOcode_f P1) 0 0 HLrow) as M1.
        cbn [mspec] in M1.
        specialize (M1 P1 eq_refl).
        destruct (FOfree_in x P1) eqn:EF; [discriminate M1|].
        apply FOProvesTn_AllExport. exact EF.
    - (* forall-elimination *)
      destruct Hj2 as [x [tc [P [Q [Hpl [Hsh [HL4 HL3]]]]]]].
      destruct B as [a0 b0| |A1 A2|y0 B0|y0 B0];
        cbn [FOcode_f] in Hsh;
        apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
        try discriminate Esh.
      apply cpair_inj in Hsh. destruct Hsh as [Hsh1 Hsh2].
      destruct A1 as [a0 b0| |C1 C2|y1 P1|y1 P1];
        cbn [FOcode_f] in Hsh1;
        apply cpair_inj in Hsh1; destruct Hsh1 as [Esh1 Hsh1];
        try discriminate Esh1.
      apply cpair_inj in Hsh1. destruct Hsh1 as [Ey1 HP1].
      subst y1 P Q.
      destruct (tbl_subst_f_witness _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  P1 A2 x tc HL3) as [[Hnf HQP]|[s Hs]].
      + apply FOcode_f_inj in HQP. subst A2.
        pose proof (FOProvesTn_AllElimT n x FOZero P1
                      (FOsubst_ok_numeral P1 x 0)) as HAE.
        rewrite (FOsubst_f_not_free P1 x FOZero Hnf) in HAE.
        exact HAE.
      + pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      4 x tc (FOcode_f P1) 1 HL4) as M4.
        cbn [mspec] in M4.
        specialize (M4 s P1 Hs eq_refl).
        destruct (FOsubst_ok x s P1) eqn:EOK; [|discriminate M4].
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      3 x tc (FOcode_f P1) (FOcode_f A2) HL3) as M3.
        cbn [mspec] in M3.
        specialize (M3 s P1 Hs eq_refl).
        apply FOcode_f_inj in M3. subst A2.
        apply FOProvesTn_AllElimT. exact EOK.
    - (* exists-introduction *)
      destruct Hj3 as [x [tc [P [Q [Hpl [Hsh [HL4 HL3]]]]]]].
      destruct B as [a0 b0| |A1 A2|y0 B0|y0 B0];
        cbn [FOcode_f] in Hsh;
        apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
        try discriminate Esh.
      apply cpair_inj in Hsh. destruct Hsh as [Hsh1 Hsh2].
      destruct A2 as [a0 b0| |C1 C2|y1 P1|y1 P1];
        cbn [FOcode_f] in Hsh2;
        apply cpair_inj in Hsh2; destruct Hsh2 as [Esh2 Hsh2];
        try discriminate Esh2.
      apply cpair_inj in Hsh2. destruct Hsh2 as [Ey1 HP1].
      subst y1 P Q.
      destruct (tbl_subst_f_witness _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  P1 A1 x tc HL3) as [[Hnf HQP]|[s Hs]].
      + apply FOcode_f_inj in HQP. subst A1.
        pose proof (FOProvesTn_ExIntroT n x FOZero P1
                      (FOsubst_ok_numeral P1 x 0)) as HAE.
        rewrite (FOsubst_f_not_free P1 x FOZero Hnf) in HAE.
        exact HAE.
      + pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      4 x tc (FOcode_f P1) 1 HL4) as M4.
        cbn [mspec] in M4.
        specialize (M4 s P1 Hs eq_refl).
        destruct (FOsubst_ok x s P1) eqn:EOK; [|discriminate M4].
        pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                      3 x tc (FOcode_f P1) (FOcode_f A1) HL3) as M3.
        cbn [mspec] in M3.
        specialize (M3 s P1 Hs eq_refl).
        apply FOcode_f_inj in M3. subst A1.
        apply FOProvesTn_ExIntroT. exact EOK.
    - (* modus ponens *)
      destruct Hj4 as [i' [j' [bi [bj [Hpl [Hii' [Hjj' [Hbi [Hbj
        Hsh]]]]]]]]].
      pose proof (Hguard i' ltac:(lia)) as [rgi Hrowi].
      rewrite Hbi in Hrowi.
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowi (Nat.lt_succ_diag_r bi)) as [Bi EBi].
      pose proof (Hguard j' ltac:(lia)) as [rgj Hrowj].
      rewrite Hbj in Hrowj.
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowj (Nat.lt_succ_diag_r bj)) as [Bj EBj].
      rewrite EBi, EBj in Hsh.
      assert (EBi2 : Bi = FOImplF Bj B).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      apply (FOProvesTn_MP n Bj B).
      + assert (PBi : FOProvesTn n Bi).
        { apply (IHm i' ltac:(lia) ltac:(lia)). congruence. }
        rewrite EBi2 in PBi. exact PBi.
      + apply (IHm j' ltac:(lia) ltac:(lia)). congruence.
    - (* generalization *)
      destruct Hj5 as [Hpli [bb [x [Hbb Hsh]]]].
      pose proof (Hguard pl ltac:(lia)) as [rgb Hrowb].
      rewrite Hbb in Hrowb.
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowb (Nat.lt_succ_diag_r bb)) as [Bb EBb].
      rewrite EBb in Hsh.
      assert (EA : B = FOForall x Bb).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      rewrite EA.
      apply FOProvesTn_Gen.
      apply (IHm pl ltac:(lia) ltac:(lia)). congruence.
    - (* Loeb *)
      destruct Hj6 as [Hpli [bj [nu [core [na [p [Hbj [H5u [H3c [H5a
        [H3p Hsh]]]]]]]]]]].
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f (FOPRMAT (FOPrCores n))) 0 0 nu H5u)
        as M5u.
      cbn [mspec] in M5u.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 0 nu (FOcode_f (FOPRMAT (FOPrCores n))) core
                    H3c) as M3c.
      cbn [mspec] in M3c.
      specialize (M3c (FOnumeral (FOcode_f (FOPRMAT (FOPrCores n))))
                    (FOPRMAT (FOPrCores n)) M5u eq_refl).
      rewrite FOsubst_f_num in M3c.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f B) 0 0 na H5a) as M5a.
      cbn [mspec] in M5a.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 na core p H3p) as M3p.
      cbn [mspec] in M3p.
      specialize (M3p (FOnumeral (FOcode_f B))
                    (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores n)))
                       (FOPRMAT (FOPrCores n))) M5a M3c).
      rewrite FOsubst_f_num in M3p.
      pose proof (Hguard pl ltac:(lia)) as [rgb Hrowb].
      rewrite Hbj in Hrowb.
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowb (Nat.lt_succ_diag_r bj)) as [Bj EBj].
      rewrite EBj in Hsh.
      rewrite M3p in Hsh.
      assert (EBj2 : Bj = FOImplF
        (FOsubst_num 1 (FOcode_f B)
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
              (FOPRMAT (FOPrCores n)))) B).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      apply FOProvesTn_Loeb.
      assert (PBj : FOProvesTn n Bj).
      { apply (IHm pl ltac:(lia) ltac:(lia)). congruence. }
      rewrite EBj2 in PBj. exact PBj.
    - (* formalized D2 *)
      destruct (d2s_sem_in _ _ _ Hj7) as [c [HcIn Hone]].
      destruct (FOPrCores_in n c HcIn) as [k [Hk Hc]].
      subst c.
      destruct Hone as [x [y [pixy [px [py [G1 [G2 [R1 [R2 [R3
        Hsh]]]]]]]]]].
      destruct G1 as [rgx Hrowx].
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowx (Nat.lt_succ_diag_r x)) as [X EX].
      destruct G2 as [rgy Hrowy].
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowy (Nat.lt_succ_diag_r y)) as [Y EY].
      subst x y.
      destruct R1 as [nixy [R1a R1b]].
      destruct R2 as [nx [R2a R2b]].
      destruct R3 as [ny [R3a R3b]].
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (cpair 2 (cpair (FOcode_f X) (FOcode_f Y)))
                    0 0 nixy R1a) as M5i.
      cbn [mspec] in M5i.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 nixy
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores k)))
                       (FOPRMAT (FOPrCores k)))) pixy R1b) as M3i.
      cbn [mspec] in M3i.
      specialize (M3i
        (FOnumeral (cpair 2 (cpair (FOcode_f X) (FOcode_f Y))))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))) M5i eq_refl).
      rewrite FOsubst_f_num in M3i.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f X) 0 0 nx R2a) as M5x.
      cbn [mspec] in M5x.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 nx
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores k)))
                       (FOPRMAT (FOPrCores k)))) px R2b) as M3x.
      cbn [mspec] in M3x.
      specialize (M3x (FOnumeral (FOcode_f X))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))) M5x eq_refl).
      rewrite FOsubst_f_num in M3x.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f Y) 0 0 ny R3a) as M5y.
      cbn [mspec] in M5y.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 ny
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores k)))
                       (FOPRMAT (FOPrCores k)))) py R3b) as M3y.
      cbn [mspec] in M3y.
      specialize (M3y (FOnumeral (FOcode_f Y))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))) M5y eq_refl).
      rewrite FOsubst_f_num in M3y.
      rewrite M3i, M3x, M3y in Hsh.
      assert (EB : B = FOImplF
        (FOsubst_num 1 (cpair 2 (cpair (FOcode_f X) (FOcode_f Y)))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k))))
        (FOImplF
           (FOsubst_num 1 (FOcode_f X)
              (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                 (FOPRMAT (FOPrCores k))))
           (FOsubst_num 1 (FOcode_f Y)
              (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                 (FOPRMAT (FOPrCores k)))))).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      rewrite EB.
      exact (FOProvesTn_ax n _ (FOAx_D2 n k X Y Hk)).
    - (* formalized D3 *)
      destruct (d3s_sem_in _ _ _ Hj8) as [c [HcIn Hone]].
      destruct (FOPrCores_in n c HcIn) as [k [Hk Hc]].
      subst c.
      destruct Hone as [a [pa [ppa [G1 [R1 [R2 Hsh]]]]]].
      destruct G1 as [rga Hrowa].
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowa (Nat.lt_succ_diag_r a)) as [A0 EA].
      subst a.
      destruct R1 as [na [R1a R1b]].
      destruct R2 as [npa [R2a R2b]].
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f A0) 0 0 na R1a) as M5a.
      cbn [mspec] in M5a.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 na
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores k)))
                       (FOPRMAT (FOPrCores k)))) pa R1b) as M3a.
      cbn [mspec] in M3a.
      specialize (M3a (FOnumeral (FOcode_f A0))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))) M5a eq_refl).
      rewrite FOsubst_f_num in M3a.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 pa 0 0 npa R2a) as M5p.
      cbn [mspec] in M5p.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 npa
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores k)))
                       (FOPRMAT (FOPrCores k)))) ppa R2b) as M3p.
      cbn [mspec] in M3p.
      specialize (M3p (FOnumeral pa)
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))) M5p eq_refl).
      rewrite FOsubst_f_num in M3p.
      rewrite M3a in M3p.
      rewrite M3a, M3p in Hsh.
      assert (EB : B = FOImplF
        (FOsubst_num 1 (FOcode_f A0)
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k))))
        (FOsubst_num 1
           (FOcode_f (FOsubst_num 1 (FOcode_f A0)
              (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                 (FOPRMAT (FOPrCores k)))))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k))))).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      rewrite EB.
      exact (FOProvesTn_ax n _ (FOAx_D3 n k A0 Hk)).
    - (* formalized monotonicity *)
      destruct (dmons_sem_in_nth _ _ _ Hj9)
        as [i1 [i2 [c [c' [Hle [Hic [Hic' Hone]]]]]]].
      destruct (FOPrCores_nth n i1 c Hic) as [Hk1 Hc1].
      destruct (FOPrCores_nth n i2 c' Hic') as [Hk2 Hc2].
      subst c c'.
      destruct Hone as [a [p [p' [G1 [R1 [R2 Hsh]]]]]].
      destruct G1 as [rga Hrowa].
      destruct (tbl_genuine_f _ _ _ _ _ _ _ _ _ _ _ Hdisp
                  _ _ _ _ Hrowa (Nat.lt_succ_diag_r a)) as [A0 EA].
      subst a.
      destruct R1 as [na [R1a R1b]].
      destruct R2 as [na' [R2a R2b]].
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f A0) 0 0 na R1a) as M5a.
      cbn [mspec] in M5a.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 na
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores i1)))
                       (FOPRMAT (FOPrCores i1)))) p R1b) as M3a.
      cbn [mspec] in M3a.
      specialize (M3a (FOnumeral (FOcode_f A0))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores i1)))
           (FOPRMAT (FOPrCores i1))) M5a eq_refl).
      rewrite FOsubst_f_num in M3a.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    5 (FOcode_f A0) 0 0 na' R2a) as M5a'.
      cbn [mspec] in M5a'.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 1 na'
                    (FOcode_f (FOsubst_num 0
                       (FOcode_f (FOPRMAT (FOPrCores i2)))
                       (FOPRMAT (FOPrCores i2)))) p' R2b) as M3a'.
      cbn [mspec] in M3a'.
      specialize (M3a' (FOnumeral (FOcode_f A0))
        (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores i2)))
           (FOPRMAT (FOPrCores i2))) M5a' eq_refl).
      rewrite FOsubst_f_num in M3a'.
      rewrite M3a, M3a' in Hsh.
      assert (EB : B = FOImplF
        (FOsubst_num 1 (FOcode_f A0)
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores i1)))
              (FOPRMAT (FOPrCores i1))))
        (FOsubst_num 1 (FOcode_f A0)
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores i2)))
              (FOPRMAT (FOPrCores i2))))).
      { apply FOcode_f_inj. cbn [FOcode_f]. exact Hsh. }
      rewrite EB.
      exact (FOProvesTn_ax n _ (FOAx_DMon n i1 i2 A0 Hle Hk2)).
    - (* induction schema *)
      destruct Hj10 as [x [PA [C0 [SS [_ [Hsh [_ [HL3b [_ HL3s]]]]]]]]].
      destruct B as [a0 b0| |B1 B2|y0 B0|y0 B0];
        cbn [FOcode_f] in Hsh;
        apply cpair_inj in Hsh; destruct Hsh as [Esh Hsh];
        try discriminate Esh.
      apply cpair_inj in Hsh. destruct Hsh as [HB1 Hsh].
      destruct B2 as [a0 b0| |B21 B22|y0 B0|y0 B0];
        cbn [FOcode_f] in Hsh;
        apply cpair_inj in Hsh; destruct Hsh as [Esh2 Hsh];
        try discriminate Esh2.
      apply cpair_inj in Hsh. destruct Hsh as [HB21 HB22].
      destruct B21 as [a0 b0| |C1 C2|y1 B21b|y1 B21b];
        cbn [FOcode_f] in HB21;
        apply cpair_inj in HB21; destruct HB21 as [E21 HB21];
        try discriminate E21.
      apply cpair_inj in HB21. destruct HB21 as [Ey1 HB21]. subst y1.
      destruct B21b as [a0 b0| |B21b1 B21b2|y0 B0|y0 B0];
        cbn [FOcode_f] in HB21;
        apply cpair_inj in HB21; destruct HB21 as [E21b HB21];
        try discriminate E21b.
      apply cpair_inj in HB21. destruct HB21 as [HB21b1 HB21b2].
      destruct B22 as [a0 b0| |C1 C2|y2 B22b|y2 B22b];
        cbn [FOcode_f] in HB22;
        apply cpair_inj in HB22; destruct HB22 as [E22 HB22];
        try discriminate E22.
      apply cpair_inj in HB22. destruct HB22 as [Ey2 HB22]. subst y2.
      assert (EA : B21b1 = B22b)
        by (apply FOcode_f_inj; rewrite HB21b1, HB22; reflexivity).
      subst B21b1.
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 x (cpair 1 0) PA C0 HL3b) as M3b.
      cbn [mspec] in M3b.
      specialize (M3b FOZero B22b eq_refl (eq_sym HB22)).
      pose proof (tbl_sound _ _ _ _ _ _ _ _ _ _ _ Hdisp
                    3 x (cpair 2 (cpair 0 x)) PA SS HL3s) as M3s.
      cbn [mspec] in M3s.
      specialize (M3s (FOSucc (FOVar x)) B22b eq_refl (eq_sym HB22)).
      assert (EB1 : B1 = FOsubst_f x FOZero B22b)
        by (apply FOcode_f_inj; rewrite HB1; exact M3b).
      assert (EB21b2 : B21b2 = FOsubst_f x (FOSucc (FOVar x)) B22b)
        by (apply FOcode_f_inj; rewrite HB21b2; exact M3s).
      subst B1 B21b2.
      exact (FOProvesTn_ax n _ (FOAx_Ind n x B22b)). }
  destruct Hlast as [m [Hvdlen Hbeta]].
  apply (MAIN (S m) m); [lia | rewrite Hvdlen; lia | exact Hbeta].
Qed.

(** ** Encoding a derivation as a justified entry list.

    Each sequence entry contributes its entry-code guard trace and
    the computation rows its justification consults: substitution and
    capture traces for the quantifier axioms, freeness traces for the
    side-conditioned logical axioms, numeral and self-substitution
    traces for the reflection axioms and the Loeb rule. *)

Definition jcode (j : FOjust) : nat :=
  match j with
  | J_thax => cpair 0 0
  | J_log => cpair 1 0
  | J_AllElim x t => cpair 2 (cpair x (FOcode_tm t))
  | J_ExIntro x t => cpair 3 (cpair x (FOcode_tm t))
  | J_MP i j' => cpair 4 (cpair i j')
  | J_Gen i => cpair 5 i
  | J_Loeb i => cpair 6 i
  | J_d2 k X Y => cpair 7 (cpair k (cpair (FOcode_f X) (FOcode_f Y)))
  | J_d3 k X => cpair 8 (cpair k (FOcode_f X))
  | J_dmon k k' X => cpair 9 (cpair k (cpair k' (FOcode_f X)))
  | J_ind x X => cpair 10 (cpair x (FOcode_f X))
  end.

Definition jrows (n : nat) (B : FOFormula) (j : FOjust)
    : list TEntry :=
  match j with
  | J_thax =>
      match B with
      | FOImplF P C =>
          concat (map (fun k =>
            trace5 (FOcode_f C)
            ++ trace3 1 (FOnumeral (FOcode_f C))
                 (FOsubst_num 0
                    (FOcode_f (FOPRMAT (FOPrCores k)))
                    (FOPRMAT (FOPrCores k)))) (seq 0 n))
      | _ => []
      end
  | J_log =>
      match B with
      | FOImplF (FOForall x (FOImplF P Q)) _ =>
          trace1 x Q ++ trace1 x P
      | _ => []
      end
  | J_AllElim x t =>
      match B with
      | FOImplF (FOForall _ P) _ => trace4 x t P ++ trace3 x t P
      | _ => []
      end
  | J_ExIntro x t =>
      match B with
      | FOImplF _ (FOExists _ P) => trace4 x t P ++ trace3 x t P
      | _ => []
      end
  | J_MP _ _ => []
  | J_Gen _ => []
  | J_Loeb _ =>
      trace5 (FOcode_f (FOPRMAT (FOPrCores n)))
      ++ trace3 0 (FOnumeral (FOcode_f (FOPRMAT (FOPrCores n))))
           (FOPRMAT (FOPrCores n))
      ++ trace5 (FOcode_f B)
      ++ trace3 1 (FOnumeral (FOcode_f B))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
              (FOPRMAT (FOPrCores n)))
  | J_d2 k X Y =>
      trace3 (S (FOcode_f X)) (FOVar 0) X
      ++ trace3 (S (FOcode_f Y)) (FOVar 0) Y
      ++ trace5 (FOcode_f (FOImplF X Y))
      ++ trace3 1 (FOnumeral (FOcode_f (FOImplF X Y)))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
      ++ trace5 (FOcode_f X)
      ++ trace3 1 (FOnumeral (FOcode_f X))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
      ++ trace5 (FOcode_f Y)
      ++ trace3 1 (FOnumeral (FOcode_f Y))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
  | J_d3 k X =>
      trace3 (S (FOcode_f X)) (FOVar 0) X
      ++ trace5 (FOcode_f X)
      ++ trace3 1 (FOnumeral (FOcode_f X))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
      ++ trace5 (FOcode_f (FOProvSentence k X))
      ++ trace3 1 (FOnumeral (FOcode_f (FOProvSentence k X)))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
  | J_dmon k k' X =>
      trace3 (S (FOcode_f X)) (FOVar 0) X
      ++ trace5 (FOcode_f X)
      ++ trace3 1 (FOnumeral (FOcode_f X))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))
      ++ trace3 1 (FOnumeral (FOcode_f X))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k')))
              (FOPRMAT (FOPrCores k')))
  | J_ind x X =>
      trace4 x FOZero X ++ trace3 x FOZero X
      ++ trace4 x (FOSucc (FOVar x)) X
      ++ trace3 x (FOSucc (FOVar x)) X
  end.

Fixpoint seqrows (n : nat) (items : list (FOFormula * FOjust))
    : list TEntry :=
  match items with
  | [] => []
  | (B, j) :: rest =>
      trace3 (S (FOcode_f B)) (FOVar 0) B
      ++ jrows n B j ++ seqrows n rest
  end.

Lemma incl_concat_member : forall (X : Type) (l : list X) ll,
  In l ll -> incl l (concat ll).
Proof.
  intros X l ll HIn x Hx.
  induction ll as [|l0 rest IH]; cbn [concat].
  - destruct HIn.
  - destruct HIn as [->|HIn].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH HIn).
Qed.

Opaque FOPRMAT.

Lemma reflrows_one_ok : forall C k L,
  incl (trace5 (FOcode_f C)
        ++ trace3 1 (FOnumeral (FOcode_f C))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))) L ->
  forall e,
    In e (trace5 (FOcode_f C)
          ++ trace3 1 (FOnumeral (FOcode_f C))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))) ->
    entry_ok L e.
Proof.
  intros C k L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  - exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn).
  - exact (trace3_ok _ _ _ L (incl_app_tail _ _ _ _ Hincl) e HeIn).
Qed.

Lemma jrows_ok_thax : forall n C L,
  incl (concat (map (fun k =>
    trace5 (FOcode_f C)
    ++ trace3 1 (FOnumeral (FOcode_f C))
         (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
            (FOPRMAT (FOPrCores k)))) (seq 0 n))) L ->
  forall e,
    In e (concat (map (fun k =>
      trace5 (FOcode_f C)
      ++ trace3 1 (FOnumeral (FOcode_f C))
           (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
              (FOPRMAT (FOPrCores k)))) (seq 0 n))) ->
    entry_ok L e.
Proof.
  intros n C L Hincl e HeIn.
  apply in_concat in HeIn.
  destruct HeIn as [l [Hl HeIn]].
  apply in_map_iff in Hl.
  destruct Hl as [k [<- Hk]].
  apply (reflrows_one_ok C k L); [|exact HeIn].
  apply incl_tran with (2 := Hincl).
  apply incl_concat_member.
  apply in_map_iff.
  exists k. split; [reflexivity|exact Hk].
Qed.

Lemma jrows_ok_free : forall x P Q L,
  incl (trace1 x Q ++ trace1 x P) L ->
  forall e, In e (trace1 x Q ++ trace1 x P) -> entry_ok L e.
Proof.
  intros x P Q L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  - exact (trace1_ok _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn).
  - exact (trace1_ok _ _ L (incl_app_tail _ _ _ _ Hincl) e HeIn).
Qed.

Lemma jrows_ok_subst : forall x t P L,
  incl (trace4 x t P ++ trace3 x t P) L ->
  forall e, In e (trace4 x t P ++ trace3 x t P) -> entry_ok L e.
Proof.
  intros x t P L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  - exact (trace4_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn).
  - exact (trace3_ok _ _ _ L (incl_app_tail _ _ _ _ Hincl) e HeIn).
Qed.

Lemma jrows_ok_loeb : forall n B L,
  incl (trace5 (FOcode_f (FOPRMAT (FOPrCores n)))
        ++ trace3 0 (FOnumeral (FOcode_f (FOPRMAT (FOPrCores n))))
             (FOPRMAT (FOPrCores n))
        ++ trace5 (FOcode_f B)
        ++ trace3 1 (FOnumeral (FOcode_f B))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
                (FOPRMAT (FOPrCores n)))) L ->
  forall e,
    In e (trace5 (FOcode_f (FOPRMAT (FOPrCores n)))
          ++ trace3 0 (FOnumeral (FOcode_f (FOPRMAT (FOPrCores n))))
               (FOPRMAT (FOPrCores n))
          ++ trace5 (FOcode_f B)
          ++ trace3 1 (FOnumeral (FOcode_f B))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
                  (FOPRMAT (FOPrCores n)))) ->
    entry_ok L e.
Proof.
  intros n B L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  - exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn).
  - apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
    + exact (trace3_ok _ _ _ L
               (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl))
               e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
      * exact (trace5_ok _ L
                 (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _
                    (incl_app_tail _ _ _ _ Hincl))) e HeIn).
      * exact (trace3_ok _ _ _ L
                 (incl_app_tail _ _ _ _ (incl_app_tail _ _ _ _
                    (incl_app_tail _ _ _ _ Hincl))) e HeIn).
Qed.

Lemma jrows_ok_nil : forall (L : list TEntry) e,
  In e (@nil TEntry) -> entry_ok L e.
Proof.
  intros L e HeIn. destruct HeIn.
Qed.

Lemma jrows_ok_d2 : forall k X Y L,
  incl (trace3 (S (FOcode_f X)) (FOVar 0) X
        ++ trace3 (S (FOcode_f Y)) (FOVar 0) Y
        ++ trace5 (FOcode_f (FOImplF X Y))
        ++ trace3 1 (FOnumeral (FOcode_f (FOImplF X Y)))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))
        ++ trace5 (FOcode_f X)
        ++ trace3 1 (FOnumeral (FOcode_f X))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))
        ++ trace5 (FOcode_f Y)
        ++ trace3 1 (FOnumeral (FOcode_f Y))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))) L ->
  forall e,
    In e (trace3 (S (FOcode_f X)) (FOVar 0) X
          ++ trace3 (S (FOcode_f Y)) (FOVar 0) Y
          ++ trace5 (FOcode_f (FOImplF X Y))
          ++ trace3 1 (FOnumeral (FOcode_f (FOImplF X Y)))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))
          ++ trace5 (FOcode_f X)
          ++ trace3 1 (FOnumeral (FOcode_f X))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))
          ++ trace5 (FOcode_f Y)
          ++ trace3 1 (FOnumeral (FOcode_f Y))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))) ->
    entry_ok L e.
Proof.
  intros k X Y L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  exact (trace3_ok _ _ _ L Hincl e HeIn).
Qed.

Lemma jrows_ok_d3 : forall k X L,
  incl (trace3 (S (FOcode_f X)) (FOVar 0) X
        ++ trace5 (FOcode_f X)
        ++ trace3 1 (FOnumeral (FOcode_f X))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))
        ++ trace5 (FOcode_f (FOProvSentence k X))
        ++ trace3 1 (FOnumeral (FOcode_f (FOProvSentence k X)))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))) L ->
  forall e,
    In e (trace3 (S (FOcode_f X)) (FOVar 0) X
          ++ trace5 (FOcode_f X)
          ++ trace3 1 (FOnumeral (FOcode_f X))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))
          ++ trace5 (FOcode_f (FOProvSentence k X))
          ++ trace3 1 (FOnumeral (FOcode_f (FOProvSentence k X)))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))) ->
    entry_ok L e.
Proof.
  intros k X L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  exact (trace3_ok _ _ _ L Hincl e HeIn).
Qed.

Lemma jrows_ok_dmon : forall k k' X L,
  incl (trace3 (S (FOcode_f X)) (FOVar 0) X
        ++ trace5 (FOcode_f X)
        ++ trace3 1 (FOnumeral (FOcode_f X))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                (FOPRMAT (FOPrCores k)))
        ++ trace3 1 (FOnumeral (FOcode_f X))
             (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k')))
                (FOPRMAT (FOPrCores k')))) L ->
  forall e,
    In e (trace3 (S (FOcode_f X)) (FOVar 0) X
          ++ trace5 (FOcode_f X)
          ++ trace3 1 (FOnumeral (FOcode_f X))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                  (FOPRMAT (FOPrCores k)))
          ++ trace3 1 (FOnumeral (FOcode_f X))
               (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k')))
                  (FOPRMAT (FOPrCores k')))) ->
    entry_ok L e.
Proof.
  intros k k' X L Hincl e HeIn.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace5_ok _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
  { exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
  apply incl_app_tail in Hincl.
  exact (trace3_ok _ _ _ L Hincl e HeIn).
Qed.

Lemma jrows_ok : forall n B j L,
  incl (jrows n B j) L ->
  forall e, In e (jrows n B j) -> entry_ok L e.
Proof.
  intros n B j L Hincl e HeIn.
  destruct j as [| | x t | x t | i j' | i | i | k X Y | k X | k k' X | x X].
  - destruct B as [a b| |P C|y B0|y B0]; try destruct HeIn.
    exact (jrows_ok_thax n C L Hincl e HeIn).
  - destruct B as [a b| |P C|y B0|y B0]; try destruct HeIn.
    destruct P as [a b| |P1 Q1|y P0|y P0]; try destruct HeIn.
    destruct P0 as [a b| |P1 Q1|y2 B2|y2 B2]; try destruct HeIn.
    exact (jrows_ok_free y P1 Q1 L Hincl e HeIn).
  - destruct B as [a b| |P C|y B0|y B0]; try destruct HeIn.
    destruct P as [a b| |P1 Q1|y P0|y P0]; try destruct HeIn.
    exact (jrows_ok_subst x t P0 L Hincl e HeIn).
  - destruct B as [a b| |P C|y B0|y B0]; try destruct HeIn.
    destruct C as [a b| |P1 Q1|y P0|y P0]; try destruct HeIn.
    exact (jrows_ok_subst x t P0 L Hincl e HeIn).
  - exact (jrows_ok_nil L e HeIn).
  - exact (jrows_ok_nil L e HeIn).
  - cbv beta iota delta [jrows] in Hincl, HeIn.
    exact (jrows_ok_loeb n B L Hincl e HeIn).
  - cbv beta iota delta [jrows] in Hincl, HeIn.
    exact (jrows_ok_d2 k X Y L Hincl e HeIn).
  - cbv beta iota delta [jrows] in Hincl, HeIn.
    exact (jrows_ok_d3 k X L Hincl e HeIn).
  - cbv beta iota delta [jrows] in Hincl, HeIn.
    exact (jrows_ok_dmon k k' X L Hincl e HeIn).
  - cbv beta iota delta [jrows] in Hincl, HeIn.
    apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
    { exact (trace4_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn). }
    apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
    { exact (trace3_ok _ _ _ L
               (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl))
               e HeIn). }
    apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
    { exact (trace4_ok _ _ _ L
               (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _
                  (incl_app_tail _ _ _ _ Hincl))) e HeIn). }
    exact (trace3_ok _ _ _ L
             (incl_app_tail _ _ _ _ (incl_app_tail _ _ _ _
                (incl_app_tail _ _ _ _ Hincl))) e HeIn).
Qed.

Transparent FOPRMAT.

Lemma seqrows_ok : forall n items L,
  incl (seqrows n items) L ->
  forall e, In e (seqrows n items) -> entry_ok L e.
Proof.
  intros n items.
  induction items as [|[B j] rest IH]; intros L Hincl e HeIn;
    cbn [seqrows] in HeIn.
  - destruct HeIn.
  - apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
    + cbn [seqrows] in Hincl.
      exact (trace3_ok _ _ _ L (incl_app_head _ _ _ _ Hincl) e HeIn).
    + apply in_app_or in HeIn. destruct HeIn as [HeIn|HeIn].
      * cbn [seqrows] in Hincl.
        exact (jrows_ok n B j L
                 (incl_app_head _ _ _ _ (incl_app_tail _ _ _ _ Hincl))
                 e HeIn).
      * cbn [seqrows] in Hincl.
        exact (IH L
                 (incl_app_tail _ _ _ _ (incl_app_tail _ _ _ _ Hincl))
                 e HeIn).
Qed.

Lemma seqrows_guard_in : forall n items B j e,
  In (B, j) items ->
  In e (trace3 (S (FOcode_f B)) (FOVar 0) B) ->
  In e (seqrows n items).
Proof.
  intros n items B j e HIn He. revert HIn.
  induction items as [|[B0 j0] rest IH]; intros HIn;
    [destruct HIn|].
  cbn [seqrows].
  destruct HIn as [Heq|HIn].
  - injection Heq as -> ->.
    apply in_or_app. left. exact He.
  - apply in_or_app. right. apply in_or_app. right.
    exact (IH HIn).
Qed.

Lemma seqrows_jrows_in : forall n items B j e,
  In (B, j) items ->
  In e (jrows n B j) ->
  In e (seqrows n items).
Proof.
  intros n items B j e HIn He. revert HIn.
  induction items as [|[B0 j0] rest IH]; intros HIn;
    [destruct HIn|].
  cbn [seqrows].
  destruct HIn as [Heq|HIn].
  - injection Heq as -> ->.
    apply in_or_app. right. apply in_or_app. left. exact He.
  - apply in_or_app. right. apply in_or_app. right.
    exact (IH HIn).
Qed.

Lemma FORobinsonQ_axq : forall B,
  FORobinsonQ B -> axq_sem (FOcode_f B).
Proof.
  intros B HQ. unfold axq_sem.
  destruct HQ as [a b|a|x|a|a b|a|a b];
    unfold FONeg; cbn [FOcode_f FOcode_tm].
  - left. exists (FOcode_tm a), (FOcode_tm b). reflexivity.
  - right; left. exists (FOcode_tm a). reflexivity.
  - do 2 right; left. exists x. reflexivity.
  - do 3 right; left. exists (FOcode_tm a). reflexivity.
  - do 4 right; left. exists (FOcode_tm a), (FOcode_tm b).
    reflexivity.
  - do 5 right; left. exists (FOcode_tm a). reflexivity.
  - do 6 right. exists (FOcode_tm a), (FOcode_tm b). reflexivity.
Qed.

Lemma FOPrCores_in_of : forall n k,
  k < n ->
  In (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
        (FOPRMAT (FOPrCores k)))) (FOPrCores n).
Proof.
  induction n as [|n IH]; intros k Hk.
  - lia.
  - cbn [FOPrCores]. apply in_or_app.
    destruct (Nat.eq_dec k n) as [->|Hne].
    + right. left. reflexivity.
    + left. apply IH. lia.
Qed.

Lemma refls_sem_of : forall L cores c d,
  In c cores -> refl_sem L c d -> refls_sem L cores d.
Proof.
  intros L cores c d HIn Hr. revert HIn.
  induction cores as [|c0 rest IH]; cbn [refls_sem]; intros HIn.
  - destruct HIn.
  - destruct HIn as [->|HIn].
    + left. exact Hr.
    + right. exact (IH HIn).
Qed.

(** ** Encoding: from an accepted sequence to the matrix semantics.

    Position extraction from the boolean acceptance, resolution of
    backward references, and the per-justification witnesses against
    the realized table. *)

Lemma FOseq_check_nth : forall axb PrF maxk items done i B j,
  FOseq_check axb PrF maxk done items = true ->
  nth_error items i = Some (B, j) ->
  FOentry_check axb PrF maxk (done ++ map fst (firstn i items)) B j
  = true.
Proof.
  intros axb PrF maxk items.
  induction items as [|[A0 j0] rest IH]; intros done i B j Hck Hnth.
  - destruct i; discriminate.
  - cbn [FOseq_check] in Hck. apply andb_prop in Hck.
    destruct Hck as [He Hrest].
    destruct i as [|i'].
    + cbn in Hnth. injection Hnth as -> ->.
      cbn [firstn map]. rewrite app_nil_r. exact He.
    + cbn [nth_error] in Hnth.
      cbn [firstn map fst].
      specialize (IH (done ++ [A0]) i' B j Hrest Hnth).
      rewrite <- app_assoc in IH. exact IH.
Qed.

Lemma FOseq_check_nth0 : forall axb PrF maxk items i B j,
  FOseq_check axb PrF maxk [] items = true ->
  nth_error items i = Some (B, j) ->
  FOentry_check axb PrF maxk (map fst (firstn i items)) B j = true.
Proof.
  intros axb PrF maxk items i B j Hck Hnth.
  exact (FOseq_check_nth axb PrF maxk items [] i B j Hck Hnth).
Qed.

Lemma prev_nth_resolve : forall (items : list (FOFormula * FOjust)) ii i' AB,
  nth_error (map fst (firstn ii items)) i' = Some AB ->
  i' < ii /\ exists j0, nth_error items i' = Some (AB, j0).
Proof.
  intros items ii i' AB H.
  rewrite nth_error_map in H.
  rewrite nth_error_firstn in H.
  destruct (i' <? ii) eqn:Hlt; [|discriminate].
  apply Nat.ltb_lt in Hlt.
  destruct (nth_error items i') as [[A0 j0]|]; [|discriminate].
  cbn in H. injection H as ->.
  split; [exact Hlt|]. exists j0. reflexivity.
Qed.

Opaque FOPRMAT.

Lemma justck_thax : forall (L : nat -> nat -> nat -> nat -> nat -> Prop)
    n items B,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, J_thax) items ->
  FOaxb n B = true ->
  thax_sem L (FOPrCores n) (FOcode_f B).
Proof.
  intros L n items B Hsub HIn Hax.
  unfold FOaxb in Hax. apply Bool.orb_true_iff in Hax.
  destruct Hax as [Hrq|Hrefl].
  - left. exact (FORobinsonQ_axq B (FOis_RQ_sound B Hrq)).
  - right.
    destruct B as [a b | | P C | x B0 | x B0]; try discriminate.
    cbn [FOreflb] in Hrefl.
    apply existsb_exists in Hrefl.
    destruct Hrefl as [k [Hk Heqb]].
    apply in_seq in Hk.
    apply FOform_eqb_eq in Heqb. subst P.
    apply (refls_sem_of _ _
      (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
         (FOPRMAT (FOPrCores k)))) _).
    + apply FOPrCores_in_of. lia.
    + exists (FOcode_f C), (FOcode_tm (FOnumeral (FOcode_f C))),
        (FOcode_f (FOProvSentence k C)).
      split; [|split].
      * apply Hsub.
        apply (seqrows_jrows_in n items _ J_thax _ HIn).
        cbv beta iota delta [jrows].
        apply in_concat.
        exists (trace5 (FOcode_f C)
                ++ trace3 1 (FOnumeral (FOcode_f C))
                     (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                        (FOPRMAT (FOPrCores k)))).
        split.
        { apply in_map_iff. exists k. split; [reflexivity|].
          apply in_seq. lia. }
        apply in_or_app. left. apply trace5_seed. reflexivity.
      * apply Hsub.
        apply (seqrows_jrows_in n items _ J_thax _ HIn).
        cbv beta iota delta [jrows].
        apply in_concat.
        exists (trace5 (FOcode_f C)
                ++ trace3 1 (FOnumeral (FOcode_f C))
                     (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                        (FOPRMAT (FOPrCores k)))).
        split.
        { apply in_map_iff. exists k. split; [reflexivity|].
          apply in_seq. lia. }
        apply in_or_app. right. apply trace3_seed.
        unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity.
      * reflexivity.
Qed.

Lemma justck_log : forall (L : nat -> nat -> nat -> nat -> nat -> Prop)
    n items B,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, J_log) items ->
  FOis_logical_axiom B = true ->
  logax_sem L (FOcode_f B).
Proof.
  intros L n items B Hsub HIn Hax.
  unfold FOis_logical_axiom in Hax.
  repeat (apply Bool.orb_true_iff in Hax;
          destruct Hax as [Hax|Hax]).
  - destruct (FOis_K_shape B Hax) as [P [Q HB]]. subst B.
    left. exists (FOcode_f P), (FOcode_f Q). reflexivity.
  - destruct (FOis_S_shape B Hax) as [P [Q [R HB]]]. subst B.
    right; left.
    exists (FOcode_f P), (FOcode_f Q), (FOcode_f R). reflexivity.
  - destruct (FOis_DN_shape B Hax) as [P HB]. subst B.
    do 2 right; left. exists (FOcode_f P). reflexivity.
  - destruct (FOis_EqRefl_shape B Hax) as [t HB]. subst B.
    do 3 right; left. exists (FOcode_tm t). reflexivity.
  - destruct (FOis_EqSym_shape B Hax) as [a [b HB]]. subst B.
    do 4 right; left.
    exists (FOcode_tm a), (FOcode_tm b). reflexivity.
  - destruct (FOis_EqTrans_shape B Hax) as [a [b [c HB]]]. subst B.
    do 5 right; left.
    exists (FOcode_tm a), (FOcode_tm b), (FOcode_tm c). reflexivity.
  - destruct (FOis_CongS_shape B Hax) as [a [b HB]]. subst B.
    do 6 right; left.
    exists (FOcode_tm a), (FOcode_tm b). reflexivity.
  - destruct (FOis_CongPlus_shape B Hax) as [a [b [c [d HB]]]]. subst B.
    do 7 right; left.
    exists (FOcode_tm a), (FOcode_tm b), (FOcode_tm c), (FOcode_tm d).
    reflexivity.
  - destruct (FOis_CongMult_shape B Hax) as [a [b [c [d HB]]]]. subst B.
    do 8 right; left.
    exists (FOcode_tm a), (FOcode_tm b), (FOcode_tm c), (FOcode_tm d).
    reflexivity.
  - destruct (FOis_ExElim_shape B Hax) as [x [P [Q [HB Hf]]]]. subst B.
    do 9 right; left.
    exists x, (FOcode_f P), (FOcode_f Q).
    split; [reflexivity|].
    apply Hsub.
    apply (seqrows_jrows_in n items _ J_log _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. left. apply trace1_seed.
    rewrite Hf. reflexivity.
  - destruct (FOis_AllK_shape B Hax) as [y [P [Q HB]]]. subst B.
    do 10 right; left.
    exists y, (FOcode_f P), (FOcode_f Q). reflexivity.
  - destruct (FOis_AllExport_shape B Hax) as [y [Hh [R [HB Hf]]]]. subst B.
    do 11 right.
    exists y, (FOcode_f Hh), (FOcode_f R).
    split; [reflexivity|].
    apply Hsub.
    apply (seqrows_jrows_in n items _ J_log _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply trace1_seed.
    rewrite Hf. reflexivity.
Qed.

Lemma justck_allelim : forall (L : nat -> nat -> nat -> nat -> nat -> Prop)
    n items B x t,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, J_AllElim x t) items ->
  FOis_AllElim x t B = true ->
  exists P Q,
    FOcode_f B = cpair 2 (cpair (cpair 3 (cpair x P)) Q)
    /\ L 4 x (FOcode_tm t) P 1
    /\ L 3 x (FOcode_tm t) P Q.
Proof.
  intros L n items B x t Hsub HIn Hck.
  destruct B as [a b | | L0 Q0 | y B0 | y B0]; try discriminate.
  destruct L0 as [a b | | P0 C0 | x' P | y B0]; try discriminate.
  cbn in Hck.
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hck HQ].
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hx Hok].
  apply Nat.eqb_eq in Hx. subst x'.
  apply FOform_eqb_eq in HQ.
  exists (FOcode_f P), (FOcode_f Q0).
  split; [reflexivity|].
  split.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_AllElim x t) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. left. apply trace4_seed.
    rewrite Hok. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_AllElim x t) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply trace3_seed.
    rewrite HQ. reflexivity.
Qed.

Lemma justck_exintro : forall (L : nat -> nat -> nat -> nat -> nat -> Prop)
    n items B x t,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, J_ExIntro x t) items ->
  FOis_ExIntro x t B = true ->
  exists P Q,
    FOcode_f B = cpair 2 (cpair Q (cpair 4 (cpair x P)))
    /\ L 4 x (FOcode_tm t) P 1
    /\ L 3 x (FOcode_tm t) P Q.
Proof.
  intros L n items B x t Hsub HIn Hck.
  destruct B as [a b | | Q0 R0 | y B0 | y B0]; try discriminate.
  destruct R0 as [a b | | P0 C0 | y B0 | x' P]; try discriminate.
  cbn in Hck.
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hck HQ].
  apply Bool.andb_true_iff in Hck. destruct Hck as [Hx Hok].
  apply Nat.eqb_eq in Hx. subst x'.
  apply FOform_eqb_eq in HQ.
  exists (FOcode_f P), (FOcode_f Q0).
  split; [reflexivity|].
  split.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ExIntro x t) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. left. apply trace4_seed.
    rewrite Hok. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ExIntro x t) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply trace3_seed.
    rewrite HQ. reflexivity.
Qed.

Lemma justck_loeb_rows : forall
    (L : nat -> nat -> nat -> nat -> nat -> Prop) n items B i,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, J_Loeb i) items ->
  exists nu core na p,
    L 5 (FOcode_f (FOPRMAT (FOPrCores n))) 0 0 nu
    /\ L 3 0 nu (FOcode_f (FOPRMAT (FOPrCores n))) core
    /\ L 5 (FOcode_f B) 0 0 na
    /\ L 3 1 na core p
    /\ p = FOcode_f (FOProvSentence n B).
Proof.
  intros L n items B i Hsub HIn.
  exists (FOcode_tm (FOnumeral (FOcode_f (FOPRMAT (FOPrCores n))))),
    (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
       (FOPRMAT (FOPrCores n)))),
    (FOcode_tm (FOnumeral (FOcode_f B))),
    (FOcode_f (FOProvSentence n B)).
  split; [|split; [|split; [|split]]].
  - apply Hsub.
    apply (seqrows_jrows_in n items B (J_Loeb i) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. left. apply trace5_seed. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items B (J_Loeb i) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. left.
    apply trace3_seed. rewrite FOsubst_f_num. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items B (J_Loeb i) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left.
    apply trace5_seed. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items B (J_Loeb i) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right.
    apply trace3_seed.
    unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity.
  - reflexivity.
Qed.

Lemma justck_genuine_row : forall
    (L : nat -> nat -> nat -> nat -> nat -> Prop) n items B j X,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (B, j) items ->
  (forall e, In e (trace3 (S (FOcode_f X)) (FOVar 0) X) ->
     In e (jrows n B j)) ->
  genuine_sem L (FOcode_f X).
Proof.
  intros L n items B j X Hsub HIn Hchunk.
  exists (FOcode_f (FOsubst_f (S (FOcode_f X)) (FOVar 0) X)).
  apply Hsub.
  apply (seqrows_jrows_in n items B j _ HIn).
  apply Hchunk.
  pose proof (trace3_seed (S (FOcode_f X)) (FOVar 0) X
      (FOcode_f (FOsubst_f (S (FOcode_f X)) (FOVar 0) X))
      eq_refl) as Hrow.
  change (FOcode_tm (FOVar 0)) with 0 in Hrow.
  exact Hrow.
Qed.

Lemma justck_d2_rows : forall
    (L : nat -> nat -> nat -> nat -> nat -> Prop) n items k X Y,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (FOImplF (FOProvSentence k (FOImplF X Y))
        (FOImplF (FOProvSentence k X) (FOProvSentence k Y)),
      J_d2 k X Y) items ->
  d2one_sem L
    (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
       (FOPRMAT (FOPrCores k))))
    (FOcode_f (FOImplF (FOProvSentence k (FOImplF X Y))
        (FOImplF (FOProvSentence k X) (FOProvSentence k Y)))).
Proof.
  intros L n items k X Y Hsub HIn.
  exists (FOcode_f X), (FOcode_f Y),
    (FOcode_f (FOProvSentence k (FOImplF X Y))),
    (FOcode_f (FOProvSentence k X)),
    (FOcode_f (FOProvSentence k Y)).
  split.
  { apply (justck_genuine_row L n items _ _ X Hsub HIn).
    intros e He.
    cbv beta iota delta [jrows].
    apply in_or_app. left. exact He. }
  split.
  { apply (justck_genuine_row L n items _ _ Y Hsub HIn).
    intros e He.
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. left. exact He. }
  split.
  { exists (FOcode_tm (FOnumeral
      (cpair 2 (cpair (FOcode_f X) (FOcode_f Y))))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. left.
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f X))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      do 4 (apply in_or_app; right). apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      do 5 (apply in_or_app; right). apply in_or_app. left.
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f Y))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      do 6 (apply in_or_app; right). apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d2 k X Y) _ HIn).
      cbv beta iota delta [jrows].
      do 7 (apply in_or_app; right).
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  reflexivity.
Qed.

Lemma justck_d3_rows : forall
    (L : nat -> nat -> nat -> nat -> nat -> Prop) n items k X,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (FOImplF (FOProvSentence k X)
        (FOProvSentence k (FOProvSentence k X)),
      J_d3 k X) items ->
  d3one_sem L
    (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
       (FOPRMAT (FOPrCores k))))
    (FOcode_f (FOImplF (FOProvSentence k X)
        (FOProvSentence k (FOProvSentence k X)))).
Proof.
  intros L n items k X Hsub HIn.
  exists (FOcode_f X),
    (FOcode_f (FOProvSentence k X)),
    (FOcode_f (FOProvSentence k (FOProvSentence k X))).
  split.
  { apply (justck_genuine_row L n items _ _ X Hsub HIn).
    intros e He.
    cbv beta iota delta [jrows].
    apply in_or_app. left. exact He. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f X))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d3 k X) _ HIn).
      cbv beta iota delta [jrows].
      apply in_or_app. right. apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d3 k X) _ HIn).
      cbv beta iota delta [jrows].
      do 2 (apply in_or_app; right). apply in_or_app. left.
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f (FOProvSentence k X)))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d3 k X) _ HIn).
      cbv beta iota delta [jrows].
      do 3 (apply in_or_app; right). apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_d3 k X) _ HIn).
      cbv beta iota delta [jrows].
      do 4 (apply in_or_app; right).
      apply trace3_seed.
      unfold FOProvSentence at 2. rewrite FOsubst_f_num.
      reflexivity. }
  reflexivity.
Qed.

Lemma justck_dmon_rows : forall
    (L : nat -> nat -> nat -> nat -> nat -> Prop) n items k k' X,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (FOImplF (FOProvSentence k X) (FOProvSentence k' X),
      J_dmon k k' X) items ->
  dmonone_sem L
    (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
       (FOPRMAT (FOPrCores k))))
    (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k')))
       (FOPRMAT (FOPrCores k'))))
    (FOcode_f (FOImplF (FOProvSentence k X) (FOProvSentence k' X))).
Proof.
  intros L n items k k' X Hsub HIn.
  exists (FOcode_f X),
    (FOcode_f (FOProvSentence k X)),
    (FOcode_f (FOProvSentence k' X)).
  split.
  { apply (justck_genuine_row L n items _ _ X Hsub HIn).
    intros e He.
    cbv beta iota delta [jrows].
    apply in_or_app. left. exact He. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f X))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_dmon k k' X) _ HIn).
      cbv beta iota delta [jrows].
      apply in_or_app. right. apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_dmon k k' X) _ HIn).
      cbv beta iota delta [jrows].
      do 2 (apply in_or_app; right). apply in_or_app. left.
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  split.
  { exists (FOcode_tm (FOnumeral (FOcode_f X))).
    split.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_dmon k k' X) _ HIn).
      cbv beta iota delta [jrows].
      apply in_or_app. right. apply in_or_app. left.
      apply trace5_seed. reflexivity.
    - apply Hsub.
      apply (seqrows_jrows_in n items _ (J_dmon k k' X) _ HIn).
      cbv beta iota delta [jrows].
      do 3 (apply in_or_app; right).
      apply trace3_seed.
      unfold FOProvSentence. rewrite FOsubst_f_num. reflexivity. }
  reflexivity.
Qed.

Lemma justck_ind : forall (L : nat -> nat -> nat -> nat -> nat -> Prop)
    n items x X,
  (forall tg a1 a2 a3 r,
     In (mkTE tg a1 a2 a3 r) (seqrows n items) -> L tg a1 a2 a3 r) ->
  In (FOInduction x X, J_ind x X) items ->
  L 4 x (FOcode_tm FOZero) (FOcode_f X) 1
  /\ L 3 x (FOcode_tm FOZero) (FOcode_f X)
       (FOcode_f (FOsubst_f x FOZero X))
  /\ L 4 x (FOcode_tm (FOSucc (FOVar x))) (FOcode_f X) 1
  /\ L 3 x (FOcode_tm (FOSucc (FOVar x))) (FOcode_f X)
       (FOcode_f (FOsubst_f x (FOSucc (FOVar x)) X)).
Proof.
  intros L n items x X Hsub HIn.
  pose proof (FOsubst_ok_numeral X x 0) as Hok0.
  cbn [FOnumeral] in Hok0.
  pose proof (FOsubst_ok_succ_var_self X x) as Hoks.
  split; [|split; [|split]].
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ind x X) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. left.
    apply trace4_seed. rewrite Hok0. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ind x X) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. left.
    apply trace3_seed. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ind x X) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left.
    apply trace4_seed. rewrite Hoks. reflexivity.
  - apply Hsub.
    apply (seqrows_jrows_in n items _ (J_ind x X) _ HIn).
    cbv beta iota delta [jrows].
    apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right.
    apply trace3_seed. reflexivity.
Qed.

Theorem provmat_encode : forall n A,
  FOProvesTn n A ->
  provmat_sem (FOPrCores n) (FOcode_f (FOPRMAT (FOPrCores n)))
    (FOcode_f A).
Proof.
  intros n A HPr.
  destruct (FOProvesTn_to_seq n A HPr) as [items [pre [Hck Hmap]]].
  destruct (table_realize (seqrows n items)
      (seqrows_ok n items (seqrows n items) (incl_refl _)))
    as [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr
        [HIFF Hdisp]]]]]]]]]]].
  destruct (beta_complete (map (fun it => FOcode_f (fst it)) items))
    as [vcs [vds Hbs]].
  destruct (beta_complete (map (fun it => jcode (snd it)) items))
    as [vcj [vdj Hbj]].
  assert (Hsub : forall tg a1 a2 a3 r,
      In (mkTE tg a1 a2 a3 r) (seqrows n items) ->
      tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
        (length (seqrows n items)) tg a1 a2 a3 r).
  { intros tg a1 a2 a3 r Hrow. apply HIFF. exact Hrow. }
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr,
    (length (seqrows n items)), vcs, vds, vcj, vdj, (length items).
  split; [exact Hdisp|].
  split.
  { exists (length pre).
    assert (HlenA : length items = S (length pre)).
    { pose proof (length_map fst items) as Hl.
      rewrite Hmap in Hl. rewrite length_app in Hl.
      cbn [length] in Hl. lia. }
    split; [exact HlenA|].
    rewrite Hbs by (rewrite length_map; lia).
    apply nth_error_nth.
    rewrite <- map_map. rewrite Hmap. rewrite map_app.
    rewrite nth_error_app2 by (rewrite length_map; lia).
    rewrite length_map. rewrite Nat.sub_diag. reflexivity. }
  split.
  { intros ii Hii.
    destruct (nth_error items ii) as [[B j]|] eqn:Hith.
    2:{ apply nth_error_None in Hith. lia. }
    pose proof (nth_error_In _ _ Hith) as HInBj.
    pose proof (FOseq_check_nth0 _ _ _ _ _ _ _ Hck Hith) as Hentry.
    assert (Hvd : beta vcs vds ii = FOcode_f B).
    { rewrite Hbs by (rewrite length_map; lia).
      apply nth_error_nth. rewrite nth_error_map.
      rewrite Hith. reflexivity. }
    assert (Hvj : beta vcj vdj ii = jcode j).
    { rewrite Hbj by (rewrite length_map; lia).
      apply nth_error_nth. rewrite nth_error_map.
      rewrite Hith. reflexivity. }
    exists (FOcode_f B), (jcode j).
    destruct j as [| | x t | x t | i1 j1 | i1 | i1
                  | k X Y | k X | k k' X | x X];
      cbv beta iota delta [FOentry_check] in Hentry.
    - exists 0, 0.
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      left. split; [reflexivity|].
      exact (justck_thax _ n items B Hsub HInBj Hentry).
    - exists 1, 0.
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      right; left. split; [reflexivity|].
      exact (justck_log _ n items B Hsub HInBj Hentry).
    - exists 2, (cpair x (FOcode_tm t)).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 2 right; left. split; [reflexivity|].
      destruct (justck_allelim _ n items B x t Hsub HInBj Hentry)
        as [P [Q [Hshape [H4 H3]]]].
      exists x, (FOcode_tm t), P, Q.
      split; [reflexivity|]. split; [exact Hshape|].
      split; [exact H4|exact H3].
    - exists 3, (cpair x (FOcode_tm t)).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 3 right; left. split; [reflexivity|].
      destruct (justck_exintro _ n items B x t Hsub HInBj Hentry)
        as [P [Q [Hshape [H4 H3]]]].
      exists x, (FOcode_tm t), P, Q.
      split; [reflexivity|]. split; [exact Hshape|].
      split; [exact H4|exact H3].
    - exists 4, (cpair i1 j1).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 4 right; left. split; [reflexivity|].
      revert Hentry.
      destruct (nth_error (map fst (firstn ii items)) i1)
        as [AB|] eqn:HAB; intros Hentry; [|discriminate].
      revert Hentry.
      destruct (nth_error (map fst (firstn ii items)) j1)
        as [B1|] eqn:HB1; intros Hentry; [|discriminate].
      cbv beta iota in Hentry.
      apply FOform_eqb_eq in Hentry. subst AB.
      destruct (prev_nth_resolve _ _ _ _ HAB) as [Hi1 [jA HitA]].
      destruct (prev_nth_resolve _ _ _ _ HB1) as [Hj1 [jB HitB]].
      exists i1, j1, (FOcode_f (FOImplF B1 B)), (FOcode_f B1).
      split; [reflexivity|]. split; [lia|]. split; [lia|].
      split.
      { rewrite Hbs by (rewrite length_map; lia).
        apply nth_error_nth. rewrite nth_error_map.
        rewrite HitA. reflexivity. }
      split.
      { rewrite Hbs by (rewrite length_map; lia).
        apply nth_error_nth. rewrite nth_error_map.
        rewrite HitB. reflexivity. }
      reflexivity.
    - destruct B as [a b | | P0 C0 | y B0 | y B0]; try discriminate.
      exists 5, i1.
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 5 right; left.
      revert Hentry.
      destruct (nth_error (map fst (firstn ii items)) i1)
        as [B'|] eqn:HB'; intros Hentry; [|discriminate].
      cbv beta iota in Hentry.
      apply FOform_eqb_eq in Hentry. subst B0.
      destruct (prev_nth_resolve _ _ _ _ HB') as [Hi1 [jB HitB]].
      split; [reflexivity|]. split; [lia|].
      exists (FOcode_f B'), y.
      split.
      { rewrite Hbs by (rewrite length_map; lia).
        apply nth_error_nth. rewrite nth_error_map.
        rewrite HitB. reflexivity. }
      reflexivity.
    - exists 6, i1.
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 6 right; left.
      revert Hentry.
      destruct (nth_error (map fst (firstn ii items)) i1)
        as [P0|] eqn:HP0; intros Hentry; [|discriminate].
      cbv beta iota in Hentry.
      apply FOform_eqb_eq in Hentry. subst P0.
      destruct (prev_nth_resolve _ _ _ _ HP0) as [Hi1 [jP HitP]].
      split; [reflexivity|]. split; [lia|].
      destruct (justck_loeb_rows _ n items B i1 Hsub HInBj)
        as [nu [core [na [p [R1 [R2 [R3 [R4 Hp]]]]]]]].
      exists (FOcode_f (FOImplF (FOProvSentence n B) B)),
        nu, core, na, p.
      split.
      { rewrite Hbs by (rewrite length_map; lia).
        apply nth_error_nth. rewrite nth_error_map.
        rewrite HitP. reflexivity. }
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
      split; [exact R4|].
      rewrite Hp. reflexivity.
    - exists 7, (cpair k (cpair (FOcode_f X) (FOcode_f Y))).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 7 right; left. split; [reflexivity|].
      apply andb_prop in Hentry. destruct Hentry as [Hk Heq].
      apply Nat.ltb_lt in Hk.
      apply FOform_eqb_eq in Heq. subst B.
      apply (d2s_sem_of _ _
        (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k)))) _).
      + apply FOPrCores_in_of. exact Hk.
      + exact (justck_d2_rows _ n items k X Y Hsub HInBj).
    - exists 8, (cpair k (FOcode_f X)).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 8 right; left. split; [reflexivity|].
      apply andb_prop in Hentry. destruct Hentry as [Hk Heq].
      apply Nat.ltb_lt in Hk.
      apply FOform_eqb_eq in Heq. subst B.
      apply (d3s_sem_of _ _
        (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k)))) _).
      + apply FOPrCores_in_of. exact Hk.
      + exact (justck_d3_rows _ n items k X Hsub HInBj).
    - exists 9, (cpair k (cpair k' (FOcode_f X))).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 9 right; left. split; [reflexivity|].
      apply andb_prop in Hentry. destruct Hentry as [Hk Heq].
      apply andb_prop in Hk. destruct Hk as [Hkk Hk'].
      apply Nat.leb_le in Hkk. apply Nat.ltb_lt in Hk'.
      apply FOform_eqb_eq in Heq. subst B.
      apply (dmons_sem_of_nth _ _ k k'
        (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
           (FOPRMAT (FOPrCores k))))
        (FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k')))
           (FOPRMAT (FOPrCores k')))) _
        (FOPrCores_nth_of n k ltac:(lia))
        (FOPrCores_nth_of n k' Hk') Hkk).
      exact (justck_dmon_rows _ n items k k' X Hsub HInBj).
    - apply FOform_eqb_eq in Hentry. subst B.
      exists 10, (cpair x (FOcode_f X)).
      split; [exact Hvd|]. split; [exact Hvj|]. split; [reflexivity|].
      do 10 right. split; [reflexivity|].
      destruct (justck_ind _ n items x X Hsub HInBj)
        as [H4b [H3b [H4s H3s]]].
      exists x, (FOcode_f X),
        (FOcode_f (FOsubst_f x FOZero X)),
        (FOcode_f (FOsubst_f x (FOSucc (FOVar x)) X)).
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact H4b|]. split; [exact H3b|].
      split; [exact H4s|exact H3s]. }
  { intros ii Hii.
    destruct (nth_error items ii) as [[B j]|] eqn:Hith.
    2:{ apply nth_error_None in Hith. lia. }
    pose proof (nth_error_In _ _ Hith) as HInBj.
    assert (Hvd : beta vcs vds ii = FOcode_f B).
    { rewrite Hbs by (rewrite length_map; lia).
      apply nth_error_nth. rewrite nth_error_map.
      rewrite Hith. reflexivity. }
    rewrite Hvd.
    exists (FOcode_f (FOsubst_f (S (FOcode_f B)) (FOVar 0) B)).
    apply Hsub.
    pose proof (trace3_seed (S (FOcode_f B)) (FOVar 0) B
        (FOcode_f (FOsubst_f (S (FOcode_f B)) (FOVar 0) B))
        eq_refl) as Hrow.
    change (FOcode_tm (FOVar 0)) with 0 in Hrow.
    exact (seqrows_guard_in n items B j _ HInBj Hrow). }
Qed.

Transparent FOPRMAT.

(** ** The representability bridge.

    Satisfaction of the level-[n] provability sentence coincides with
    derivability in [T_n]: decoding consumes an accepted matrix,
    encoding produces one from an accepted sequence.  Modus ponens
    and the Loeb rule then transfer to the satisfaction level. *)

Theorem FOProvSentence_sat_iff : forall e n A,
  FOsat e (FOProvSentence n A) <-> FOProvesTn n A.
Proof.
  intros e n A.
  rewrite (FOsat_FOProvSentence e n A).
  split; [exact (provmat_decode n A)|exact (provmat_encode n A)].
Qed.

Theorem FOHBL1_sat : forall e n A,
  FOProvesTn n A -> FOsat e (FOProvSentence n A).
Proof.
  intros e n A H. apply (FOProvSentence_sat_iff e n A). exact H.
Qed.

Theorem FOHBL2_sat : forall e n A B,
  FOsat e (FOProvSentence n (FOImplF A B)) ->
  FOsat e (FOProvSentence n A) ->
  FOsat e (FOProvSentence n B).
Proof.
  intros e n A B H1 H2.
  apply (FOProvSentence_sat_iff e n B).
  exact (FOProvesTn_MP n A B
    (proj1 (FOProvSentence_sat_iff e n (FOImplF A B)) H1)
    (proj1 (FOProvSentence_sat_iff e n A) H2)).
Qed.

Theorem FOLoeb_sat : forall e n A,
  FOsat e (FOProvSentence n (FOImplF (FOProvSentence n A) A)) ->
  FOsat e (FOProvSentence n A).
Proof.
  intros e n A H.
  apply (FOProvSentence_sat_iff e n A).
  apply FOProvesTn_Loeb.
  exact (proj1 (FOProvSentence_sat_iff e n _) H).
Qed.

(** ** Formalized derivability and tower cumulativity.

    The provability sentence is a closed Sigma_1 formula, so provable
    Sigma_1-completeness turns derivability of [A] in [T_n] into
    derivability of the level-[n] provability sentence at every
    level.  Cumulativity then absorbs the Loeb rule: the rule's
    conclusion at level [n] re-enters level [m] through the
    formalized derivability statement. *)

Theorem FOHBL3_provable : forall n m A,
  FOProvesTn n A -> FOProvesTn m (FOProvSentence n A).
Proof.
  intros n m A H.
  apply (FOsigma1_completeness_closed (FOProvSentence n A)).
  - apply FOsigma1_FOProvSentence.
  - intro v. apply FOProvSentence_closed.
  - apply (FOHBL1_sat (fun _ => 0) n A). exact H.
Qed.

Theorem FOHBL3_sat : forall e n A,
  FOsat e (FOProvSentence n A) ->
  FOsat e (FOProvSentence n (FOProvSentence n A)).
Proof.
  intros e n A H.
  apply FOHBL1_sat. apply (FOHBL3_provable n n).
  exact (proj1 (FOProvSentence_sat_iff e n A) H).
Qed.

Theorem FOProvesTn_cumulative : forall n m A,
  n <= m -> FOProvesTn n A -> FOProvesTn m A.
Proof.
  intros n m A Hnm H. induction H.
  - apply FOProvesTn_ax.
    match goal with
    | HA : FOAxiomTn _ _ |- _ =>
        inversion HA; subst;
        [ apply FOAx_RQ; assumption
        | apply FOAx_Refl; lia
        | apply FOAx_D2; lia
        | apply FOAx_D3; lia
        | apply FOAx_DMon; lia
        | apply FOAx_Ind ]
    end.
  - apply FOProvesTn_K.
  - apply FOProvesTn_S.
  - apply FOProvesTn_DN.
  - eapply FOProvesTn_MP; eassumption.
  - apply FOProvesTn_Gen; assumption.
  - apply FOProvesTn_EqRefl.
  - apply FOProvesTn_EqSym.
  - apply FOProvesTn_EqTrans.
  - apply FOProvesTn_CongS.
  - apply FOProvesTn_CongPlus.
  - apply FOProvesTn_CongMult.
  - apply FOProvesTn_AllElimT; assumption.
  - apply FOProvesTn_ExIntroT; assumption.
  - apply FOProvesTn_ExElim; assumption.
  - apply FOProvesTn_AllK.
  - apply FOProvesTn_AllExport; assumption.
  - apply (FOProvesTn_MP m (FOProvSentence n phi) phi);
      [assumption|].
    apply (FOHBL3_provable n m).
    apply FOProvesTn_Loeb. assumption.
Qed.

Theorem FOProv_sat_monotone : forall e n m A,
  n <= m ->
  FOsat e (FOProvSentence n A) -> FOsat e (FOProvSentence m A).
Proof.
  intros e n m A Hnm H.
  apply FOProvSentence_sat_iff.
  exact (FOProvesTn_cumulative n m A Hnm
           (proj1 (FOProvSentence_sat_iff e n A) H)).
Qed.

(** ** Provable Sigma_1 completeness, closed Delta_0 fragment.

    The level-[n] tower internally derives the completeness implication
    [A -> Prov_n A] for every closed Delta_0 sentence [A].  Decidability
    of closed Delta_0 sentences ([FOdelta0_decided]) splits on truth: a
    true [A] is derivable, hence (by necessitation [FOHBL3_provable]) so
    is [Prov_n A], and weakening discharges the antecedent; a false [A]
    is refutable, and ex falso closes the implication.  This is the
    closed-[Delta_0] case of provable Sigma_1 completeness; the open
    case (and the existential wrap) need the internal numeral
    substitution function and are not covered by truth-splitting. *)

Theorem provable_delta0_completeness_closed : forall n A,
  FOdelta0 A -> (forall v, FOfree_in v A = false) ->
  FOProvesTn n (FOImplF A (FOProvSentence n A)).
Proof.
  intros n A HD Hcl.
  destruct (FOdelta0_decided (FOfsize A) A (Nat.le_refl _) HD Hcl n)
    as [Htrue Hfalse].
  destruct (classic (FOsat (fun _ => 0) A)) as [Hs | Hns].
  - exact (FOPr_weaken n (FOProvSentence n A) A
             (FOHBL3_provable n n A (Htrue Hs))).
  - exact (FOPr_compose n A FOFalseF (FOProvSentence n A)
             (Hfalse Hns) (FOPr_efq n (FOProvSentence n A))).
Qed.

(** ** Cross-level box combinators.

    These internalize, at level [n], the distribution of a level-[k]
    derivation over the level-[k] provability box (for [k < n]).  They
    are the reusable steps of the open-[Delta_0] and [Sigma_1]
    constructions: [FOprov_box_nec_imp] necessitates an object-level
    implication provable at level [k] and distributes it across the box
    using the second Hilbert-Bernays axiom; the binary and existential
    forms specialize it.  No truth-splitting and no appeal to
    [FOAx_D3]. *)

Lemma FOprov_box_nec_imp : forall n k A B,
  k < n -> FOProvesTn k (FOImplF A B) ->
  FOProvesTn n (FOImplF (FOProvSentence k A) (FOProvSentence k B)).
Proof.
  intros n k A B Hk Hab.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_ax n _ (FOAx_D2 n k A B Hk))
           (FOHBL3_provable k n _ Hab)).
Qed.

Lemma FOprov_box_nec_imp2 : forall n k A B C,
  k < n -> FOProvesTn k (FOImplF A (FOImplF B C)) ->
  FOProvesTn n (FOImplF (FOProvSentence k A)
                  (FOImplF (FOProvSentence k B) (FOProvSentence k C))).
Proof.
  intros n k A B C Hk Habc.
  pose proof (FOprov_box_nec_imp n k A (FOImplF B C) Hk Habc) as H1.
  pose proof (FOProvesTn_ax n _ (FOAx_D2 n k B C Hk)) as Hd2.
  exact (FOPr_compose n (FOProvSentence k A)
           (FOProvSentence k (FOImplF B C))
           (FOImplF (FOProvSentence k B) (FOProvSentence k C)) H1 Hd2).
Qed.

Lemma FOprov_box_ex_intro : forall n k x t delta,
  k < n -> FOsubst_ok x t delta = true ->
  FOProvesTn n (FOImplF (FOProvSentence k (FOsubst_f x t delta))
                        (FOProvSentence k (FOExists x delta))).
Proof.
  intros n k x t delta Hk Hok.
  exact (FOprov_box_nec_imp n k _ _ Hk
           (FOProvesTn_ExIntroT k x t delta Hok)).
Qed.

Lemma FOprov_box_ex_intro_num : forall n k x m delta,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k (FOsubst_num x m delta))
                        (FOProvSentence k (FOExists x delta))).
Proof.
  intros n k x m delta Hk.
  rewrite <- (FOsubst_f_num delta x m).
  exact (FOprov_box_ex_intro n k x (FOnumeral m) delta Hk
           (FOsubst_ok_numeral delta x m)).
Qed.

(** Box versions of the propositional connective rules: each
    necessitates the corresponding level-[k] tautology and distributes
    it across the level-[k] box.  [box_imp_weaken] is the [K]
    combinator boxed; [box_imp_from_neg] is the ex-falso direction,
    boxed — together they give both halves of the implication case in a
    boxed [Delta_0] completeness induction. *)

Lemma FOprov_box_and_intro : forall n k A B,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k A)
                  (FOImplF (FOProvSentence k B)
                     (FOProvSentence k (FOAnd A B)))).
Proof.
  intros n k A B Hk.
  apply (FOprov_box_nec_imp2 n k A B (FOAnd A B) Hk).
  apply (FOPr_taut k (FOm2 A B)
    (Impl (Var 0) (Impl (Var 1) (And (Var 0) (Var 1)))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOprov_box_and_elim_l : forall n k A B,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k (FOAnd A B))
                        (FOProvSentence k A)).
Proof.
  intros n k A B Hk.
  exact (FOprov_box_nec_imp n k _ _ Hk (FOPr_and_elim_l k A B)).
Qed.

Lemma FOprov_box_and_elim_r : forall n k A B,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k (FOAnd A B))
                        (FOProvSentence k B)).
Proof.
  intros n k A B Hk.
  exact (FOprov_box_nec_imp n k _ _ Hk (FOPr_and_elim_r k A B)).
Qed.

Lemma FOprov_box_or_intro_l : forall n k A B,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k A)
                        (FOProvSentence k (FOOr A B))).
Proof.
  intros n k A B Hk.
  exact (FOprov_box_nec_imp n k _ _ Hk (FOPr_or_intro_l k A B)).
Qed.

Lemma FOprov_box_or_intro_r : forall n k A B,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k B)
                        (FOProvSentence k (FOOr A B))).
Proof.
  intros n k A B Hk.
  exact (FOprov_box_nec_imp n k _ _ Hk (FOPr_or_intro_r k A B)).
Qed.

Lemma FOprov_box_imp_weaken : forall n k B C,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k C)
                        (FOProvSentence k (FOImplF B C))).
Proof.
  intros n k B C Hk.
  exact (FOprov_box_nec_imp n k _ _ Hk (FOProvesTn_K k C B)).
Qed.

Lemma FOprov_box_imp_from_neg : forall n k B C,
  k < n ->
  FOProvesTn n (FOImplF (FOProvSentence k (FONeg B))
                        (FOProvSentence k (FOImplF B C))).
Proof.
  intros n k B C Hk.
  apply (FOprov_box_nec_imp n k (FONeg B) (FOImplF B C) Hk).
  apply (FOPr_taut k (FOm2 B C)
    (Impl (Neg (Var 0)) (Impl (Var 0) (Var 1))));
    [cbn; tauto | reflexivity].
Qed.

(** ** Applied equational toolkit.

    The equality axioms in their [exact]-applied (proof-to-proof) form:
    these turn object-level equational chains into ordinary function
    composition instead of nested [MP]-on-[EqTrans] terms. *)

Lemma FOPr_eq_sym : forall n a b,
  FOProvesTn n (FOEq a b) -> FOProvesTn n (FOEq b a).
Proof.
  intros n a b H. exact (FOProvesTn_MP n _ _ (FOProvesTn_EqSym n a b) H).
Qed.

Lemma FOPr_eq_trans : forall n a b c,
  FOProvesTn n (FOEq a b) -> FOProvesTn n (FOEq b c) ->
  FOProvesTn n (FOEq a c).
Proof.
  intros n a b c H1 H2.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ (FOProvesTn_EqTrans n a b c) H1) H2).
Qed.

Lemma FOPr_eq_congS : forall n a b,
  FOProvesTn n (FOEq a b) -> FOProvesTn n (FOEq (FOSucc a) (FOSucc b)).
Proof.
  intros n a b H. exact (FOProvesTn_MP n _ _ (FOProvesTn_CongS n a b) H).
Qed.

Lemma FOPr_eq_congPlus : forall n a b c d,
  FOProvesTn n (FOEq a b) -> FOProvesTn n (FOEq c d) ->
  FOProvesTn n (FOEq (FOPlus a c) (FOPlus b d)).
Proof.
  intros n a b c d H1 H2.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ (FOProvesTn_CongPlus n a b c d) H1) H2).
Qed.

Lemma FOPr_eq_congMult : forall n a b c d,
  FOProvesTn n (FOEq a b) -> FOProvesTn n (FOEq c d) ->
  FOProvesTn n (FOEq (FOMult a c) (FOMult b d)).
Proof.
  intros n a b c d H1 H2.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ (FOProvesTn_CongMult n a b c d) H1) H2).
Qed.

(** Implication-form equational steps: thread a closed equation onto an
    equation that is conditional on a hypothesis [H].  These play the
    role of a deduction theorem for the equational reasoning inside an
    induction step, where [H] is the induction hypothesis. *)

Lemma FOPr_imp_eq_trans_l : forall n H a b c,
  FOProvesTn n (FOEq a b) ->
  FOProvesTn n (FOImplF H (FOEq b c)) ->
  FOProvesTn n (FOImplF H (FOEq a c)).
Proof.
  intros n H a b c Hab Hbc.
  pose proof (FOPr_compose n H (FOEq a b) (FOImplF (FOEq b c) (FOEq a c))
                (FOPr_weaken n (FOEq a b) H Hab)
                (FOProvesTn_EqTrans n a b c)) as Hc.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ (FOProvesTn_S n H (FOEq b c) (FOEq a c)) Hc)
           Hbc).
Qed.

Lemma FOPr_imp_eq_trans_r : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOEq b c) ->
  FOProvesTn n (FOImplF H (FOEq a c)).
Proof.
  intros n H a b c Hab Hbc.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_MP n _ _ (FOPr_imp_swap n (FOEq a b) (FOEq b c) (FOEq a c))
       (FOProvesTn_EqTrans n a b c)) Hbc) as Hac.
  exact (FOPr_compose n H (FOEq a b) (FOEq a c) Hab Hac).
Qed.

Lemma FOPr_imp_eq_congS : forall n H a b,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOImplF H (FOEq (FOSucc a) (FOSucc b))).
Proof.
  intros n H a b H1.
  exact (FOPr_compose n H (FOEq a b) (FOEq (FOSucc a) (FOSucc b))
           H1 (FOProvesTn_CongS n a b)).
Qed.

(** Left-argument congruence for [+] (the right argument fixed), in
    plain and implication-conditional form: the [mult] step cases apply
    the induction hypothesis under a [+ c]. *)

Lemma FOPr_congPlus_l : forall n a b c,
  FOProvesTn n (FOImplF (FOEq a b) (FOEq (FOPlus a c) (FOPlus b c))).
Proof.
  intros n a b c.
  exact (FOProvesTn_MP n _ _
    (FOProvesTn_MP n _ _
      (FOPr_imp_swap n (FOEq a b) (FOEq c c)
         (FOEq (FOPlus a c) (FOPlus b c)))
      (FOProvesTn_CongPlus n a b c c))
    (FOProvesTn_EqRefl n c)).
Qed.

Lemma FOPr_imp_eq_congPlus_l : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOImplF H (FOEq (FOPlus a c) (FOPlus b c))).
Proof.
  intros n H a b c H1.
  exact (FOPr_compose n H (FOEq a b) (FOEq (FOPlus a c) (FOPlus b c))
           H1 (FOPr_congPlus_l n a b c)).
Qed.

Lemma FOPr_congPlus_r : forall n a b c,
  FOProvesTn n (FOImplF (FOEq b c) (FOEq (FOPlus a b) (FOPlus a c))).
Proof.
  intros n a b c.
  exact (FOProvesTn_MP n _ _
    (FOProvesTn_CongPlus n a a b c) (FOProvesTn_EqRefl n a)).
Qed.

Lemma FOPr_imp_eq_congPlus_r : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq b c)) ->
  FOProvesTn n (FOImplF H (FOEq (FOPlus a b) (FOPlus a c))).
Proof.
  intros n H a b c H1.
  exact (FOPr_compose n H (FOEq b c) (FOEq (FOPlus a b) (FOPlus a c))
           H1 (FOPr_congPlus_r n a b c)).
Qed.

(** The same congruences for [*]. *)

Lemma FOPr_congMult_l : forall n a b c,
  FOProvesTn n (FOImplF (FOEq a b) (FOEq (FOMult a c) (FOMult b c))).
Proof.
  intros n a b c.
  exact (FOProvesTn_MP n _ _
    (FOProvesTn_MP n _ _
      (FOPr_imp_swap n (FOEq a b) (FOEq c c)
         (FOEq (FOMult a c) (FOMult b c)))
      (FOProvesTn_CongMult n a b c c))
    (FOProvesTn_EqRefl n c)).
Qed.

Lemma FOPr_congMult_r : forall n a b c,
  FOProvesTn n (FOImplF (FOEq b c) (FOEq (FOMult a b) (FOMult a c))).
Proof.
  intros n a b c.
  exact (FOProvesTn_MP n _ _
    (FOProvesTn_CongMult n a a b c) (FOProvesTn_EqRefl n a)).
Qed.

Lemma FOPr_imp_eq_congMult_l : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOImplF H (FOEq (FOMult a c) (FOMult b c))).
Proof.
  intros n H a b c H1.
  exact (FOPr_compose n H (FOEq a b) (FOEq (FOMult a c) (FOMult b c))
           H1 (FOPr_congMult_l n a b c)).
Qed.

Lemma FOPr_imp_eq_congMult_r : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq b c)) ->
  FOProvesTn n (FOImplF H (FOEq (FOMult a b) (FOMult a c))).
Proof.
  intros n H a b c H1.
  exact (FOPr_compose n H (FOEq b c) (FOEq (FOMult a b) (FOMult a c))
           H1 (FOPr_congMult_r n a b c)).
Qed.

(** ** Object-level induction at work.

    Robinson [Q] proves [a + 0 = a] and [a + S b = S (a + b)] but not
    the left unit law [0 + x = x], which needs induction on [x].  With
    [FOAx_Ind] in the tower the law is an object-level theorem: apply
    the induction instance, discharge the base by [Q]'s [plus_zero], and
    the step by congruence through [Q]'s [plus_succ].  This is the first
    brick of the [PA]-over-[Q] arithmetic the numeral and substitution
    functions are built from. *)

Lemma FOPr_zero_plus : forall n,
  FOProvesTn n (FOForall 0 (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0))).
Proof.
  intros n.
  pose proof (FOProvesTn_ax n _
    (FOAx_Ind n 0 (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)))) as Hind.
  unfold FOInduction in Hind.
  apply (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ Hind (FOPr_q_plus_zero n FOZero))).
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_CongS n (FOPlus FOZero (FOVar 0)) (FOVar 0)) as Hcong.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_EqTrans n (FOPlus FOZero (FOSucc (FOVar 0)))
       (FOSucc (FOPlus FOZero (FOVar 0))) (FOSucc (FOVar 0)))
    (FOPr_q_plus_succ n FOZero (FOVar 0))) as Htr.
  exact (FOPr_compose n _ _ _ Hcong Htr).
Qed.

(** [S x + y = S (x + y)] by induction on [y].  The step chains the
    successor congruence applied to the hypothesis between the two
    [Q]-provable [plus_succ] facts, using the implication-form
    equational steps. *)

Lemma FOPr_succ_plus : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOSucc (FOPlus (FOVar 0) (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 1
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOSucc (FOPlus (FOVar 0) (FOVar 1)))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hbase : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 0)) FOZero)
          (FOSucc (FOPlus (FOVar 0) FOZero)))).
  { exact (FOPr_eq_trans n _ (FOSucc (FOVar 0)) _
             (FOPr_q_plus_zero n (FOSucc (FOVar 0)))
             (FOPr_eq_sym n _ _
                (FOPr_eq_congS n _ _ (FOPr_q_plus_zero n (FOVar 0))))). }
  assert (Hstep : FOProvesTn n (FOForall 1 (FOImplF
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOSucc (FOPlus (FOVar 0) (FOVar 1))))
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
          (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1)))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_r n
             (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                   (FOSucc (FOPlus (FOVar 0) (FOVar 1))))
             (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
             (FOSucc (FOSucc (FOPlus (FOVar 0) (FOVar 1))))
             (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1))))).
    - apply (FOPr_imp_eq_trans_l n
               (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                     (FOSucc (FOPlus (FOVar 0) (FOVar 1))))
               (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
               (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 1)))
               (FOSucc (FOSucc (FOPlus (FOVar 0) (FOVar 1))))).
      + exact (FOPr_q_plus_succ n (FOSucc (FOVar 0)) (FOVar 1)).
      + apply FOPr_imp_eq_congS.
        exact (FOPr_idf n (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                                (FOSucc (FOPlus (FOVar 0) (FOVar 1))))).
    - apply FOPr_eq_sym. apply FOPr_eq_congS.
      exact (FOPr_q_plus_succ n (FOVar 0) (FOVar 1)). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Commutativity of [+] by induction on [x] (the second argument [y]
    stays free).  The base uses [0 + y = y] (an instance of
    [FOPr_zero_plus]) against [Q]'s [y + 0 = y]; the step uses
    [S x + y = S (x + y)] (an instance of [FOPr_succ_plus]) and [Q]'s
    [y + S x = S (y + x)].  Instantiations are capture-free: [succ_plus]
    is taken at its own bound variables and [Q]'s [plus_succ] is the
    arbitrary-term axiom. *)

Lemma FOPr_plus_comm : forall n,
  FOProvesTn n (FOForall 1 (FOForall 0
    (FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOPlus (FOVar 1) (FOVar 0))))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 0
    (FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOPlus (FOVar 1) (FOVar 0))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hzy : FOProvesTn n (FOEq (FOPlus FOZero (FOVar 1)) (FOVar 1))).
  { exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 1)
         (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)) eq_refl)
      (FOPr_zero_plus n)). }
  assert (Hbase : FOProvesTn n
    (FOEq (FOPlus FOZero (FOVar 1)) (FOPlus (FOVar 1) FOZero))).
  { exact (FOPr_eq_trans n _ (FOVar 1) _ Hzy
             (FOPr_eq_sym n _ _ (FOPr_q_plus_zero n (FOVar 1)))). }
  assert (Hsp : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOSucc (FOPlus (FOVar 0) (FOVar 1))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                           (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
      (FOPr_succ_plus n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 1)
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
      H1). }
  assert (Hstep : FOProvesTn n (FOForall 0 (FOImplF
    (FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOPlus (FOVar 1) (FOVar 0)))
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOSucc (FOVar 0))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_r n
      (FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOPlus (FOVar 1) (FOVar 0)))
      (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
      (FOSucc (FOPlus (FOVar 1) (FOVar 0)))
      (FOPlus (FOVar 1) (FOSucc (FOVar 0)))).
    - apply (FOPr_imp_eq_trans_l n
        (FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOPlus (FOVar 1) (FOVar 0)))
        (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
        (FOSucc (FOPlus (FOVar 0) (FOVar 1)))
        (FOSucc (FOPlus (FOVar 1) (FOVar 0)))).
      + exact Hsp.
      + apply FOPr_imp_eq_congS.
        exact (FOPr_idf n (FOEq (FOPlus (FOVar 0) (FOVar 1))
                                (FOPlus (FOVar 1) (FOVar 0)))).
    - apply FOPr_eq_sym. exact (FOPr_q_plus_succ n (FOVar 1) (FOVar 0)). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Associativity of [+] by induction on [z] ([x],[y] free). *)

Lemma FOPr_plus_assoc : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 2
    (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hbase : FOProvesTn n
    (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) FOZero)
          (FOPlus (FOVar 0) (FOPlus (FOVar 1) FOZero)))).
  { exact (FOPr_eq_trans n _ (FOPlus (FOVar 0) (FOVar 1)) _
             (FOPr_q_plus_zero n (FOPlus (FOVar 0) (FOVar 1)))
             (FOPr_eq_sym n _ _
                (FOPr_eq_congPlus n (FOVar 0) (FOVar 0)
                   (FOPlus (FOVar 1) FOZero) (FOVar 1)
                   (FOProvesTn_EqRefl n (FOVar 0))
                   (FOPr_q_plus_zero n (FOVar 1))))). }
  assert (Hstep : FOProvesTn n (FOForall 2 (FOImplF
    (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))
    (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOSucc (FOVar 2)))
          (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOSucc (FOVar 2)))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_r n
      (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
            (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))
      (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOSucc (FOVar 2)))
      (FOSucc (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))
      (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOSucc (FOVar 2))))).
    - apply (FOPr_imp_eq_trans_l n
        (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
              (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))
        (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOSucc (FOVar 2)))
        (FOSucc (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2)))
        (FOSucc (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))).
      + exact (FOPr_q_plus_succ n (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2)).
      + apply FOPr_imp_eq_congS.
        exact (FOPr_idf n (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
                                (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))).
    - exact (FOPr_eq_trans n _
               (FOPlus (FOVar 0) (FOSucc (FOPlus (FOVar 1) (FOVar 2)))) _
               (FOPr_eq_sym n _ _
                  (FOPr_q_plus_succ n (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))))
               (FOPr_eq_congPlus n (FOVar 0) (FOVar 0)
                  (FOSucc (FOPlus (FOVar 1) (FOVar 2)))
                  (FOPlus (FOVar 1) (FOSucc (FOVar 2)))
                  (FOProvesTn_EqRefl n (FOVar 0))
                  (FOPr_eq_sym n _ _
                     (FOPr_q_plus_succ n (FOVar 1) (FOVar 2))))). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Left zero for [*] by induction on [x]: [0 * x = 0].  Step chains
    [Q]'s [mult_succ] ([0 * S x = 0 * x + 0]) and [plus_zero] back to the
    hypothesis [0 * x = 0]. *)

Lemma FOPr_mult_zero_l : forall n,
  FOProvesTn n (FOForall 0 (FOEq (FOMult FOZero (FOVar 0)) FOZero)).
Proof.
  intros n.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 0
    (FOEq (FOMult FOZero (FOVar 0)) FOZero))) as Hind.
  unfold FOInduction in Hind.
  apply (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ Hind (FOPr_q_mult_zero n FOZero))).
  apply FOProvesTn_Gen.
  apply (FOPr_imp_eq_trans_l n
    (FOEq (FOMult FOZero (FOVar 0)) FOZero)
    (FOMult FOZero (FOSucc (FOVar 0)))
    (FOMult FOZero (FOVar 0))
    FOZero).
  - exact (FOPr_eq_trans n _ (FOPlus (FOMult FOZero (FOVar 0)) FOZero) _
             (FOPr_q_mult_succ n FOZero (FOVar 0))
             (FOPr_q_plus_zero n (FOMult FOZero (FOVar 0)))).
  - exact (FOPr_idf n (FOEq (FOMult FOZero (FOVar 0)) FOZero)).
Qed.

(** Fresh-variable restatements of the additive laws, obtained by
    instantiating the committed [0..2]-indexed versions at the fresh
    indices [7..9] (capture-free, [subst_ok] by computation) and
    re-generalising.  These can then be instantiated at terms over the
    low working variables [0..2] without variable capture — the form the
    multiplicative laws need. *)

Lemma FOPr_succ_plus_fv : forall n,
  FOProvesTn n (FOForall 7 (FOForall 8
    (FOEq (FOPlus (FOSucc (FOVar 7)) (FOVar 8))
          (FOSucc (FOPlus (FOVar 7) (FOVar 8)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 1 (FOVar 8)
       (FOEq (FOPlus (FOSucc (FOVar 7)) (FOVar 1))
             (FOSucc (FOPlus (FOVar 7) (FOVar 1)))) eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOVar 7)
       (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
             (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)).
  exact (FOPr_succ_plus n).
Qed.

Lemma FOPr_plus_assoc_fv : forall n,
  FOProvesTn n (FOForall 7 (FOForall 8 (FOForall 9
    (FOEq (FOPlus (FOPlus (FOVar 7) (FOVar 8)) (FOVar 9))
          (FOPlus (FOVar 7) (FOPlus (FOVar 8) (FOVar 9))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 2 (FOVar 9)
       (FOEq (FOPlus (FOPlus (FOVar 7) (FOVar 8)) (FOVar 2))
             (FOPlus (FOVar 7) (FOPlus (FOVar 8) (FOVar 2)))) eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 1 (FOVar 8)
       (FOForall 2 (FOEq (FOPlus (FOPlus (FOVar 7) (FOVar 1)) (FOVar 2))
             (FOPlus (FOVar 7) (FOPlus (FOVar 1) (FOVar 2))))) eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOVar 7)
       (FOForall 1 (FOForall 2
          (FOEq (FOPlus (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
                (FOPlus (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))))) eq_refl)).
  exact (FOPr_plus_assoc n).
Qed.

(** [S x * y = y + x * y] by induction on [y].  The step rearranges
    [(y + x*y) + S x] to [S y + x * S y] using [Q]'s [mult_succ] and
    [plus_succ] plus the fresh-var [assoc] and [succ_plus] instances at
    [(y, x*y, x)] / [(y, x*y + x)]; the hypothesis enters under [+ S x]
    via [FOPr_imp_eq_congPlus_l]. *)

Lemma FOPr_mult_succ_l : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 1
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hassoc : FOProvesTn n
    (FOEq (FOPlus (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))) (FOVar 0))
          (FOPlus (FOVar 1)
             (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 1)
         (FOForall 8 (FOForall 9
            (FOEq (FOPlus (FOPlus (FOVar 7) (FOVar 8)) (FOVar 9))
                  (FOPlus (FOVar 7) (FOPlus (FOVar 8) (FOVar 9)))))) eq_refl)
      (FOPr_plus_assoc_fv n)) as A1.
    pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8 (FOMult (FOVar 0) (FOVar 1))
         (FOForall 9
            (FOEq (FOPlus (FOPlus (FOVar 1) (FOVar 8)) (FOVar 9))
                  (FOPlus (FOVar 1) (FOPlus (FOVar 8) (FOVar 9))))) eq_refl)
      A1) as A2.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 9 (FOVar 0)
         (FOEq (FOPlus (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
                  (FOVar 9))
               (FOPlus (FOVar 1)
                  (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 9)))) eq_refl)
      A2). }
  assert (Hsp : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 1))
             (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0)))
          (FOSucc (FOPlus (FOVar 1)
             (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0)))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 1)
         (FOForall 8 (FOEq (FOPlus (FOSucc (FOVar 7)) (FOVar 8))
               (FOSucc (FOPlus (FOVar 7) (FOVar 8))))) eq_refl)
      (FOPr_succ_plus_fv n)) as S1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8
         (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0))
         (FOEq (FOPlus (FOSucc (FOVar 1)) (FOVar 8))
               (FOSucc (FOPlus (FOVar 1) (FOVar 8)))) eq_refl)
      S1). }
  assert (Hbase : FOProvesTn n
    (FOEq (FOMult (FOSucc (FOVar 0)) FOZero)
          (FOPlus FOZero (FOMult (FOVar 0) FOZero)))).
  { apply (FOPr_eq_trans n _ FOZero _).
    - exact (FOPr_q_mult_zero n (FOSucc (FOVar 0))).
    - apply FOPr_eq_sym.
      apply (FOPr_eq_trans n _ (FOMult (FOVar 0) FOZero) _).
      + exact (FOProvesTn_MP n _ _
          (FOProvesTn_AllElimT n 0 (FOMult (FOVar 0) FOZero)
             (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)) eq_refl)
          (FOPr_zero_plus n)).
      + exact (FOPr_q_mult_zero n (FOVar 0)). }
  assert (Hstep : FOProvesTn n (FOForall 1 (FOImplF
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
          (FOPlus (FOSucc (FOVar 1))
             (FOMult (FOVar 0) (FOSucc (FOVar 1)))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_r n
      (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
            (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))
      (FOMult (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
      (FOPlus (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))) (FOSucc (FOVar 0)))
      (FOPlus (FOSucc (FOVar 1)) (FOMult (FOVar 0) (FOSucc (FOVar 1))))).
    - apply (FOPr_imp_eq_trans_l n
        (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
              (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))
        (FOMult (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
        (FOPlus (FOMult (FOSucc (FOVar 0)) (FOVar 1)) (FOSucc (FOVar 0)))
        (FOPlus (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
           (FOSucc (FOVar 0)))).
      + exact (FOPr_q_mult_succ n (FOSucc (FOVar 0)) (FOVar 1)).
      + apply (FOPr_imp_eq_congPlus_l n
          (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
                (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))
          (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
          (FOSucc (FOVar 0))).
        exact (FOPr_idf n (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
                  (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))).
    - apply (FOPr_eq_trans n _
        (FOSucc (FOPlus (FOVar 1)
           (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0)))) _).
      + apply (FOPr_eq_trans n _
          (FOSucc (FOPlus (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
             (FOVar 0))) _).
        * exact (FOPr_q_plus_succ n
            (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))) (FOVar 0)).
        * exact (FOPr_eq_congS n _ _ Hassoc).
      + apply (FOPr_eq_trans n _
          (FOPlus (FOSucc (FOVar 1))
             (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0))) _).
        * exact (FOPr_eq_sym n _ _ Hsp).
        * exact (FOPr_eq_congPlus n (FOSucc (FOVar 1)) (FOSucc (FOVar 1))
                   (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0))
                   (FOMult (FOVar 0) (FOSucc (FOVar 1)))
                   (FOProvesTn_EqRefl n (FOSucc (FOVar 1)))
                   (FOPr_eq_sym n _ _
                      (FOPr_q_mult_succ n (FOVar 0) (FOVar 1)))). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Fresh-variable commutativity of [+] (indices 7,8), for capture-free
    instantiation by the multiplicative laws. *)

Lemma FOPr_plus_comm_fv : forall n,
  FOProvesTn n (FOForall 7 (FOForall 8
    (FOEq (FOPlus (FOVar 7) (FOVar 8)) (FOPlus (FOVar 8) (FOVar 7))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOVar 7)
       (FOEq (FOPlus (FOVar 0) (FOVar 8)) (FOPlus (FOVar 8) (FOVar 0)))
       eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 1 (FOVar 8)
       (FOForall 0 (FOEq (FOPlus (FOVar 0) (FOVar 1))
                         (FOPlus (FOVar 1) (FOVar 0)))) eq_refl)).
  exact (FOPr_plus_comm n).
Qed.

(** Commutativity of [*] by induction on [x] ([y] free).  Step:
    [S x * y = y + x*y] ([mult_succ_l] instance) [= y + y*x] (IH under
    [y +], via [imp_eq_congPlus_r]) [= y*x + y] ([plus_comm_fv] at
    [(y, y*x)]) [= y * S x] ([Q]'s [mult_succ]). *)

Lemma FOPr_mult_comm : forall n,
  FOProvesTn n (FOForall 1 (FOForall 0
    (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0))))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 0
    (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hms : FOProvesTn n
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
               (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1))))) eq_refl)
      (FOPr_mult_succ_l n)) as M1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 1)
         (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
               (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))) eq_refl)
      M1). }
  assert (Hpc : FOProvesTn n
    (FOEq (FOPlus (FOVar 1) (FOMult (FOVar 1) (FOVar 0)))
          (FOPlus (FOMult (FOVar 1) (FOVar 0)) (FOVar 1)))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 1)
         (FOForall 8 (FOEq (FOPlus (FOVar 7) (FOVar 8))
               (FOPlus (FOVar 8) (FOVar 7)))) eq_refl)
      (FOPr_plus_comm_fv n)) as P1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8 (FOMult (FOVar 1) (FOVar 0))
         (FOEq (FOPlus (FOVar 1) (FOVar 8)) (FOPlus (FOVar 8) (FOVar 1)))
         eq_refl)
      P1). }
  assert (Hbase : FOProvesTn n
    (FOEq (FOMult FOZero (FOVar 1)) (FOMult (FOVar 1) FOZero))).
  { apply (FOPr_eq_trans n _ FOZero _).
    - exact (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 0 (FOVar 1)
           (FOEq (FOMult FOZero (FOVar 0)) FOZero) eq_refl)
        (FOPr_mult_zero_l n)).
    - exact (FOPr_eq_sym n _ _ (FOPr_q_mult_zero n (FOVar 1))). }
  assert (Hstep : FOProvesTn n (FOForall 0 (FOImplF
    (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0)))
    (FOEq (FOMult (FOSucc (FOVar 0)) (FOVar 1))
          (FOMult (FOVar 1) (FOSucc (FOVar 0))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_l n
      (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0)))
      (FOMult (FOSucc (FOVar 0)) (FOVar 1))
      (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
      (FOMult (FOVar 1) (FOSucc (FOVar 0)))).
    - exact Hms.
    - apply (FOPr_imp_eq_trans_r n
        (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0)))
        (FOPlus (FOVar 1) (FOMult (FOVar 0) (FOVar 1)))
        (FOPlus (FOVar 1) (FOMult (FOVar 1) (FOVar 0)))
        (FOMult (FOVar 1) (FOSucc (FOVar 0)))).
      + apply (FOPr_imp_eq_congPlus_r n
          (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 1) (FOVar 0)))
          (FOVar 1)
          (FOMult (FOVar 0) (FOVar 1))
          (FOMult (FOVar 1) (FOVar 0))).
        exact (FOPr_idf n (FOEq (FOMult (FOVar 0) (FOVar 1))
                  (FOMult (FOVar 1) (FOVar 0)))).
      + apply (FOPr_eq_trans n _
          (FOPlus (FOMult (FOVar 1) (FOVar 0)) (FOVar 1)) _).
        * exact Hpc.
        * exact (FOPr_eq_sym n _ _
                   (FOPr_q_mult_succ n (FOVar 1) (FOVar 0))). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Left distributivity [x*(y+z) = x*y + x*z] by induction on [z].  The
    step turns [x*(y+S z)] into [x*(y+z) + x] (via [Q]'s [plus_succ],
    [mult_succ] and [congMult]), applies the hypothesis under [+x], then
    reassociates [(x*y + x*z) + x] to [x*y + x*S z] with [assoc_fv] at
    [(x*y, x*z, x)] and [Q]'s [mult_succ]. *)

Lemma FOPr_mult_distrib_l : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
          (FOPlus (FOMult (FOVar 0) (FOVar 1))
                  (FOMult (FOVar 0) (FOVar 2))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 2
    (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
          (FOPlus (FOMult (FOVar 0) (FOVar 1))
                  (FOMult (FOVar 0) (FOVar 2)))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hassoc : FOProvesTn n
    (FOEq (FOPlus (FOPlus (FOMult (FOVar 0) (FOVar 1))
                     (FOMult (FOVar 0) (FOVar 2))) (FOVar 0))
          (FOPlus (FOMult (FOVar 0) (FOVar 1))
             (FOPlus (FOMult (FOVar 0) (FOVar 2)) (FOVar 0))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOMult (FOVar 0) (FOVar 1))
         (FOForall 8 (FOForall 9
            (FOEq (FOPlus (FOPlus (FOVar 7) (FOVar 8)) (FOVar 9))
                  (FOPlus (FOVar 7) (FOPlus (FOVar 8) (FOVar 9)))))) eq_refl)
      (FOPr_plus_assoc_fv n)) as A1.
    pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8 (FOMult (FOVar 0) (FOVar 2))
         (FOForall 9
            (FOEq (FOPlus (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 8))
                     (FOVar 9))
                  (FOPlus (FOMult (FOVar 0) (FOVar 1))
                     (FOPlus (FOVar 8) (FOVar 9))))) eq_refl)
      A1) as A2.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 9 (FOVar 0)
         (FOEq (FOPlus (FOPlus (FOMult (FOVar 0) (FOVar 1))
                  (FOMult (FOVar 0) (FOVar 2))) (FOVar 9))
               (FOPlus (FOMult (FOVar 0) (FOVar 1))
                  (FOPlus (FOMult (FOVar 0) (FOVar 2)) (FOVar 9)))) eq_refl)
      A2). }
  assert (Hbase : FOProvesTn n
    (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) FOZero))
          (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) FOZero)))).
  { apply (FOPr_eq_trans n _ (FOMult (FOVar 0) (FOVar 1)) _).
    - exact (FOPr_eq_congMult n (FOVar 0) (FOVar 0)
               (FOPlus (FOVar 1) FOZero) (FOVar 1)
               (FOProvesTn_EqRefl n (FOVar 0)) (FOPr_q_plus_zero n (FOVar 1))).
    - apply FOPr_eq_sym.
      apply (FOPr_eq_trans n _ (FOPlus (FOMult (FOVar 0) (FOVar 1)) FOZero) _).
      + exact (FOPr_eq_congPlus n (FOMult (FOVar 0) (FOVar 1))
                 (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) FOZero) FOZero
                 (FOProvesTn_EqRefl n (FOMult (FOVar 0) (FOVar 1)))
                 (FOPr_q_mult_zero n (FOVar 0))).
      + exact (FOPr_q_plus_zero n (FOMult (FOVar 0) (FOVar 1))). }
  assert (Hstep : FOProvesTn n (FOForall 2 (FOImplF
    (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
          (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2))))
    (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOSucc (FOVar 2))))
          (FOPlus (FOMult (FOVar 0) (FOVar 1))
                  (FOMult (FOVar 0) (FOSucc (FOVar 2)))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_l n
      (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
            (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2))))
      (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOSucc (FOVar 2))))
      (FOPlus (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))) (FOVar 0))
      (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOSucc (FOVar 2))))).
    - apply (FOPr_eq_trans n _
        (FOMult (FOVar 0) (FOSucc (FOPlus (FOVar 1) (FOVar 2)))) _).
      + exact (FOPr_eq_congMult n (FOVar 0) (FOVar 0)
                 (FOPlus (FOVar 1) (FOSucc (FOVar 2)))
                 (FOSucc (FOPlus (FOVar 1) (FOVar 2)))
                 (FOProvesTn_EqRefl n (FOVar 0))
                 (FOPr_q_plus_succ n (FOVar 1) (FOVar 2))).
      + exact (FOPr_q_mult_succ n (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))).
    - apply (FOPr_imp_eq_trans_r n
        (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
              (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2))))
        (FOPlus (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2))) (FOVar 0))
        (FOPlus (FOPlus (FOMult (FOVar 0) (FOVar 1))
                   (FOMult (FOVar 0) (FOVar 2))) (FOVar 0))
        (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOSucc (FOVar 2))))).
      + apply (FOPr_imp_eq_congPlus_l n
          (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
                (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2))))
          (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
          (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2)))
          (FOVar 0)).
        exact (FOPr_idf n (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
                  (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOMult (FOVar 0) (FOVar 2))))).
      + apply (FOPr_eq_trans n _
          (FOPlus (FOMult (FOVar 0) (FOVar 1))
             (FOPlus (FOMult (FOVar 0) (FOVar 2)) (FOVar 0))) _).
        * exact Hassoc.
        * exact (FOPr_eq_congPlus n (FOMult (FOVar 0) (FOVar 1))
                   (FOMult (FOVar 0) (FOVar 1))
                   (FOPlus (FOMult (FOVar 0) (FOVar 2)) (FOVar 0))
                   (FOMult (FOVar 0) (FOSucc (FOVar 2)))
                   (FOProvesTn_EqRefl n (FOMult (FOVar 0) (FOVar 1)))
                   (FOPr_eq_sym n _ _
                      (FOPr_q_mult_succ n (FOVar 0) (FOVar 2)))). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Fresh-variable distributivity (indices 7,8,9), for capture-free
    instantiation (e.g. [mult_assoc] needs [x*(y*z + y)]). *)

Lemma FOPr_mult_distrib_l_fv : forall n,
  FOProvesTn n (FOForall 7 (FOForall 8 (FOForall 9
    (FOEq (FOMult (FOVar 7) (FOPlus (FOVar 8) (FOVar 9)))
          (FOPlus (FOMult (FOVar 7) (FOVar 8))
                  (FOMult (FOVar 7) (FOVar 9))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 2 (FOVar 9)
       (FOEq (FOMult (FOVar 7) (FOPlus (FOVar 8) (FOVar 2)))
             (FOPlus (FOMult (FOVar 7) (FOVar 8))
                     (FOMult (FOVar 7) (FOVar 2)))) eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 1 (FOVar 8)
       (FOForall 2 (FOEq (FOMult (FOVar 7) (FOPlus (FOVar 1) (FOVar 2)))
             (FOPlus (FOMult (FOVar 7) (FOVar 1))
                     (FOMult (FOVar 7) (FOVar 2))))) eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOVar 7)
       (FOForall 1 (FOForall 2
          (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 1) (FOVar 2)))
                (FOPlus (FOMult (FOVar 0) (FOVar 1))
                        (FOMult (FOVar 0) (FOVar 2)))))) eq_refl)).
  exact (FOPr_mult_distrib_l n).
Qed.

(** Associativity of [*] by induction on [z].  Step: [(x*y)*S z] is
    [(x*y)*z + x*y] ([Q] [mult_succ]); the hypothesis rewrites the left
    summand to [x*(y*z)]; and [x*(y*S z) = x*(y*z + y) = x*(y*z) + x*y]
    via [Q] [mult_succ] and [distrib_l_fv] at [(x, y*z, y)]. *)

Lemma FOPr_mult_assoc : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 2
    (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2)))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hdist : FOProvesTn n
    (FOEq (FOMult (FOVar 0)
             (FOPlus (FOMult (FOVar 1) (FOVar 2)) (FOVar 1)))
          (FOPlus (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2)))
                  (FOMult (FOVar 0) (FOVar 1))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 0)
         (FOForall 8 (FOForall 9
            (FOEq (FOMult (FOVar 7) (FOPlus (FOVar 8) (FOVar 9)))
                  (FOPlus (FOMult (FOVar 7) (FOVar 8))
                          (FOMult (FOVar 7) (FOVar 9)))))) eq_refl)
      (FOPr_mult_distrib_l_fv n)) as D1.
    pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8 (FOMult (FOVar 1) (FOVar 2))
         (FOForall 9
            (FOEq (FOMult (FOVar 0) (FOPlus (FOVar 8) (FOVar 9)))
                  (FOPlus (FOMult (FOVar 0) (FOVar 8))
                          (FOMult (FOVar 0) (FOVar 9))))) eq_refl)
      D1) as D2.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 9 (FOVar 1)
         (FOEq (FOMult (FOVar 0)
                  (FOPlus (FOMult (FOVar 1) (FOVar 2)) (FOVar 9)))
               (FOPlus (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2)))
                       (FOMult (FOVar 0) (FOVar 9)))) eq_refl)
      D2). }
  assert (Hbase : FOProvesTn n
    (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) FOZero)
          (FOMult (FOVar 0) (FOMult (FOVar 1) FOZero)))).
  { apply (FOPr_eq_trans n _ FOZero _).
    - exact (FOPr_q_mult_zero n (FOMult (FOVar 0) (FOVar 1))).
    - apply FOPr_eq_sym.
      apply (FOPr_eq_trans n _ (FOMult (FOVar 0) FOZero) _).
      + exact (FOPr_eq_congMult n (FOVar 0) (FOVar 0)
                 (FOMult (FOVar 1) FOZero) FOZero
                 (FOProvesTn_EqRefl n (FOVar 0)) (FOPr_q_mult_zero n (FOVar 1))).
      + exact (FOPr_q_mult_zero n (FOVar 0)). }
  assert (Hstep : FOProvesTn n (FOForall 2 (FOImplF
    (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))
    (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOSucc (FOVar 2)))
          (FOMult (FOVar 0) (FOMult (FOVar 1) (FOSucc (FOVar 2)))))))).
  { apply FOProvesTn_Gen.
    apply (FOPr_imp_eq_trans_l n
      (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
            (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))
      (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOSucc (FOVar 2)))
      (FOPlus (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
              (FOMult (FOVar 0) (FOVar 1)))
      (FOMult (FOVar 0) (FOMult (FOVar 1) (FOSucc (FOVar 2))))).
    - exact (FOPr_q_mult_succ n (FOMult (FOVar 0) (FOVar 1)) (FOVar 2)).
    - apply (FOPr_imp_eq_trans_r n
        (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
              (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))
        (FOPlus (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
                (FOMult (FOVar 0) (FOVar 1)))
        (FOPlus (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2)))
                (FOMult (FOVar 0) (FOVar 1)))
        (FOMult (FOVar 0) (FOMult (FOVar 1) (FOSucc (FOVar 2))))).
      + apply (FOPr_imp_eq_congPlus_l n
          (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
                (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))
          (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2)))
          (FOMult (FOVar 0) (FOVar 1))).
        exact (FOPr_idf n (FOEq (FOMult (FOMult (FOVar 0) (FOVar 1)) (FOVar 2))
                  (FOMult (FOVar 0) (FOMult (FOVar 1) (FOVar 2))))).
      + apply (FOPr_eq_trans n _
          (FOMult (FOVar 0)
             (FOPlus (FOMult (FOVar 1) (FOVar 2)) (FOVar 1))) _).
        * exact (FOPr_eq_sym n _ _ Hdist).
        * exact (FOPr_eq_congMult n (FOVar 0) (FOVar 0)
                   (FOPlus (FOMult (FOVar 1) (FOVar 2)) (FOVar 1))
                   (FOMult (FOVar 1) (FOSucc (FOVar 2)))
                   (FOProvesTn_EqRefl n (FOVar 0))
                   (FOPr_eq_sym n _ _
                      (FOPr_q_mult_succ n (FOVar 1) (FOVar 2)))). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Fresh-variable commutativity of [*] (indices 7,8). *)

Lemma FOPr_mult_comm_fv : forall n,
  FOProvesTn n (FOForall 7 (FOForall 8
    (FOEq (FOMult (FOVar 7) (FOVar 8)) (FOMult (FOVar 8) (FOVar 7))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOVar 7)
       (FOEq (FOMult (FOVar 0) (FOVar 8)) (FOMult (FOVar 8) (FOVar 0)))
       eq_refl)).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 1 (FOVar 8)
       (FOForall 0 (FOEq (FOMult (FOVar 0) (FOVar 1))
                         (FOMult (FOVar 1) (FOVar 0)))) eq_refl)).
  exact (FOPr_mult_comm n).
Qed.

(** Right distributivity [(x+y)*z = x*z + y*z] from commutativity and
    left distributivity (no induction). Completes the semiring laws. *)

Lemma FOPr_mult_distrib_r : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOEq (FOMult (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2))
          (FOPlus (FOMult (FOVar 0) (FOVar 2))
                  (FOMult (FOVar 1) (FOVar 2))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 8 (FOVar 2)
       (FOEq (FOMult (FOPlus (FOVar 0) (FOVar 1)) (FOVar 8))
             (FOMult (FOVar 8) (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
    (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOPlus (FOVar 0) (FOVar 1))
         (FOForall 8 (FOEq (FOMult (FOVar 7) (FOVar 8))
               (FOMult (FOVar 8) (FOVar 7)))) eq_refl)
      (FOPr_mult_comm_fv n))) as Hc1.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 9 (FOVar 1)
       (FOEq (FOMult (FOVar 2) (FOPlus (FOVar 0) (FOVar 9)))
             (FOPlus (FOMult (FOVar 2) (FOVar 0))
                     (FOMult (FOVar 2) (FOVar 9)))) eq_refl)
    (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 8 (FOVar 0)
         (FOForall 9 (FOEq (FOMult (FOVar 2) (FOPlus (FOVar 8) (FOVar 9)))
               (FOPlus (FOMult (FOVar 2) (FOVar 8))
                       (FOMult (FOVar 2) (FOVar 9))))) eq_refl)
      (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 7 (FOVar 2)
           (FOForall 8 (FOForall 9
              (FOEq (FOMult (FOVar 7) (FOPlus (FOVar 8) (FOVar 9)))
                    (FOPlus (FOMult (FOVar 7) (FOVar 8))
                            (FOMult (FOVar 7) (FOVar 9)))))) eq_refl)
        (FOPr_mult_distrib_l_fv n)))) as Hc2.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 8 (FOVar 0)
       (FOEq (FOMult (FOVar 2) (FOVar 8)) (FOMult (FOVar 8) (FOVar 2)))
       eq_refl)
    (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 2)
         (FOForall 8 (FOEq (FOMult (FOVar 7) (FOVar 8))
               (FOMult (FOVar 8) (FOVar 7)))) eq_refl)
      (FOPr_mult_comm_fv n))) as Hc3.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 8 (FOVar 1)
       (FOEq (FOMult (FOVar 2) (FOVar 8)) (FOMult (FOVar 8) (FOVar 2)))
       eq_refl)
    (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 7 (FOVar 2)
         (FOForall 8 (FOEq (FOMult (FOVar 7) (FOVar 8))
               (FOMult (FOVar 8) (FOVar 7)))) eq_refl)
      (FOPr_mult_comm_fv n))) as Hc4.
  apply (FOPr_eq_trans n _ (FOMult (FOVar 2) (FOPlus (FOVar 0) (FOVar 1))) _).
  - exact Hc1.
  - apply (FOPr_eq_trans n _
      (FOPlus (FOMult (FOVar 2) (FOVar 0)) (FOMult (FOVar 2) (FOVar 1))) _).
    + exact Hc2.
    + exact (FOPr_eq_congPlus n
               (FOMult (FOVar 2) (FOVar 0)) (FOMult (FOVar 0) (FOVar 2))
               (FOMult (FOVar 2) (FOVar 1)) (FOMult (FOVar 1) (FOVar 2))
               Hc3 Hc4).
Qed.

(** ** Ordering layer.

    [S (a + w) <> a] (no value is its own successor-plus-anything), by
    induction on [a]: the base is [Q]'s [succ_nonzero]; the step turns
    [S (S a + w) = S a] into [S (a + w) = a] (via [succ_inj] and
    [succ_plus]) and feeds the hypothesis through [FOPr_syl].  This is
    the basis for irreflexivity and antisymmetry of the strict order. *)

Lemma FOPr_neq_succ_add : forall n,
  FOProvesTn n (FOForall 1 (FOForall 0
    (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0))))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 0
    (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0))))) as Hind.
  unfold FOInduction in Hind.
  assert (Hbase : FOProvesTn n
    (FONeg (FOEq (FOSucc (FOPlus FOZero (FOVar 1))) FOZero))).
  { exact (FOPr_q_succ_nonzero n (FOPlus FOZero (FOVar 1))). }
  assert (Hstep : FOProvesTn n (FOForall 0 (FOImplF
    (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0)))
    (FONeg (FOEq (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 1)))
                 (FOSucc (FOVar 0))))))).
  { apply FOProvesTn_Gen.
    assert (Hsp : FOProvesTn n
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
            (FOSucc (FOPlus (FOVar 0) (FOVar 1))))).
    { pose proof (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 0 (FOVar 0)
           (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                 (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
        (FOPr_succ_plus n)) as H1.
      exact (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 1 (FOVar 1)
           (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                 (FOSucc (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
        H1). }
    pose proof (FOPr_compose n
      (FOEq (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 1))) (FOSucc (FOVar 0)))
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1)) (FOVar 0))
      (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0))
      (FOPr_q_succ_inj n (FOPlus (FOSucc (FOVar 0)) (FOVar 1)) (FOVar 0))
      (FOPr_imp_eq_trans_l n
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1)) (FOVar 0))
         (FOSucc (FOPlus (FOVar 0) (FOVar 1)))
         (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
         (FOVar 0)
         (FOPr_eq_sym n _ _ Hsp)
         (FOPr_idf n (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                           (FOVar 0))))) as SC.
    exact (FOProvesTn_MP n _ _
      (FOPr_syl n
         (FOEq (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 1)))
               (FOSucc (FOVar 0)))
         (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0))
         FOFalseF)
      SC). }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind Hbase) Hstep).
Qed.

(** Irreflexivity of the strict order: [~ (a < a)].  Unfolds [FOLtF] to
    [exists w, a + S w = a], pushes the negation inside ([AllNegToNegEx]),
    and refutes [a + S w = a] by [Q]'s [plus_succ] composed with
    [neq_succ_add]. *)

Lemma FOPr_lt_irrefl : forall n,
  FOProvesTn n (FOForall 0 (FONeg (FOLtF (FOVar 0) (FOVar 0)))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply (FOProvesTn_MP n _ _ (FOProvesTn_AllNegToNegEx n 1
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOVar 0)))).
  apply FOProvesTn_Gen.
  assert (Hneq : FOProvesTn n
    (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0)))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 1)
         (FOForall 0 (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1)))
                                  (FOVar 0)))) eq_refl)
      (FOPr_neq_succ_add n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0)))
         eq_refl)
      H1). }
  exact (FOPr_compose n
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOVar 0))
    (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1))) (FOVar 0))
    FOFalseF
    (FOPr_imp_eq_trans_l n
       (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOVar 0))
       (FOSucc (FOPlus (FOVar 0) (FOVar 1)))
       (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
       (FOVar 0)
       (FOPr_eq_sym n _ _ (FOPr_q_plus_succ n (FOVar 0) (FOVar 1)))
       (FOPr_idf n (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOVar 0))))
    Hneq).
Qed.

(** [a < S a]: witness [w = 0], since [a + S 0 = S (a + 0) = S a]. *)

Lemma FOPr_lt_succ_self : forall n,
  FOProvesTn n (FOForall 0 (FOLtF (FOVar 0) (FOSucc (FOVar 0)))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply (FOProvesTn_MP n _ _ (FOProvesTn_ExIntroNum n 1 0
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOSucc (FOVar 0))))).
  cbn [FOsubst_num FOsubst_tm FOnumeral].
  apply (FOPr_eq_trans n _ (FOSucc (FOPlus (FOVar 0) FOZero)) _).
  - exact (FOPr_q_plus_succ n (FOVar 0) FOZero).
  - exact (FOPr_eq_congS n _ _ (FOPr_q_plus_zero n (FOVar 0))).
Qed.

(** [0 < S a]: witness [w = a], since [0 + S a = S a]. *)

Lemma FOPr_lt_zero_succ : forall n,
  FOProvesTn n (FOForall 0 (FOLtF FOZero (FOSucc (FOVar 0)))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply (FOProvesTn_MP n _ _ (FOProvesTn_ExIntroT n 1 (FOVar 0)
    (FOEq (FOPlus FOZero (FOSucc (FOVar 1))) (FOSucc (FOVar 0))) eq_refl)).
  cbn [FOsubst_f FOsubst_t Nat.eqb].
  exact (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n 0 (FOSucc (FOVar 0))
       (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)) eq_refl)
    (FOPr_zero_plus n)).
Qed.

(** Monotonicity [a < b -> a < S b]: eliminate the witness [w] of
    [a < b], then re-introduce [S w] as the witness of [a < S b] since
    [a + S (S w) = S (a + S w) = S b].  Validates the [ExElim]/[ExIntroT]
    pattern for the strict order. *)

Lemma FOPr_lt_succ : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOImplF (FOLtF (FOVar 0) (FOVar 1))
             (FOLtF (FOVar 0) (FOSucc (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_ExElim n 2
       (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
       (FOExists 2 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
                         (FOSucc (FOVar 1))))
       eq_refl)).
  apply FOProvesTn_Gen.
  apply (FOPr_compose n
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOSucc (FOVar 2)))) (FOSucc (FOVar 1)))
    (FOExists 2 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
                      (FOSucc (FOVar 1))))).
  - apply (FOPr_imp_eq_trans_l n
      (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
      (FOPlus (FOVar 0) (FOSucc (FOSucc (FOVar 2))))
      (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 2))))
      (FOSucc (FOVar 1))).
    + exact (FOPr_q_plus_succ n (FOVar 0) (FOSucc (FOVar 2))).
    + apply FOPr_imp_eq_congS.
      exact (FOPr_idf n (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
                              (FOVar 1))).
  - exact (FOProvesTn_ExIntroT n 2 (FOSucc (FOVar 2))
      (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOSucc (FOVar 1)))
      eq_refl).
Qed.

(** Successor monotonicity [a < b -> S a < S b]: the witness is
    unchanged, since [S a + S w = S (a + S w) = S b], so [FOPr_ex_mono]
    suffices (no witness re-introduction). *)

Lemma FOPr_lt_succ_mono : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOImplF (FOLtF (FOVar 0) (FOVar 1))
             (FOLtF (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply FOPr_ex_mono.
  apply FOProvesTn_Gen.
  assert (Hsp : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
          (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 2)))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
      (FOPr_succ_plus n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOSucc (FOVar 2))
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
      H1). }
  apply (FOPr_imp_eq_trans_l n
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
    (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
    (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 2))))
    (FOSucc (FOVar 1))).
  - exact Hsp.
  - apply FOPr_imp_eq_congS.
    exact (FOPr_idf n (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))).
Qed.

(** Successor cancellation [S x < S y -> x < y] (same witness): from
    [S x + S w = S y] strip the outer successor ([succ_inj]) to get
    [S x + w = y], then [S x + w = S (x + w)] and [x + S w = S (x + w)]
    give [x + S w = y]. *)

Lemma FOPr_succ_lt_succ : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOImplF (FOLtF (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
             (FOLtF (FOVar 0) (FOVar 1))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply FOPr_ex_mono.
  apply FOProvesTn_Gen.
  assert (Hsp : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
          (FOSucc (FOPlus (FOVar 0) (FOVar 2))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
      (FOPr_succ_plus n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 2)
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
      H1). }
  apply (FOPr_compose n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2))) (FOSucc (FOVar 1)))
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))).
  - apply (FOPr_compose n
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2))) (FOSucc (FOVar 1)))
      (FOEq (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 2))) (FOSucc (FOVar 1)))
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))).
    + apply (FOPr_imp_eq_trans_l n
        (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2))) (FOSucc (FOVar 1)))
        (FOSucc (FOPlus (FOSucc (FOVar 0)) (FOVar 2)))
        (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
        (FOSucc (FOVar 1))).
      * exact (FOPr_eq_sym n _ _
          (FOPr_q_plus_succ n (FOSucc (FOVar 0)) (FOVar 2))).
      * exact (FOPr_idf n (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
                                (FOSucc (FOVar 1)))).
    + exact (FOPr_q_succ_inj n (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)).
  - apply (FOPr_compose n
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
      (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 2))) (FOVar 1))
      (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))).
    + apply (FOPr_imp_eq_trans_l n
        (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
        (FOSucc (FOPlus (FOVar 0) (FOVar 2)))
        (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
        (FOVar 1)).
      * exact (FOPr_eq_sym n _ _ Hsp).
      * exact (FOPr_idf n (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
                                (FOVar 1))).
    + apply (FOPr_imp_eq_trans_l n
        (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 2))) (FOVar 1))
        (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
        (FOSucc (FOPlus (FOVar 0) (FOVar 2)))
        (FOVar 1)).
      * exact (FOPr_q_plus_succ n (FOVar 0) (FOVar 2)).
      * exact (FOPr_idf n (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 2)))
                                (FOVar 1))).
Qed.

(** [x + S w = S x + w] (both equal [S (x + w)]): the shift lemma used
    to move a [< ] witness across the successor, central to the
    trichotomy. *)

Lemma FOPr_x_succ_eq_succ_x : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
          (FOPlus (FOSucc (FOVar 0)) (FOVar 1))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  assert (Hsp : FOProvesTn n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
          (FOSucc (FOPlus (FOVar 0) (FOVar 1))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
      (FOPr_succ_plus n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 1)
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
               (FOSucc (FOPlus (FOVar 0) (FOVar 1)))) eq_refl)
      H1). }
  exact (FOPr_eq_trans n _ (FOSucc (FOPlus (FOVar 0) (FOVar 1))) _
           (FOPr_q_plus_succ n (FOVar 0) (FOVar 1))
           (FOPr_eq_sym n _ _ Hsp)).
Qed.

(** [~ (S a < a)]: a witness would give [S a + S w = a], hence
    [a + S (S w) = a] (shift) [= S (a + S w) = a], refuted by
    [neq_succ_add]. *)

Lemma FOPr_not_succ_lt_self : forall n,
  FOProvesTn n (FOForall 0 (FONeg (FOLtF (FOSucc (FOVar 0)) (FOVar 0)))).
Proof.
  intros n.
  apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  apply (FOProvesTn_MP n _ _ (FOProvesTn_AllNegToNegEx n 1
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1))) (FOVar 0)))).
  apply FOProvesTn_Gen.
  assert (Hshift : FOProvesTn n
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOSucc (FOVar 1))))
          (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1))))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
               (FOPlus (FOSucc (FOVar 0)) (FOVar 1)))) eq_refl)
      (FOPr_x_succ_eq_succ_x n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOSucc (FOVar 1))
         (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
               (FOPlus (FOSucc (FOVar 0)) (FOVar 1))) eq_refl)
      H1). }
  assert (Hneq : FOProvesTn n
    (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1)))) (FOVar 0)))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOSucc (FOVar 1))
         (FOForall 0 (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOVar 1)))
                                  (FOVar 0)))) eq_refl)
      (FOPr_neq_succ_add n)) as H1.
    exact (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FONeg (FOEq (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1))))
                      (FOVar 0))) eq_refl)
      H1). }
  apply (FOPr_compose n
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1))) (FOVar 0))
    (FOEq (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1)))) (FOVar 0))
    FOFalseF).
  - apply (FOPr_imp_eq_trans_l n
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1))) (FOVar 0))
      (FOSucc (FOPlus (FOVar 0) (FOSucc (FOVar 1))))
      (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
      (FOVar 0)).
    + apply (FOPr_eq_trans n _
        (FOPlus (FOVar 0) (FOSucc (FOSucc (FOVar 1)))) _).
      * exact (FOPr_eq_sym n _ _
          (FOPr_q_plus_succ n (FOVar 0) (FOSucc (FOVar 1)))).
      * exact Hshift.
    + exact (FOPr_idf n (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))
                              (FOVar 0))).
  - exact Hneq.
Qed.

(** Two building blocks for the successor-trichotomy.  From [t + w = b]:
    if [w = 0] then [t = b]; and [S x + S y = b] gives [S x < b]
    (existential introduction at witness [y]). *)

Lemma FOPr_eq_of_add_zero : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOImplF (FOEq (FOVar 2) FOZero)
       (FOImplF (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 1))
                (FOEq (FOVar 0) (FOVar 1))))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  assert (He : FOProvesTn n
    (FOImplF (FOEq (FOVar 2) FOZero)
             (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 0)))).
  { apply (FOPr_imp_eq_trans_r n (FOEq (FOVar 2) FOZero)
      (FOPlus (FOVar 0) (FOVar 2)) (FOPlus (FOVar 0) FOZero) (FOVar 0)).
    - apply (FOPr_imp_eq_congPlus_r n (FOEq (FOVar 2) FOZero)
        (FOVar 0) (FOVar 2) FOZero).
      exact (FOPr_idf n (FOEq (FOVar 2) FOZero)).
    - exact (FOPr_q_plus_zero n (FOVar 0)). }
  exact (FOPr_compose n (FOEq (FOVar 2) FOZero)
    (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 0))
    (FOImplF (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 1))
             (FOEq (FOVar 0) (FOVar 1)))
    He
    (FOPr_compose n
       (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 0))
       (FOEq (FOVar 0) (FOPlus (FOVar 0) (FOVar 2)))
       (FOImplF (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 1))
                (FOEq (FOVar 0) (FOVar 1)))
       (FOProvesTn_EqSym n (FOPlus (FOVar 0) (FOVar 2)) (FOVar 0))
       (FOProvesTn_EqTrans n (FOVar 0) (FOPlus (FOVar 0) (FOVar 2))
          (FOVar 1)))).
Qed.

Lemma FOPr_lt_of_add_succ : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1 (FOForall 2
    (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2))) (FOVar 1))
             (FOLtF (FOSucc (FOVar 0)) (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  exact (FOProvesTn_ExIntroT n 2 (FOVar 2)
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2))) (FOVar 1)) eq_refl).
Qed.

(** Successor-trichotomy [x < b -> S x < b \/ S x = b], the Euclidean
    division gateway.  Eliminate the witness [w] of [x < b], shift it to
    [S x + w = b], then case on [w] ([Q] zero-or-succ): [w = 0] gives
    [S x = b] ([eq_of_add_zero]); [w = S y] gives [S x < b]
    ([lt_of_add_succ]). *)

Lemma FOPr_lt_succ_trichotomy : forall n,
  FOProvesTn n (FOForall 0 (FOForall 1
    (FOImplF (FOLtF (FOVar 0) (FOVar 1))
       (FOOr (FOLtF (FOSucc (FOVar 0)) (FOVar 1))
             (FOEq (FOSucc (FOVar 0)) (FOVar 1)))))).
Proof.
  intros n.
  apply FOProvesTn_Gen. apply FOProvesTn_Gen.
  unfold FOLtF. cbn [FOmax_var_tm Nat.max].
  pose (PSI := FOOr (FOExists 2 (FOEq (FOPlus (FOSucc (FOVar 0))
                                        (FOSucc (FOVar 2))) (FOVar 1)))
                    (FOEq (FOSucc (FOVar 0)) (FOVar 1))).
  apply (FOProvesTn_MP n _ _
    (FOProvesTn_ExElim n 2
       (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1)) PSI eq_refl)).
  apply FOProvesTn_Gen.
  (* goal: (x + S w = b) -> PSI   [w = v2] *)
  assert (U2 : FOProvesTn n
    (FOImplF (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
             (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 0 (FOVar 0)
         (FOForall 1 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
               (FOPlus (FOSucc (FOVar 0)) (FOVar 1)))) eq_refl)
      (FOPr_x_succ_eq_succ_x n)) as Hxe1.
    pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 2)
         (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
               (FOPlus (FOSucc (FOVar 0)) (FOVar 1))) eq_refl)
      Hxe1) as Hxe.
    apply (FOPr_imp_eq_trans_l n
      (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
      (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
      (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
      (FOVar 1)).
    - exact (FOPr_eq_sym n _ _ Hxe).
    - exact (FOPr_idf n (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2)))
                              (FOVar 1))). }
  assert (Hz : FOProvesTn n
    (FOImplF (FOEq (FOVar 2) FOZero)
       (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)) PSI))).
  { pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 1 (FOVar 1)
         (FOForall 2 (FOImplF (FOEq (FOVar 2) FOZero)
            (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
                     (FOEq (FOSucc (FOVar 0)) (FOVar 1))))) eq_refl)
      (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 0 (FOSucc (FOVar 0))
           (FOForall 1 (FOForall 2 (FOImplF (FOEq (FOVar 2) FOZero)
              (FOImplF (FOEq (FOPlus (FOVar 0) (FOVar 2)) (FOVar 1))
                       (FOEq (FOVar 0) (FOVar 1)))))) eq_refl)
        (FOPr_eq_of_add_zero n))) as Hz0.
    pose proof (FOProvesTn_MP n _ _
      (FOProvesTn_AllElimT n 2 (FOVar 2)
         (FOImplF (FOEq (FOVar 2) FOZero)
            (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
                     (FOEq (FOSucc (FOVar 0)) (FOVar 1)))) eq_refl)
      Hz0) as Hz1.
    exact (FOPr_mp2 n _ _ _
      (FOPr_compose2 n (FOEq (FOVar 2) FOZero)
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
         (FOEq (FOSucc (FOVar 0)) (FOVar 1)) PSI)
      Hz1
      (FOPr_or_intro_r n
         (FOExists 2 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
                           (FOVar 1)))
         (FOEq (FOSucc (FOVar 0)) (FOVar 1)))). }
  assert (Hs : FOProvesTn n
    (FOImplF (FOExists 3 (FOEq (FOVar 2) (FOSucc (FOVar 3))))
       (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)) PSI))).
  { apply (FOProvesTn_MP n _ _
      (FOProvesTn_ExElim n 3 (FOEq (FOVar 2) (FOSucc (FOVar 3)))
         (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)) PSI)
         eq_refl)).
    apply FOProvesTn_Gen.
    pose proof (FOPr_compose n
      (FOEq (FOVar 2) (FOSucc (FOVar 3)))
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
            (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))))
      (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
               (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))) (FOVar 1)))
      (FOPr_imp_eq_congPlus_r n (FOEq (FOVar 2) (FOSucc (FOVar 3)))
         (FOSucc (FOVar 0)) (FOVar 2) (FOSucc (FOVar 3))
         (FOPr_idf n (FOEq (FOVar 2) (FOSucc (FOVar 3)))))
      (FOPr_compose n
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
               (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))))
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3)))
               (FOPlus (FOSucc (FOVar 0)) (FOVar 2)))
         (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
                  (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))) (FOVar 1)))
         (FOProvesTn_EqSym n (FOPlus (FOSucc (FOVar 0)) (FOVar 2))
            (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))))
         (FOProvesTn_EqTrans n
            (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3)))
            (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)))) as Leib.
    pose proof (FOPr_compose n
      (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))) (FOVar 1))
      (FOLtF (FOSucc (FOVar 0)) (FOVar 1)) PSI
      (FOProvesTn_MP n _ _
        (FOProvesTn_AllElimT n 2 (FOVar 3)
           (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
                          (FOVar 1))
              (FOLtF (FOSucc (FOVar 0)) (FOVar 1))) eq_refl)
        (FOProvesTn_MP n _ _
          (FOProvesTn_AllElimT n 1 (FOVar 1)
             (FOForall 2 (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0))
                  (FOSucc (FOVar 2))) (FOVar 1))
                (FOLtF (FOSucc (FOVar 0)) (FOVar 1)))) eq_refl)
          (FOProvesTn_MP n _ _
            (FOProvesTn_AllElimT n 0 (FOVar 0)
               (FOForall 1 (FOForall 2 (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0))
                    (FOSucc (FOVar 2))) (FOVar 1))
                  (FOLtF (FOSucc (FOVar 0)) (FOVar 1))))) eq_refl)
            (FOPr_lt_of_add_succ n))))
      (FOPr_or_intro_l n
         (FOExists 2 (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 2)))
                           (FOVar 1)))
         (FOEq (FOSucc (FOVar 0)) (FOVar 1)))) as P1.
    exact (FOPr_mp2 n _ _ _
      (FOPr_compose2 n (FOEq (FOVar 2) (FOSucc (FOVar 3)))
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1))
         (FOEq (FOPlus (FOSucc (FOVar 0)) (FOSucc (FOVar 3))) (FOVar 1)) PSI)
      Leib P1). }
  apply (FOPr_compose n
    (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 2))) (FOVar 1))
    (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)) PSI U2).
  exact (FOPr_case n (FOEq (FOVar 2) FOZero)
    (FOExists 3 (FOEq (FOVar 2) (FOSucc (FOVar 3))))
    (FOImplF (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 2)) (FOVar 1)) PSI)
    (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_zero_or_succ 2)))
    Hz Hs).
Qed.

(** Both sides of an equation discharged under a common hypothesis:
    symmetry and transitivity in the [H -> _] reader, composed from the
    bare [EqSym]/[EqTrans] axioms.  These shrink the equational chains in
    the Euclidean-division step, where every fact arrives as an
    antecedent (a conjunct of the body or the witness equation) rather
    than as a standalone theorem. *)

Lemma FOPr_imp_eq_sym : forall n H a b,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOImplF H (FOEq b a)).
Proof.
  intros n H a b Hab.
  exact (FOPr_compose n H (FOEq a b) (FOEq b a) Hab
           (FOProvesTn_EqSym n a b)).
Qed.

Lemma FOPr_imp_eq_trans : forall n H a b c,
  FOProvesTn n (FOImplF H (FOEq a b)) ->
  FOProvesTn n (FOImplF H (FOEq b c)) ->
  FOProvesTn n (FOImplF H (FOEq a c)).
Proof.
  intros n H a b c Hab Hbc.
  exact (FOPr_under_mp n H (FOEq b c) (FOEq a c)
           (FOPr_compose n H (FOEq a b)
              (FOImplF (FOEq b c) (FOEq a c)) Hab
              (FOProvesTn_EqTrans n a b c))
           Hbc).
Qed.

(** Conjunction introduction under a common hypothesis. *)
Lemma FOPr_imp_and : forall n H A B,
  FOProvesTn n (FOImplF H A) -> FOProvesTn n (FOImplF H B) ->
  FOProvesTn n (FOImplF H (FOAnd A B)).
Proof.
  intros n H A B HA HB.
  assert (T : FOProvesTn n (FOImplF A (FOImplF B (FOAnd A B)))).
  { apply (FOPr_taut n (FOm2 A B)
      (Impl (Var 0) (Impl (Var 1) (And (Var 0) (Var 1)))));
      [cbn; tauto | reflexivity]. }
  exact (FOPr_under_mp n H B (FOAnd A B)
           (FOPr_compose n H A (FOImplF B (FOAnd A B)) HA T) HB).
Qed.

(** ** Euclidean division, object level.

    [T_n] internally proves that every dividend [a] splits against a
    positive divisor [S b] into a quotient [q] and a remainder [r] strictly
    below [S b].  The proof is object-level induction on [a] (the
    [FOAx_Ind] schema at variable [0]); the step decides, via the successor
    case-split [RQ_zero_or_succ] applied to the witness of the inductive
    remainder bound, whether the bumped remainder [S r] still fits below
    [S b] (keep the quotient, advance the remainder) or has reached it
    (advance the quotient, reset the remainder to zero).  Every equational
    fact in the step arrives as an antecedent (a conjunct of the body or
    the witness equation), so the chains run through the
    hypothesis-discharged [FOPr_imp_eq_*] reader.  This is the arithmetic
    ground floor for gcd / Bezout / CRT and the beta-function existence
    lemma, hence for provable Sigma_1 completeness. *)

Section Div.

Local Notation SB := (FOSucc (FOVar 1)).
Local Notation CJ1 :=
  (FOEq (FOVar 0) (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3))).
Local Notation CJ1S :=
  (FOEq (FOSucc (FOVar 0))
        (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3))).
Local Notation LTR := (FOLtF (FOVar 3) (FOSucc (FOVar 1))).
Local Notation P4 :=
  (FOEq (FOPlus (FOVar 3) (FOSucc (FOVar 4))) (FOSucc (FOVar 1))).
Local Notation BODY := (FOAnd CJ1 LTR).
Local Notation BODYS := (FOAnd CJ1S LTR).
Local Notation MAT := (FOExists 2 (FOExists 3 BODY)).
Local Notation CONCL := (FOExists 2 (FOExists 3 BODYS)).
Local Notation BODY0 :=
  (FOAnd (FOEq FOZero (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3)))
         LTR).
Local Notation Z4 := (FOEq (FOVar 4) FOZero).

Lemma FOPr_div_exists : forall n,
  FOProvesTn n (FOForall 1 (FOForall 0 MAT)).
Proof.
  intro n.
  apply FOProvesTn_Gen.
  pose proof (FOProvesTn_ax n _ (FOAx_Ind n 0 MAT)) as Hind.
  unfold FOInduction in Hind.
  (* ---- base case: a = 0, witnesses q = 0, r = 0 ---- *)
  assert (BASE : FOProvesTn n (FOExists 2 (FOExists 3 BODY0))).
  { assert (bc1 : FOProvesTn n
      (FOEq FOZero (FOPlus (FOMult (FOSucc (FOVar 1)) FOZero) FOZero))).
    { apply FOPr_eq_sym.
      exact (FOPr_eq_trans n
        (FOPlus (FOMult (FOSucc (FOVar 1)) FOZero) FOZero)
        (FOMult (FOSucc (FOVar 1)) FOZero) FOZero
        (FOPr_q_plus_zero n (FOMult (FOSucc (FOVar 1)) FOZero))
        (FOPr_q_mult_zero n (FOSucc (FOVar 1)))). }
    assert (bc2 : FOProvesTn n
      (FOExists 4 (FOEq (FOPlus FOZero (FOSucc (FOVar 4))) (FOSucc (FOVar 1))))).
    { apply (FOProvesTn_MP n _ _
        (FOProvesTn_ExIntroT n 4 (FOVar 1)
           (FOEq (FOPlus FOZero (FOSucc (FOVar 4))) (FOSucc (FOVar 1))) eq_refl)).
      exact (FOPr_eq_trans n
        (FOPlus FOZero (FOSucc (FOVar 1)))
        (FOSucc (FOPlus FOZero (FOVar 1)))
        (FOSucc (FOVar 1))
        (FOPr_q_plus_succ n FOZero (FOVar 1))
        (FOPr_eq_congS n (FOPlus FOZero (FOVar 1)) (FOVar 1)
          (FOProvesTn_MP n _ _
            (FOProvesTn_AllElimT n 0 (FOVar 1)
               (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)) eq_refl)
            (FOPr_zero_plus n)))). }
    assert (bbody : FOProvesTn n
      (FOAnd (FOEq FOZero (FOPlus (FOMult (FOSucc (FOVar 1)) FOZero) FOZero))
             (FOExists 4
                (FOEq (FOPlus FOZero (FOSucc (FOVar 4))) (FOSucc (FOVar 1)))))).
    { exact (FOPr_and_intro n _ _ bc1 bc2). }
    apply (FOProvesTn_MP n _ _
      (FOProvesTn_ExIntroT n 2 FOZero (FOExists 3 BODY0) eq_refl)).
    apply (FOProvesTn_MP n _ _
      (FOProvesTn_ExIntroT n 3 FOZero
         (FOAnd (FOEq FOZero (FOPlus (FOMult (FOSucc (FOVar 1)) FOZero) (FOVar 3)))
                LTR) eq_refl)).
    exact bbody. }
  (* ---- step case ---- *)
  assert (STEP : FOProvesTn n (FOForall 0 (FOImplF MAT CONCL))).
  { apply FOProvesTn_Gen.
    (* core : BODY -> CONCL *)
    assert (core : FOProvesTn n (FOImplF BODY CONCL)).
    { (* Core2 : CJ1 -> (LTR -> CONCL) *)
      assert (Core3 : FOProvesTn n (FOImplF CJ1 (FOImplF P4 CONCL))).
      { (* armZ : Z4 -> (CJ1 -> (P4 -> CONCL)) ; witnesses q=Sv2, r=0 *)
        assert (armZ : FOProvesTn n
          (FOImplF Z4 (FOImplF CJ1 (FOImplF P4 CONCL)))).
        { assert (hz : FOProvesTn n (FOImplF (FOAnd Z4 (FOAnd CJ1 P4)) Z4)).
          { exact (FOPr_and_elim_l n Z4 (FOAnd CJ1 P4)). }
          assert (hr : FOProvesTn n
            (FOImplF (FOAnd Z4 (FOAnd CJ1 P4)) (FOAnd CJ1 P4))).
          { exact (FOPr_and_elim_r n Z4 (FOAnd CJ1 P4)). }
          assert (hc1 : FOProvesTn n (FOImplF (FOAnd Z4 (FOAnd CJ1 P4)) CJ1)).
          { exact (FOPr_compose n _ _ _ hr (FOPr_and_elim_l n CJ1 P4)). }
          assert (hp : FOProvesTn n (FOImplF (FOAnd Z4 (FOAnd CJ1 P4)) P4)).
          { exact (FOPr_compose n _ _ _ hr (FOPr_and_elim_r n CJ1 P4)). }
          (* t5 : H -> (S r = S b) *)
          assert (t5 : FOProvesTn n
            (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
               (FOEq (FOSucc (FOVar 3)) (FOSucc (FOVar 1))))).
          { assert (t1 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOSucc (FOVar 4)) (FOSucc FOZero)))).
            { exact (FOPr_imp_eq_congS n _ (FOVar 4) FOZero hz). }
            assert (t2 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOPlus (FOVar 3) (FOSucc (FOVar 4)))
                       (FOPlus (FOVar 3) (FOSucc FOZero))))).
            { exact (FOPr_imp_eq_congPlus_r n _ (FOVar 3)
                       (FOSucc (FOVar 4)) (FOSucc FOZero) t1). }
            assert (t3 : FOProvesTn n
              (FOEq (FOPlus (FOVar 3) (FOSucc FOZero)) (FOSucc (FOVar 3)))).
            { exact (FOPr_eq_trans n
                (FOPlus (FOVar 3) (FOSucc FOZero))
                (FOSucc (FOPlus (FOVar 3) FOZero))
                (FOSucc (FOVar 3))
                (FOPr_q_plus_succ n (FOVar 3) FOZero)
                (FOPr_eq_congS n (FOPlus (FOVar 3) FOZero) (FOVar 3)
                   (FOPr_q_plus_zero n (FOVar 3)))). }
            assert (t4 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOPlus (FOVar 3) (FOSucc (FOVar 4))) (FOSucc (FOVar 3))))).
            { exact (FOPr_imp_eq_trans_r n _ _ _ _ t2 t3). }
            exact (FOPr_imp_eq_trans n _ _ _ _ (FOPr_imp_eq_sym n _ _ _ t4) hp). }
          (* H1 : H -> (S a = (S b)*(S q) + 0) *)
          assert (H1 : FOProvesTn n
            (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
               (FOEq (FOSucc (FOVar 0))
                  (FOPlus (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))
                          FOZero)))).
          { assert (s1 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOSucc (FOVar 0))
                    (FOSucc (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                                    (FOVar 3)))))).
            { exact (FOPr_imp_eq_congS n _ (FOVar 0)
                       (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3))
                       hc1). }
            assert (s2 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOSucc (FOVar 0))
                    (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                            (FOSucc (FOVar 3)))))).
            { exact (FOPr_imp_eq_trans_r n _ _ _ _ s1
                       (FOPr_eq_sym n _ _
                          (FOPr_q_plus_succ n
                             (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3)))). }
            assert (s3 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                               (FOSucc (FOVar 3)))
                       (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                               (FOSucc (FOVar 1)))))).
            { exact (FOPr_imp_eq_congPlus_r n _
                       (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                       (FOSucc (FOVar 3)) (FOSucc (FOVar 1)) t5). }
            assert (s4 : FOProvesTn n
              (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
                 (FOEq (FOSucc (FOVar 0))
                    (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                            (FOSucc (FOVar 1)))))).
            { exact (FOPr_imp_eq_trans n _ _ _ _ s2 s3). }
            assert (ms : FOProvesTn n
              (FOEq (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                            (FOSucc (FOVar 1)))
                    (FOPlus (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))
                            FOZero))).
            { exact (FOPr_eq_trans n
                (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOSucc (FOVar 1)))
                (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))
                (FOPlus (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2))) FOZero)
                (FOPr_eq_sym n _ _
                   (FOPr_q_mult_succ n (FOSucc (FOVar 1)) (FOVar 2)))
                (FOPr_eq_sym n _ _
                   (FOPr_q_plus_zero n
                      (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))))). }
            exact (FOPr_imp_eq_trans_r n _ _ _ _ s4 ms). }
          (* H2 : H -> 0 < S b  (binder 4) *)
          assert (H2 : FOProvesTn n
            (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
               (FOExists 4
                  (FOEq (FOPlus FOZero (FOSucc (FOVar 4))) (FOSucc (FOVar 1)))))).
          { apply (FOPr_weaken n _ (FOAnd Z4 (FOAnd CJ1 P4))).
            apply (FOProvesTn_MP n _ _
              (FOProvesTn_ExIntroT n 4 (FOVar 1)
                 (FOEq (FOPlus FOZero (FOSucc (FOVar 4))) (FOSucc (FOVar 1)))
                 eq_refl)).
            exact (FOPr_eq_trans n
              (FOPlus FOZero (FOSucc (FOVar 1)))
              (FOSucc (FOPlus FOZero (FOVar 1)))
              (FOSucc (FOVar 1))
              (FOPr_q_plus_succ n FOZero (FOVar 1))
              (FOPr_eq_congS n (FOPlus FOZero (FOVar 1)) (FOVar 1)
                (FOProvesTn_MP n _ _
                  (FOProvesTn_AllElimT n 0 (FOVar 1)
                     (FOEq (FOPlus FOZero (FOVar 0)) (FOVar 0)) eq_refl)
                  (FOPr_zero_plus n)))). }
          assert (asm : FOProvesTn n
            (FOImplF (FOAnd Z4 (FOAnd CJ1 P4))
               (FOAnd
                  (FOEq (FOSucc (FOVar 0))
                     (FOPlus (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))
                             FOZero))
                  (FOExists 4
                     (FOEq (FOPlus FOZero (FOSucc (FOVar 4)))
                           (FOSucc (FOVar 1))))))).
          { exact (FOPr_imp_and n _ _ _ H1 H2). }
          (* existentially introduce r:=0 then q:=S q *)
          assert (hcc : FOProvesTn n (FOImplF (FOAnd Z4 (FOAnd CJ1 P4)) CONCL)).
          { apply (FOPr_compose n _ _ _ asm).
            apply (FOPr_compose n _
              (FOExists 3
                 (FOAnd (FOEq (FOSucc (FOVar 0))
                           (FOPlus (FOMult (FOSucc (FOVar 1)) (FOSucc (FOVar 2)))
                                   (FOVar 3))) LTR))
              CONCL).
            - exact (FOProvesTn_ExIntroT n 3 FOZero
                       (FOAnd (FOEq (FOSucc (FOVar 0))
                                 (FOPlus (FOMult (FOSucc (FOVar 1))
                                            (FOSucc (FOVar 2))) (FOVar 3))) LTR)
                       eq_refl).
            - exact (FOProvesTn_ExIntroT n 2 (FOSucc (FOVar 2))
                       (FOExists 3 BODYS) eq_refl). }
          (* curry the bundle into Z4 -> CJ1 -> P4 -> CONCL *)
          apply (FOProvesTn_MP n _ _
            (FOPr_taut n (FOm4 Z4 CJ1 P4 CONCL)
               (Impl (Impl (And (Var 0) (And (Var 1) (Var 2))) (Var 3))
                     (Impl (Var 0) (Impl (Var 1) (Impl (Var 2) (Var 3)))))
               ltac:(cbn; tauto) eq_refl)).
          exact hcc. }
        (* armS : (exists w. v4 = S w) -> (CJ1 -> (P4 -> CONCL)) ; q=v2, r=S r *)
        assert (armS : FOProvesTn n
          (FOImplF (FOExists 5 (FOEq (FOVar 4) (FOSucc (FOVar 5))))
                   (FOImplF CJ1 (FOImplF P4 CONCL)))).
        { apply (FOProvesTn_MP n _ _
            (FOProvesTn_ExElim n 5 (FOEq (FOVar 4) (FOSucc (FOVar 5)))
               (FOImplF CJ1 (FOImplF P4 CONCL)) eq_refl)).
          apply FOProvesTn_Gen.
          (* inner: (v4 = S v5) -> (CJ1 -> (P4 -> CONCL)) *)
          pose (HS := FOAnd (FOEq (FOVar 4) (FOSucc (FOVar 5))) (FOAnd CJ1 P4)).
          assert (hv : FOProvesTn n
            (FOImplF HS (FOEq (FOVar 4) (FOSucc (FOVar 5))))).
          { exact (FOPr_and_elim_l n _ (FOAnd CJ1 P4)). }
          assert (hr : FOProvesTn n (FOImplF HS (FOAnd CJ1 P4))).
          { exact (FOPr_and_elim_r n (FOEq (FOVar 4) (FOSucc (FOVar 5)))
                     (FOAnd CJ1 P4)). }
          assert (hc1 : FOProvesTn n (FOImplF HS CJ1)).
          { exact (FOPr_compose n _ _ _ hr (FOPr_and_elim_l n CJ1 P4)). }
          assert (hp : FOProvesTn n (FOImplF HS P4)).
          { exact (FOPr_compose n _ _ _ hr (FOPr_and_elim_r n CJ1 P4)). }
          (* H1' : HS -> (S a = (S b)*v2 + S r) *)
          assert (H1' : FOProvesTn n
            (FOImplF HS
               (FOEq (FOSucc (FOVar 0))
                  (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                          (FOSucc (FOVar 3)))))).
          { assert (s1 : FOProvesTn n
              (FOImplF HS
                 (FOEq (FOSucc (FOVar 0))
                    (FOSucc (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                                    (FOVar 3)))))).
            { exact (FOPr_imp_eq_congS n _ (FOVar 0)
                       (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3))
                       hc1). }
            exact (FOPr_imp_eq_trans_r n _ _ _ _ s1
                     (FOPr_eq_sym n _ _
                        (FOPr_q_plus_succ n
                           (FOMult (FOSucc (FOVar 1)) (FOVar 2)) (FOVar 3)))). }
          (* H2eq : HS -> (S r + S v5 = S b) *)
          assert (H2eq : FOProvesTn n
            (FOImplF HS
               (FOEq (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 5)))
                     (FOSucc (FOVar 1))))).
          { (* u1 : HS -> (S b = v3 + S (S v5)) *)
            assert (u1 : FOProvesTn n
              (FOImplF HS
                 (FOEq (FOSucc (FOVar 1))
                    (FOPlus (FOVar 3) (FOSucc (FOSucc (FOVar 5))))))).
            { assert (a1 : FOProvesTn n
                (FOImplF HS
                   (FOEq (FOSucc (FOVar 1))
                         (FOPlus (FOVar 3) (FOSucc (FOVar 4)))))).
              { exact (FOPr_imp_eq_sym n _ _ _ hp). }
              assert (a2 : FOProvesTn n
                (FOImplF HS
                   (FOEq (FOSucc (FOVar 4)) (FOSucc (FOSucc (FOVar 5)))))).
              { exact (FOPr_imp_eq_congS n _ (FOVar 4) (FOSucc (FOVar 5)) hv). }
              assert (a3 : FOProvesTn n
                (FOImplF HS
                   (FOEq (FOPlus (FOVar 3) (FOSucc (FOVar 4)))
                         (FOPlus (FOVar 3) (FOSucc (FOSucc (FOVar 5))))))).
              { exact (FOPr_imp_eq_congPlus_r n _ (FOVar 3)
                         (FOSucc (FOVar 4)) (FOSucc (FOSucc (FOVar 5))) a2). }
              exact (FOPr_imp_eq_trans n _ _ _ _ a1 a3). }
            (* u2 : HS -> (S b = S (S (v3 + v5))) *)
            assert (u2 : FOProvesTn n
              (FOImplF HS
                 (FOEq (FOSucc (FOVar 1))
                       (FOSucc (FOSucc (FOPlus (FOVar 3) (FOVar 5))))))).
            { assert (f1 : FOProvesTn n
                (FOEq (FOPlus (FOVar 3) (FOSucc (FOSucc (FOVar 5))))
                      (FOSucc (FOSucc (FOPlus (FOVar 3) (FOVar 5)))))).
              { exact (FOPr_eq_trans n
                  (FOPlus (FOVar 3) (FOSucc (FOSucc (FOVar 5))))
                  (FOSucc (FOPlus (FOVar 3) (FOSucc (FOVar 5))))
                  (FOSucc (FOSucc (FOPlus (FOVar 3) (FOVar 5))))
                  (FOPr_q_plus_succ n (FOVar 3) (FOSucc (FOVar 5)))
                  (FOPr_eq_congS n (FOPlus (FOVar 3) (FOSucc (FOVar 5)))
                     (FOSucc (FOPlus (FOVar 3) (FOVar 5)))
                     (FOPr_q_plus_succ n (FOVar 3) (FOVar 5)))). }
              exact (FOPr_imp_eq_trans_r n _ _ _ _ u1 f1). }
            (* u4 : S r + S v5 = S (S (v3 + v5))   (fact) *)
            assert (u4 : FOProvesTn n
              (FOEq (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 5)))
                    (FOSucc (FOSucc (FOPlus (FOVar 3) (FOVar 5)))))).
            { exact (FOPr_eq_trans n
                (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 5)))
                (FOSucc (FOPlus (FOVar 3) (FOSucc (FOVar 5))))
                (FOSucc (FOSucc (FOPlus (FOVar 3) (FOVar 5))))
                (FOProvesTn_MP n _ _
                   (FOProvesTn_AllElimT n 1 (FOSucc (FOVar 5))
                      (FOEq (FOPlus (FOSucc (FOVar 3)) (FOVar 1))
                            (FOSucc (FOPlus (FOVar 3) (FOVar 1)))) eq_refl)
                   (FOProvesTn_MP n _ _
                      (FOProvesTn_AllElimT n 0 (FOVar 3)
                         (FOForall 1
                            (FOEq (FOPlus (FOSucc (FOVar 0)) (FOVar 1))
                                  (FOSucc (FOPlus (FOVar 0) (FOVar 1))))) eq_refl)
                      (FOPr_succ_plus n)))
                (FOPr_eq_congS n (FOPlus (FOVar 3) (FOSucc (FOVar 5)))
                   (FOSucc (FOPlus (FOVar 3) (FOVar 5)))
                   (FOPr_q_plus_succ n (FOVar 3) (FOVar 5)))). }
            exact (FOPr_imp_eq_trans_l n _ _ _ _ u4
                     (FOPr_imp_eq_sym n _ _ _ u2)). }
          (* H2' : HS -> exists w. S r + S w = S b   (binder 4) *)
          assert (H2' : FOProvesTn n
            (FOImplF HS
               (FOExists 4
                  (FOEq (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 4)))
                        (FOSucc (FOVar 1)))))).
          { exact (FOPr_compose n _ _ _ H2eq
                     (FOProvesTn_ExIntroT n 4 (FOVar 5)
                        (FOEq (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 4)))
                              (FOSucc (FOVar 1))) eq_refl)). }
          assert (asm : FOProvesTn n
            (FOImplF HS
               (FOAnd
                  (FOEq (FOSucc (FOVar 0))
                     (FOPlus (FOMult (FOSucc (FOVar 1)) (FOVar 2))
                             (FOSucc (FOVar 3))))
                  (FOExists 4
                     (FOEq (FOPlus (FOSucc (FOVar 3)) (FOSucc (FOVar 4)))
                           (FOSucc (FOVar 1))))))).
          { exact (FOPr_imp_and n _ _ _ H1' H2'). }
          assert (hcc : FOProvesTn n (FOImplF HS CONCL)).
          { apply (FOPr_compose n _ _ _ asm).
            apply (FOPr_compose n _ (FOExists 3 BODYS) CONCL).
            - exact (FOProvesTn_ExIntroT n 3 (FOSucc (FOVar 3))
                       (FOAnd CJ1S LTR) eq_refl).
            - exact (FOProvesTn_ExIntroT n 2 (FOVar 2)
                       (FOExists 3 BODYS) eq_refl). }
          apply (FOProvesTn_MP n _ _
            (FOPr_taut n (FOm4 (FOEq (FOVar 4) (FOSucc (FOVar 5))) CJ1 P4 CONCL)
               (Impl (Impl (And (Var 0) (And (Var 1) (Var 2))) (Var 3))
                     (Impl (Var 0) (Impl (Var 1) (Impl (Var 2) (Var 3)))))
               ltac:(cbn; tauto) eq_refl)).
          exact hcc. }
        (* combine the two arms via RQ zero-or-succ on the witness v4 *)
        exact (FOPr_case n Z4
                 (FOExists 5 (FOEq (FOVar 4) (FOSucc (FOVar 5))))
                 (FOImplF CJ1 (FOImplF P4 CONCL))
                 (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_zero_or_succ 4)))
                 armZ armS). }
      (* lift Core3 over the existential bound in CJ2 = exists w. P4 *)
      assert (Core2 : FOProvesTn n (FOImplF CJ1 (FOImplF LTR CONCL))).
      { apply (FOPr_compose n CJ1
                 (FOForall 4 (FOImplF P4 CONCL))
                 (FOImplF LTR CONCL)).
        - exact (FOProvesTn_MP n _ _
                   (FOProvesTn_AllExport n 4 CJ1 (FOImplF P4 CONCL) eq_refl)
                   (FOProvesTn_Gen n 4 _ Core3)).
        - exact (FOProvesTn_ExElim n 4 P4 CONCL eq_refl). }
      exact (FOPr_under_mp n BODY LTR CONCL
               (FOPr_compose n BODY CJ1 (FOImplF LTR CONCL)
                  (FOPr_and_elim_l n CJ1 LTR) Core2)
               (FOPr_and_elim_r n CJ1 LTR)). }
    (* assemble step: generalise over the two existential layers *)
    apply (FOProvesTn_MP n _ _
      (FOProvesTn_ExElim n 2 (FOExists 3 BODY) CONCL eq_refl)).
    apply FOProvesTn_Gen.
    apply (FOProvesTn_MP n _ _
      (FOProvesTn_ExElim n 3 BODY CONCL eq_refl)).
    apply FOProvesTn_Gen.
    exact core. }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Hind BASE) STEP).
Qed.

End Div.

(** ** Stratified soundness of the tower.

    Robinson axioms hold in the standard model outright.  Soundness
    of [T_n] is by strong induction on the level: a reflection axiom
    at [k < n] discharges through the representability bridge into
    the level-[k] soundness, and the Loeb rule's conclusion re-enters
    as the truth of its own provability sentence. *)

Lemma FORobinsonQ_sat : forall A e, FORobinsonQ A -> FOsat e A.
Proof.
  intros A e H.
  destruct H as [a b|a|x|a|a b|a|a b]; cbn.
  - lia.
  - lia.
  - intro H0. exists (Nat.pred (e x)).
    unfold FOupdate.
    rewrite Nat.eqb_refl.
    assert (Ex : Nat.eqb x (S x) = false)
      by (apply Nat.eqb_neq; lia).
    rewrite Ex. cbn. lia.
  - lia.
  - lia.
  - nia.
  - nia.
Qed.

Theorem FOProvesTn_sound : forall n A,
  FOProvesTn n A -> forall e, FOsat e A.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros A H. induction H; intro e.
  - match goal with
    | HA : FOAxiomTn _ _ |- _ => inversion HA; subst
    end.
    + apply FORobinsonQ_sat. assumption.
    + cbn [FOsat]. intro Hp.
      match goal with
      | Hk : ?k < n, Hp2 : FOsat ?e0 (FOProvSentence ?k ?B0)
        |- FOsat ?e0 ?B0 =>
          exact (IHn k Hk B0
                   (proj1 (FOProvSentence_sat_iff e0 k B0) Hp2) e0)
      end.
    + cbn [FOsat]. intros H1 H2.
      exact (FOHBL2_sat e _ _ _ H1 H2).
    + cbn [FOsat]. intro H1.
      exact (FOHBL3_sat e _ _ H1).
    + cbn [FOsat]. intro Hpm.
      eapply FOProv_sat_monotone; eassumption.
    + apply FOInduction_sat.
  - cbn. tauto.
  - cbn. tauto.
  - cbn. intro Hnn.
    destruct (classic (FOsat e phi)) as [Hp|Hnp];
      [exact Hp | exfalso; exact (Hnn Hnp)].
  - exact (IHFOProvesTn1 e (IHFOProvesTn2 e)).
  - cbn. intro v. exact (IHFOProvesTn (FOupdate e x v)).
  - cbn. reflexivity.
  - cbn. intro H1. symmetry. exact H1.
  - cbn. intros H1 H2. lia.
  - cbn. intro H1. rewrite H1. reflexivity.
  - cbn. intros H1 H2. rewrite H1, H2. reflexivity.
  - cbn. intros H1 H2. rewrite H1, H2. reflexivity.
  - cbn [FOsat]. intro Hall.
    apply (FOsat_subst_f phi x t e H).
    exact (Hall (FOeval e t)).
  - cbn [FOsat]. intro Hsub. exists (FOeval e t).
    exact (proj1 (FOsat_subst_f phi x t e H) Hsub).
  - cbn [FOsat]. intros Hall [v Hv].
    exact (proj1 (FOsat_update_not_free psi e x v H) (Hall v Hv)).
  - cbn [FOsat]. intros H1 H2 v. exact (H1 v (H2 v)).
  - cbn [FOsat]. intros H1 H2 v.
    apply (H1 v).
    refine (proj2 (FOsat_update_not_free _ e y v _) _); assumption.
  - exact (IHFOProvesTn e
      (FOHBL1_sat e n phi (FOProvesTn_Loeb n phi H))).
Qed.

Theorem FOProvesTn_consistent : forall n, ~ FOProvesTn n FOFalseF.
Proof.
  intros n H.
  exact (FOProvesTn_sound n FOFalseF H (fun _ => 0)).
Qed.

(** ** Goedel's second incompleteness theorem for the tower.

    The consistency assertion in its derivability form is the Loeb
    premise at falsity, so its provability would collapse the level;
    its truth is the consistency theorem read through the bridge. *)

Theorem FOGodel2 : forall n,
  ~ FOProvesTn n (FONeg (FOProvSentence n FOFalseF)).
Proof.
  intros n H.
  exact (FOProvesTn_consistent n (FOProvesTn_Loeb n FOFalseF H)).
Qed.

Theorem FOConSentenceF_true : forall e n,
  FOsat e (FONeg (FOProvSentence n FOFalseF)).
Proof.
  intros e n. cbn [FOsat]. intro Hp.
  exact (FOProvesTn_consistent n
    (proj1 (FOProvSentence_sat_iff e n FOFalseF) Hp)).
Qed.

Theorem FOConSentence_true : forall e n, FOsat e (FOConSentence n).
Proof.
  intros e n. unfold FOConSentence. cbn [FOsat]. intro Hp.
  apply (FOProvesTn_consistent n).
  apply (FOProvesTn_MP n FOTopFm FOFalseF).
  - exact (proj1 (FOProvSentence_sat_iff e n (FONeg FOTopFm)) Hp).
  - exact (FOPr_idf n FOFalseF).
Qed.

(** ** The arithmetic embedding of the polymodal language.

    [FOembed nu] interprets modal formulas over an atom assignment:
    implication and falsity map to their first-order counterparts and
    [Box n] maps to the level-[n] provability sentence.  Every axiom
    of GLP* embeds to a sentence true in the standard model, modus
    ponens preserves embedded truth, and necessitation transports
    derivability of the embedded formula. *)

Fixpoint FOembed (nu : nat -> FOFormula) (phi : Form) : FOFormula :=
  match phi with
  | Var p => nu p
  | Bot => FOFalseF
  | Impl a b => FOImplF (FOembed nu a) (FOembed nu b)
  | Box n psi => FOProvSentence n (FOembed nu psi)
  end.

Definition is_FO_arithmetic_interpretation
    (J : Form -> FOFormula) : Prop :=
  (forall a b, J (Impl a b) = FOImplF (J a) (J b)) /\
  (J Bot = FOFalseF) /\
  (forall n psi, J (Box n psi) = FOProvSentence n (J psi)).

Lemma FOembed_proper : forall nu,
  is_FO_arithmetic_interpretation (FOembed nu).
Proof.
  intro nu. split; [|split]; reflexivity.
Qed.

Lemma FO_interpretation_factors : forall J,
  is_FO_arithmetic_interpretation J ->
  forall phi, J phi = FOembed (fun p => J (Var p)) phi.
Proof.
  intros J HJ phi.
  destruct HJ as [HI [HB HX]].
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn [FOembed].
  - reflexivity.
  - exact HB.
  - rewrite HI, IHa, IHb. reflexivity.
  - rewrite HX, IHa. reflexivity.
Qed.

Theorem FOembed_Ax_K_valid : forall nu e phi psi,
  FOsat e (FOembed nu (Impl phi (Impl psi phi))).
Proof. intros. cbn. tauto. Qed.

Theorem FOembed_Ax_S_valid : forall nu e phi psi chi,
  FOsat e (FOembed nu (Impl (Impl phi (Impl psi chi))
                        (Impl (Impl phi psi) (Impl phi chi)))).
Proof. intros. cbn. tauto. Qed.

Theorem FOembed_Ax_DN_valid : forall nu e phi,
  FOsat e (FOembed nu (Impl (Neg (Neg phi)) phi)).
Proof.
  intros. cbn. intro Hnn.
  destruct (classic (FOsat e (FOembed nu phi))) as [Hp|Hnp];
    [exact Hp | exfalso; exact (Hnn Hnp)].
Qed.

Theorem FOembed_Ax_BoxK_valid : forall nu e n phi psi,
  FOsat e (FOembed nu (Impl (Box n (Impl phi psi))
                        (Impl (Box n phi) (Box n psi)))).
Proof.
  intros. cbn [FOembed FOsat]. intros H1 H2.
  exact (FOHBL2_sat e n _ _ H1 H2).
Qed.

Theorem FOembed_Ax_Loeb_valid : forall nu e n phi,
  FOsat e (FOembed nu (Impl (Box n (Impl (Box n phi) phi))
                        (Box n phi))).
Proof.
  intros. cbn [FOembed FOsat]. intro H1.
  exact (FOLoeb_sat e n _ H1).
Qed.

Theorem FOembed_Ax_Box4_valid : forall nu e n phi,
  FOsat e (FOembed nu (Impl (Box n phi) (Box n (Box n phi)))).
Proof.
  intros. cbn [FOembed FOsat]. intro H1.
  exact (FOHBL3_sat e n _ H1).
Qed.

Theorem FOembed_Ax_Mon_valid : forall nu e n phi,
  FOsat e (FOembed nu (Impl (Box n phi) (Box (S n) phi))).
Proof.
  intros. cbn [FOembed FOsat]. intro H1.
  exact (FOProv_sat_monotone e n (S n) _ (Nat.le_succ_diag_r n) H1).
Qed.

Theorem FOembed_Ax_NextCon_valid : forall nu e n,
  FOsat e (FOembed nu (Box (S n) (Neg (Box n Bot)))).
Proof.
  intros. cbn [FOembed].
  apply FOHBL1_sat.
  exact (FOProvesTn_ax (S n) _
           (FOAx_Refl (S n) n FOFalseF (Nat.lt_succ_diag_r n))).
Qed.

Theorem FOembed_MP_sat : forall nu e phi psi,
  FOsat e (FOembed nu (Impl phi psi)) ->
  FOsat e (FOembed nu phi) ->
  FOsat e (FOembed nu psi).
Proof. intros nu e phi psi H1 H2. exact (H1 H2). Qed.

Theorem FOembed_Nec_sat : forall nu e n phi,
  FOProvesTn n (FOembed nu phi) ->
  FOsat e (FOembed nu (Box n phi)).
Proof.
  intros nu e n phi H. cbn [FOembed]. apply FOHBL1_sat. exact H.
Qed.

Definition FOInconsistent (n : nat) : Prop := FOProvesTn n FOFalseF.


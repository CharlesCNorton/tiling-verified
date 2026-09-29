From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51 P52 P53 P54 P55.
Open Scope fo_scope.

(** ** Sigma_1 formulas. *)

Definition S1P (n k W : nat) (A : FOFormula) : Prop :=
  FOvars_max A < W ->
  forall V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall x, FOfree_in x A = true -> W <= h x) ->
  FOPrH n G (hsub_f h A) -> PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.

Lemma FOPr_ex_self : forall x A, FOProvesTn 0 (FOImplF A (FOExists x A)).
Proof.
  intros x A. change (FOPrH 0 [] (FOImplF A (FOExists x A))). apply FOPrH_intro.
  apply (FOPrH_ex_intro _ _ x (FOVar x)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_last.
Qed.

Lemma S1P_ex : forall n k W x A, S1P n k W A -> S1P n k W (FOExists x A).
Proof.
  intros n k W x A IHA HW V G h rho env HI Hhw HB. cbn [FOvars_max] in HW.
  assert (HWA : FOvars_max A < W) by lia.
  assert (HS : forall y, FOfree_in y (FOExists x A) = true <-> FOfree_in y A = true /\ y <> x).
  { intros y. cbn [FOfree_in]. destruct (Nat.eqb_spec x y) as [->|Hxy].
    - split; [discriminate | intros [_ H]; exfalso; exact (H eq_refl)].
    - split; [intros H; split; [exact H | lia] | intros [H _]; exact H]. }
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (HhA : forall y, FOfree_in y A = true -> y <> x -> HOK n G V h rho env y)
    by (intros y Hy Hyx; apply Hh; apply HS; split; assumption).
  cbn [hsub_f] in HB.
  refine (PRI_exe n _ _ V W G _ env x (hsub_f (h_hide x h) A) HB _ _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | | | |].
  - intros w Hw Hwx. exact (hA_free n G V h rho env x A w HhA ltac:(lia) Hwx).
  - intros w Hw Hwx. exact (hA_free n G V h rho env x A w HhA ltac:(lia) Hwx).
  - intros w Hw HWw. apply (hsub_f_ok A (h_hide x h) x (FOVar w) W HWA).
    intros w' Hw'. cbn [FOin_tm] in Hw'. apply Nat.eqb_eq in Hw'. lia.
  - intros w0 Hw0 HWw0.
    rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw z ltac:(apply HS; split; assumption));
                           lia).
    refine (PRI_numr_ex n _ _ (S w0) 0 _ _ env (FOVar w0) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
    intros w1 Hw1 _.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HA3 : FOPrH n G3 (hsub_f (h_upd x w0 h) A)) by wk_in;
      assert (N3 : FOPrH n G3 (FONUMR (FOVar w0) (FOVar w1))) by wk_in;
      assert (Hinc3 : forall X, In X G -> In X G3)
        by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX);
      assert (HG3 : FOctx_avoid G3 0 1000);
      [| assert (HG3V : forall w', S w1 <= w' -> FOfree_ctx w' G3)]
    end.
    { intros w' ? ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply HG0; lia|]|].
      - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (hsub_f (h_upd x w0 h) A)) eqn:E; [|reflexivity].
        destruct (FOfree_in_hsub A (h_upd x w0 h) w' E) as [y [Hy Ey]]. unfold h_upd in Ey.
        destruct (Nat.eqb_spec y x) as [->|Hyx]; [lia|].
        pose proof (HOK_range n G V h rho env y (HhA y Hy Hyx)). lia.
      - free_ctx. }
    { intros w' ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply HGV; lia|]|].
      - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (hsub_f (h_upd x w0 h) A)) eqn:E; [|reflexivity].
        destruct (FOfree_in_hsub A (h_upd x w0 h) w' E) as [y [Hy Ey]]. unfold h_upd in Ey.
        destruct (Nat.eqb_spec y x) as [->|Hyx]; [lia|].
        pose proof (HOK_range n G V h rho env y (HhA y Hy Hyx)). lia.
      - free_ctx. }
    pose proof (Inv_move n V (S w1) G _ h rho env _ HI Hinc3 ltac:(lia) HG3 HG3V) as HIm.
    pose proof (Inv_weaken n (S w1) _ h rho env _
                  (fun y => FOfree_in y A = true /\ y <> x) HIm
                  (fun y Hy => proj2 (HS y) Hy)) as HIm'.
    pose proof (Inv_holder n (S w1) _ h rho env (fun y => FOfree_in y A = true) x w0 (FOVar w1)
                  HIm' N3 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI3.
    pose proof (IHA HWA (S w1) _ _ _ _ HI3
                  ltac:(intros y Hy; unfold h_upd; destruct (Nat.eqb_spec y x) as [->|Hyx];
                        [exact HWw0 | apply Hhw; apply HS; split; assumption]) HA3) as TA.
    pose proof HI3 as [_ [_ [_ [HE3 [_ [Hr3 Hh3]]]]]].
    pose proof (PRI_thm_open n k (S w1) _ _ (rho_sub (Some x) (length env) rho) _
                  (FOPr_ex_self x A) HE3) as T.
    specialize (T ltac:(intros y Hy; cbn [FOfree_in] in Hy;
                        apply Bool.orb_true_iff in Hy; destruct Hy as [Hy|Hy];
                        [ destruct (Hh3 y Hy) as [i [Hyi [Hi _]]]; exists i; split; assumption
                        | destruct (Nat.eqb x y); [discriminate Hy|];
                          destruct (Hh3 y Hy) as [i [Hyi [Hi _]]]; exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w1) _ _ _ _ _ HE3 Hr3 T TA) as T1.
    refine (PRI_reslot n _ _ (S w1) _ _ _ rho _ env _ _ _ _ T1); [| above_tac | avoid_tms | lia].
    intros y Hy. unfold SlotAgree. apply HS in Hy. destruct Hy as [Hy Hyx].
    rewrite (rho_sub_ne x (length env) rho y Hyx).
    destruct (Hh y (proj2 (HS y) (conj Hy Hyx))) as [i [Hyi [Hi _]]].
    rewrite Hyi, (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.

Theorem S1P_all : forall n k W A, FOsigma1 A -> S1P n k W A.
Proof.
  intros n k W A HA. induction HA as [A HA | x A HA IH].
  - intros HW V G h rho env HI Hhw HB. exact (proj1 (D0P_all n k W A HA HW V G h rho env HI Hhw) HB).
  - exact (S1P_ex n k W x A IH).
Qed.

(** ** Sigma_1 sentences. *)

Lemma hsub_f_id : forall A h, (forall z, h z = z) -> hsub_f h A = A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h H; cbn [hsub_f].
  - assert (K : forall t, hsub_tm h t = t).
    { induction t as [z| |u IH|u IHu w IHw|u IHu w IHw]; cbn [hsub_tm];
        [rewrite H | | rewrite IH | rewrite IHu, IHw | rewrite IHu, IHw]; reflexivity. }
    rewrite !K. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact H. reflexivity.
  - rewrite IHB; [reflexivity|]. intros z. unfold h_hide. destruct (Nat.eqb_spec z y); auto.
  - rewrite IHB; [reflexivity|]. intros z. unfold h_hide. destruct (Nat.eqb_spec z y); auto.
Qed.

Lemma FOPRu_ProvSentence : forall k A,
  FOPRu (FOPrCores k) (FOu0 k) (FOnumeral (FOcode_f A)) = FOProvSentence k A.
Proof.
  intros k A. unfold FOPRu, FOu0. rewrite FOPRMATx_num, FOsubst_f_num.
  rewrite (FOsubst_num_comm (FOPRMAT (FOPrCores k)) 0 1) by lia. reflexivity.
Qed.

Theorem provable_sigma1_sentence : forall k A, FOsigma1 A ->
  (forall x, FOfree_in x A = false) ->
  FOProvesTn 0 (FOImplF A (FOProvSentence k A)).
Proof.
  intros k A HA Hcl.
  set (W := S (FOvars_max A)).
  set (V := 2000 + W).
  assert (HCA : forall w, FOfree_ctx w [A])
    by (intros w; apply FOfree_ctx_cons; [apply Hcl | apply FOfree_ctx_nil]).
  assert (HI : Inv 0 V [A] (fun z => z) (fun _ => None) [] (fun x => FOfree_in x A = true)).
  { split; [unfold V; lia|]. split; [intros w ? ?; apply HCA|]. split; [intros w ?; apply HCA|].
    split; [|split; [apply FOtms_avoid_nil | split; [intros z i Hz; discriminate Hz|]]].
    - split; [split; [intros w ? ?; apply HCA | intros i Hi; cbn in Hi; lia]|].
      split; [apply FOtms_avoid_nil|]. split; [unfold V; lia | intros t []].
    - intros x Hx. rewrite Hcl in Hx. discriminate Hx. }
  pose proof (S1P_all 0 k W A HA ltac:(unfold W; lia) V [A] (fun z => z) (fun _ => None) []
                HI ltac:(intros x Hx; rewrite Hcl in Hx; discriminate Hx)
                ltac:(rewrite (hsub_f_id A (fun z => z) (fun z => eq_refl));
                      apply FOPrH_assum; left; reflexivity)) as HP.
  pose proof (HP [A] V (FOnumeral (FOcode_f A)) (fun X HX => HX) ltac:(intros w ? ?; apply HCA)
                ltac:(avoid_tms) (le_n V)
                ltac:(split; [intros w _; apply HCA | intros t [<-|[]] w _; apply FOin_tm_numeral])
                (FOPrH_patf_closed_code 0 [A] A V ltac:(unfold V; lia))) as H.
  rewrite FOPRu_ProvSentence in H. exact H.
Qed.

(** ** The third derivability condition. *)

Theorem FOHBL3_internal : forall k A,
  FOProvesTn 0 (FOImplF (FOProvSentence k A) (FOProvSentence k (FOProvSentence k A))).
Proof.
  intros k A. apply provable_sigma1_sentence.
  - apply FOsigma1_FOProvSentence.
  - intros x. apply FOProvSentence_closed.
Qed.

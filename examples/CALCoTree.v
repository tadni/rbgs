(** * Certified abstraction layers on the coinductive tree model

  This is [examples/CALTree.v] again, on top of [models/ISpecCoTree.v].
  Equalities between specifications are now equivalences [[=]], and
  the state-threading operation [srun] is a corecursive map whose
  laws are proved by bisimulation. *)

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat Lia.
From Stdlib Require Import Morphisms RelationClasses Setoid.
Require Import coqrel.LogicalRelations.
Require Import structures.Effects.
Require Import models.ISpecCoTree.

Import ISpec.


(** * Preliminaries *)

Notation "x >>= f" := (bind f x)
  (at level 40, left associativity).

Notation "v <- x ; M" := (x >>= fun v => M)
  (at level 65, right associativity).

Definition assert {E : esig} (P : Prop) : t E unit :=
  sup H : P, ret tt.

Lemma sup_l_iff {E A I} (k : I -> t E A) y :
  Sup k [= y <-> forall i, k i [= y.
Proof.
  split.
  - intros H i. etransitivity; [ apply sup_ub | exact H ].
  - apply sup_lub.
Qed.

Lemma inf_r_iff {E A I} x (k : I -> t E A) :
  x [= Inf k <-> forall j, x [= k j.
Proof.
  split.
  - intros H j. etransitivity; [ exact H | apply inf_lb ].
  - apply inf_glb.
Qed.


(** * Effect signatures *)

Parameter val : Type.
Parameter N : nat.

Inductive rb_sig : esig :=
  | set (i : nat) (v : val) : rb_sig unit
  | get (i : nat) : rb_sig val
  | inc1 : rb_sig nat
  | inc2 : rb_sig nat.

Inductive bq_sig : esig :=
  | enq (v : val) : bq_sig unit
  | deq : bq_sig val.


(** * Layer implementation *)

Definition M_bq : rb_sig ~> bq_sig :=
  fun _ m =>
    match m with
      | enq v => i <- int inc2; int (set i v)
      | deq   => i <- int inc1; int (get i)
    end.


(** * Layer interfaces *)

Definition CALspec E S :=
  forall ar, E ar -> S -> t 0 (ar * S).

Definition update (f : nat -> val) (i : nat) (v : val) : nat -> val :=
  fun j => if Nat.eq_dec i j then v else f j.

Definition bq_state : Type :=
  list val.

Definition L_bq : CALspec bq_sig bq_state :=
  fun ar m vs =>
    match m with
      | enq v =>
        _ <- assert (length vs < N);
        ret (tt, vs ++ v :: nil)
      | deq =>
        match vs with
          | v::vs' => ret (v, vs')
          | nil => bot
        end
    end.

Definition rb_state : Type :=
  (nat -> val) * nat * nat.

Definition L_rb : CALspec rb_sig rb_state :=
  fun ar m '(f, c1, c2) =>
    match m with
      | set i v =>
        _ <- assert (E:=0) (i < N);
        ret (tt, (update f i v, c1, c2))
      | get i =>
        _ <- assert (E:=0) (i < N);
        ret (f i, (f, c1, c2))
      | inc1 =>
        ret (c1, (f, (S c1) mod N, c2))
      | inc2 =>
        ret (c2, (f, c1, (S c2) mod N))
    end.


(** * Layer interfaces and implementations as morphisms *)

(** ** Keeping track of state *)

Inductive state_sig (E : Type -> Type) (S : Type) : Type -> Type :=
  | st {ar} (m : E ar) (k : S) : state_sig E S (ar * S).

Arguments st {E S ar} m k.

Infix "#" := state_sig (at level 40, left associativity).

Coercion CALspec_mor {E S} (L : CALspec E S) : (0 ~> E # S) :=
  fun _ '(st m s) => L _ m s.

(** Running a specification with a state threaded through its
  interactions is a corecursive map over the tree. *)

Definition srun {E S A} : S -> t E A -> t (E # S) (A * S) :=
  cofix srun_ (k : S) (x : t E A) : t (E # S) (A * S) :=
    match observe x with
    | RetF a => ret (a, k)
    | VisF m κ => Vis (st m k) (fun p => srun_ (snd p) (κ (fst p)))
    | SupF κ => Sup (fun i => srun_ k (κ i))
    | InfF κ => Inf (fun i => srun_ k (κ i))
    end.

Definition srunF {E S A} (k : S) (o : tF E A (t E A)) : tF (E # S) (A * S) (t (E # S) (A * S)) :=
  match o with
  | RetF a => RetF (a, k)
  | VisF m κ => VisF (st m k) (fun p => srun (snd p) (κ (fst p)))
  | SupF κ => SupF (fun i => srun k (κ i))
  | InfF κ => InfF (fun i => srun k (κ i))
  end.

Lemma observe_srun {E S A} (k : S) (x : t E A) :
  observe (srun k x) = srunF k (observe x).
Proof. destruct x as [ox]. destruct ox; reflexivity. Qed.

Definition slift {E F S} (σ : E ~> F) : E#S ~> F#S :=
  fun ar m =>
    match m with st m k => srun k (σ _ m) end.

Definition run_layer {E F S} (M : E ~> F) (L : 0 ~> E#S) : 0 ~> F#S :=
  slift M @ L.

(** ** Properties *)

Lemma srun_mono {E S A} (k : S) (x y : t E A) :
  x [= y -> srun k x [= srun k y.
Proof.
  intros H.
  pose (R := fun u v => exists (k : S) (x y : t E A),
               observe u = srunF k (observe x) /\ observe v = srunF k (observe y) /\ x [= y).
  apply (ref_coind_up R).
  2: { exists k, x, y. split; [ apply observe_srun | ]. split; [ apply observe_srun | ]. exact H. }
  clear k x y H. intros u v H. hnf in H. destruct H as (k & x & y & Hu & Hv & Hxy).
  rewrite Hu, Hv. clear Hu Hv. apply Ref.ref_unfold in Hxy.
  generalize dependent (observe y). generalize dependent (observe x).
  intros ox oy d. induction d; cbn.
  - constructor.
  - constructor. intros p. exists (srun (snd p) (k' (fst p))). split; [ | reflexivity ].
    left. exists (snd p), (k0 (fst p)), (k' (fst p)).
    split; [ apply observe_srun | ]. split; [ apply observe_srun | ]. apply H.
  - constructor. intros i. exists (go (srunF k oy)). split; [ | reflexivity ].
    left. exists k, (k0 i), (go oy).
    split; [ apply observe_srun | ]. split; [ reflexivity | ]. apply H.
  - econstructor. exists (go (srunF k oy)). split; [ | reflexivity ].
    left. exists k, (k0 i), (go oy).
    split; [ apply observe_srun | ]. split; [ reflexivity | ]. exact H.
  - econstructor. rewrite observe_srun. apply IHd.
  - constructor. intros j. rewrite observe_srun. apply H0.
Qed.

Global Instance srun_ref_proper E S A k :
  Proper (Ref.ref ==> Ref.ref) (@srun E S A k).
Proof. intros x y. apply srun_mono. Qed.

Global Instance srun_eqv_proper E S A k :
  Proper (eqv ==> eqv) (@srun E S A k).
Proof. intros x y [H1 H2]. split; apply srun_mono; auto. Qed.

Lemma srun_ret {E S A} (k : S) (a : A) :
  srun (E:=E) k (ret a) [=] ret (a, k).
Proof. split; apply Ref.ref_fold; rewrite observe_srun; cbn; apply refF_refl_ref. Qed.

Lemma srun_ret_bisim {E S A} (k : S) (a : A) :
  bisim (srun (E:=E) k (ret a)) (ret (a, k)).
Proof. apply Bisim.bisim_fold. rewrite observe_srun. cbn. constructor. Qed.

Lemma srun_bind_bisim {E S A B} (k : S) (f : A -> t E B) (x : t E A) :
  bisim (srun k (x >>= f)) (srun k x >>= fun p => srun (snd p) (f (fst p))).
Proof.
  pose (F := fun p : A * S => srun (snd p) (f (fst p))).
  pose (R := fun u v => exists (k : S) (x : t E A),
               observe u = srunF k (layer f (bind f) (observe x)) /\
               observe v = layer F (bind F) (srunF k (observe x))).
  apply (bisim_coind_up R).
  2: { exists k, x. split; [ rewrite observe_srun, observe_bind | rewrite observe_bind, observe_srun ]; reflexivity. }
  clear k x. intros u v H. hnf in H. destruct H as (k & y & Hu & Hv). rewrite Hu, Hv. clear Hu Hv.
  destruct y as [oy]. destruct oy; cbn.
  - unfold F. rewrite observe_srun. apply bisimF_refl_up.
  - constructor. intros p.
    exists (srun (snd p) (bind f (k0 (fst p)))), (bind F (srun (snd p) (k0 (fst p)))).
    split; [ reflexivity | ]. split; [ | reflexivity ].
    left. exists (snd p), (k0 (fst p)).
    split; [ rewrite observe_srun, observe_bind | rewrite observe_bind, observe_srun ]; reflexivity.
  - constructor. intros i.
    exists (srun k (bind f (k0 i))), (bind F (srun k (k0 i))).
    split; [ reflexivity | ]. split; [ | reflexivity ].
    left. exists k, (k0 i).
    split; [ rewrite observe_srun, observe_bind | rewrite observe_bind, observe_srun ]; reflexivity.
  - constructor. intros i.
    exists (srun k (bind f (k0 i))), (bind F (srun k (k0 i))).
    split; [ reflexivity | ]. split; [ | reflexivity ].
    left. exists k, (k0 i).
    split; [ rewrite observe_srun, observe_bind | rewrite observe_bind, observe_srun ]; reflexivity.
Qed.

Lemma srun_bind {E S A B} (k : S) (f : A -> t E B) (x : t E A) :
  srun k (x >>= f) [=] srun k x >>= fun p => srun (snd p) (f (fst p)).
Proof. apply bisim_eqv. apply srun_bind_bisim. Qed.

Lemma srun_int_bisim {E S ar} (k : S) (m : E ar) :
  bisim (srun k (int m)) (int (st m k)).
Proof.
  apply Bisim.bisim_fold. rewrite observe_srun. cbn. constructor. intros [n k'].
  cbn. apply srun_ret_bisim.
Qed.

Lemma srun_int {E S ar} (k : S) (m : E ar) :
  srun k (int m) [=] int (st m k).
Proof. apply bisim_eqv. apply srun_int_bisim. Qed.

Lemma srun_slift_bisim {E F S A} (k : S) (x : t F A) (σ : E ~> F) :
  bisim (srun k x / slift σ) (srun k (x / σ)).
Proof.
  pose (R := fun u v => exists (k : S) (x : t F A),
               observe u = Subst.applyF (slift σ) (Subst.apply (slift σ)) (srunF k (observe x)) /\
               observe v = srunF k (Subst.applyF σ (Subst.apply σ) (observe x))).
  apply (bisim_coind_up R).
  2: { exists k, x. split; [ rewrite Subst.observe_apply, observe_srun | rewrite observe_srun, Subst.observe_apply ]; reflexivity. }
  clear k x. intros u v H. hnf in H. destruct H as (k & y & Hu & Hv). rewrite Hu, Hv. clear Hu Hv.
  destruct y as [oy]. destruct oy; cbn.
  - constructor.
  - constructor. intros _.
    exists (bind (fun p => srun (snd p) (k0 (fst p)) / slift σ) (srun k (σ _ m))),
           (bind (fun p => srun (snd p) (k0 (fst p) / σ)) (srun k (σ _ m))).
    split; [ reflexivity | ]. split.
    + right. right.
      exists (ar * S)%type, (srun k (σ _ m)), (srun k (σ _ m)),
             (fun p => srun (snd p) (k0 (fst p)) / slift σ), (fun p => srun (snd p) (k0 (fst p) / σ)).
      split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. split; [ reflexivity | ].
      intros p. exists (snd p), (k0 (fst p)).
      split; [ rewrite Subst.observe_apply, observe_srun | rewrite observe_srun, Subst.observe_apply ]; reflexivity.
    + symmetry. apply (srun_bind_bisim k (fun n => k0 n / σ) (σ _ m)).
  - constructor. intros i.
    exists (srun k (k0 i) / slift σ), (srun k (k0 i / σ)).
    split; [ reflexivity | ]. split; [ | reflexivity ].
    left. exists k, (k0 i).
    split; [ rewrite Subst.observe_apply, observe_srun | rewrite observe_srun, Subst.observe_apply ]; reflexivity.
  - constructor. intros i.
    exists (srun k (k0 i) / slift σ), (srun k (k0 i / σ)).
    split; [ reflexivity | ]. split; [ | reflexivity ].
    left. exists k, (k0 i).
    split; [ rewrite Subst.observe_apply, observe_srun | rewrite observe_srun, Subst.observe_apply ]; reflexivity.
Qed.

Lemma srun_slift {E F S A} (k : S) (x : t F A) (σ : E ~> F) :
  srun k x / slift σ [=] srun k (x / σ).
Proof. apply bisim_eqv. apply srun_slift_bisim. Qed.

Lemma assert_true {E} {P : Prop} (H : P) :
  @assert E P [=] ret tt.
Proof.
  split.
  - apply sup_lub. reflexivity.
  - apply (sup_at H). reflexivity.
Qed.

(** ** Rewriting tactic *)

Create HintDb intm.

#[export] Hint Rewrite
  @bind_ret_l
  @bind_ret_r
  @bind_bind
  @apply_ret
  @apply_bind
  @apply_int_r
  @apply_sup
  @apply_inf
  @bind_sup
  @bind_inf
  @srun_ret
  @srun_bind
  @srun_int
  : intm.

Ltac intm :=
  repeat progress (autorewrite with intm;
                   cbn [Subst.compose slift CALspec_mor M_bq L_rb L_bq fst snd fsup finf]).

(** ** Example *)

Goal
  forall f, 5 < N ->
    srun (f, 2, 5) (int deq) / run_layer M_bq L_rb [=] ret (f 2, (f, 3, 5)).
Proof.
  intros f HN. unfold run_layer.
  rewrite <- apply_assoc. intm.
  rewrite assert_true by lia. intm.
  rewrite Nat.mod_small by lia.
  reflexivity.
Qed.


(** * Data refinement *)

Definition srel_push {E S1 S2} (R : rel S1 S2) : E#S2 ~> E#S1 :=
  fun _ '(st m k1) =>
    sup {k2 | R k1 k2}, int (st m k2) >>= fun '(n, k2') =>
    inf {k1' | R k1' k2'}, ret (n, k1').

Definition srel_pull {E S1 S2} (R : rel S1 S2) : E#S1 ~> E#S2 :=
  fun _ '(st m k2) =>
    inf {k1 | R k1 k2}, int (st m k1) >>= fun '(n, k1') =>
    sup {k2' | R k1' k2'}, ret (n, k2').

Lemma srel_push_pull {E S1 S2} (R : rel S1 S2) (σ : 0 ~> E#S2) (τ : 0 ~> E#S1) :
  srel_push R @ σ [~= τ <-> σ [~= srel_pull R @ τ.
Proof.
  unfold Subst.compose, srel_push, srel_pull, fsup, finf. split.
  - intros H _ [ar m k2].
    rewrite apply_inf. apply inf_glb. intros [k1 Hk]. cbn [proj1_sig].
    rewrite apply_bind, apply_int_r.
    specialize (H _ (st m k1)). rewrite apply_sup in H.
    rewrite sup_l_iff in H. specialize (H (exist _ k2 Hk)). cbn [proj1_sig] in H.
    rewrite apply_bind, apply_int_r in H.
    match type of H with bind ?g _ [= _ => set (g0 := g) in H end.
    match goal with |- _ [= bind ?g' _ => set (g1 := g') end.
    transitivity (bind (fun a => bind g1 (g0 a)) (σ _ (st m k2))).
    + rewrite <- (bind_ret_l (σ _ (st m k2))) at 1.
      apply bind_mono; [ | reflexivity ].
      intros [n k2']. subst g0 g1. cbn.
      rewrite apply_inf, bind_inf. apply inf_glb. intros [k1' Hk']. cbn.
      rewrite apply_ret, bind_ret_r, apply_sup. apply (sup_at (exist _ k2' Hk')). cbn.
      rewrite apply_ret. reflexivity.
    + rewrite <- bind_bind. apply bind_mono; [ intros a; reflexivity | exact H ].
  - intros H _ [ar m k1].
    rewrite apply_sup. apply sup_lub. intros [k2 Hk]. cbn [proj1_sig].
    rewrite apply_bind, apply_int_r.
    specialize (H _ (st m k2)). rewrite apply_inf in H.
    rewrite inf_r_iff in H. specialize (H (exist _ k1 Hk)). cbn [proj1_sig] in H.
    rewrite apply_bind, apply_int_r in H.
    match type of H with _ [= bind ?g _ => set (g0 := g) in H end.
    match goal with |- bind ?g' _ [= _ => set (g1 := g') end.
    transitivity (bind (fun a => bind g1 (g0 a)) (τ _ (st m k1))).
    + rewrite <- bind_bind. apply bind_mono; [ intros a; reflexivity | exact H ].
    + rewrite <- (bind_ret_l (τ _ (st m k1))) at 2.
      apply bind_mono; [ | reflexivity ].
      intros [n k1']. subst g0 g1. cbn.
      rewrite apply_sup, bind_sup. apply sup_lub. intros [k2' Hk']. cbn.
      rewrite apply_ret, bind_ret_r, apply_inf. apply (inf_at (exist _ k1' Hk')). cbn.
      rewrite apply_ret. reflexivity.
Qed.

(** ** Correctness of [M_bq] *)

Fixpoint slice (f : nat -> val) (i : nat) (n : nat) : list val :=
  match n with
    | O => nil
    | S n' => f i :: slice f (S i mod N) n'
  end.

Inductive rb_bq : rb_state -> bq_state -> Prop :=
  bq_rb_intro f c1 c2 n q :
    c1 < N ->
    n <= N ->
    q = slice f c1 n ->
    c2 = (c1 + n) mod N ->
    rb_bq (f, c1, c2) q.

(** *** Arithmetic about slices *)

Lemma slice_length f c1 n :
  length (slice f c1 n) = n.
Proof.
  revert c1. induction n; cbn; auto.
Qed.


Lemma slice_S f i n :
  slice f i (S n) = f i :: slice f (S i mod N) n.
Proof. reflexivity. Qed.

Lemma slice_snoc f c1 n :
  c1 < N ->
  slice f c1 (S n) = slice f c1 n ++ f ((c1 + n) mod N) :: nil.
Proof.
  revert c1. induction n; intros c1 Hc1.
  - cbn. rewrite Nat.add_0_r, Nat.mod_small by auto. reflexivity.
  - rewrite (slice_S f c1 (S n)), (slice_S f c1 n). cbn [app]. f_equal.
    rewrite IHn by (apply Nat.mod_upper_bound; lia).
    f_equal. f_equal. f_equal.
    rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia.
Qed.

(** Updating a position outside the slice does not change it. *)

Lemma slice_update f c1 n j v :
  c1 < N ->
  n <= N ->
  (forall i, i < n -> (c1 + i) mod N <> j) ->
  slice (update f j v) c1 n = slice f c1 n.
Proof.
  revert c1. induction n; intros c1 Hc1 Hn Hj; cbn [slice]; auto.
  f_equal.
  - unfold update. destruct Nat.eq_dec as [Heq | Hne]; auto.
    exfalso. apply (Hj O); [ lia | ].
    rewrite Nat.add_0_r, Nat.mod_small; auto.
  - apply IHn.
    + apply Nat.mod_upper_bound. lia.
    + lia.
    + intros i Hi. rewrite Nat.Div0.add_mod_idemp_l.
      replace (S c1 + i) with (c1 + S i) by lia.
      apply Hj. lia.
Qed.

Lemma mod_distinct c1 i n :
  c1 < N -> i < n -> n < N ->
  (c1 + i) mod N <> (c1 + n) mod N.
Proof.
  intros Hc1 Hi Hn Heq.
  destruct (Nat.le_gt_cases N (c1 + n)).
  - (* wrapped *)
    rewrite (Nat.mod_small (c1 + i)) in Heq.
    2: {
      destruct (Nat.le_gt_cases N (c1 + i)); [ | lia ].
      exfalso.
      assert ((c1 + n) mod N = c1 + n - N) as E.
      { replace (c1 + n) with ((c1 + n - N) + 1 * N) at 1 by lia.
        rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia. }
      assert ((c1 + i) mod N = c1 + i - N) as E'.
      { replace (c1 + i) with ((c1 + i - N) + 1 * N) at 1 by lia.
        rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia. }
      lia.
    }
    assert ((c1 + n) mod N = c1 + n - N) as E.
    { replace (c1 + n) with ((c1 + n - N) + 1 * N) at 1 by lia.
      rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia. }
    lia.
  - rewrite !Nat.mod_small in Heq by lia. lia.
Qed.

(** *** The refinement *)

Lemma assert_l {E A} (P : Prop) (x y : t E A) :
  (P -> x [= y) ->
  _ <- assert P; x [= y.
Proof.
  intros H. unfold assert. rewrite bind_sup. apply sup_lub. intros HP.
  rewrite bind_ret_r. apply H. assumption.
Qed.

Lemma assert_r {E A} (P : Prop) (x y : t E A) :
  x [= y -> P ->
  x [= _ <- assert P; y.
Proof.
  intros Hxy HP. unfold assert. rewrite bind_sup. apply (sup_at HP).
  rewrite bind_ret_r. assumption.
Qed.

Lemma bq_rb_correct :
  L_bq [~= srel_pull rb_bq @ slift M_bq @ L_rb.
Proof.
  intros _ [ar m q]. unfold Subst.compose, srel_pull, finf. cbn [CALspec_mor].
  rewrite !apply_inf. apply inf_glb. intros [[[f c1] c2] H]. cbn [proj1_sig].
  inversion H; clear H; subst.
  assert (HN : N <> O) by lia.
  destruct m; intm.
  - (* enq *)
    apply assert_l. intros Hlen. rewrite slice_length in Hlen.
    apply assert_r. 2: apply Nat.mod_upper_bound; auto.
    intm. unfold fsup. rewrite !apply_sup. eapply (sup_at (exist _ _ _)). cbn [proj1_sig].
    rewrite !apply_ret. reflexivity.
    Unshelve. cbn.
    apply bq_rb_intro with (n := S n); auto.
    + rewrite slice_snoc by auto.
      rewrite slice_update; auto.
      * unfold update. destruct Nat.eq_dec; congruence.
      * intros i Hi. apply mod_distinct; auto.
    + change (S ((c1 + n) mod N)) with (1 + (c1 + n) mod N).
      rewrite Nat.Div0.add_mod_idemp_r. f_equal. lia.
  - (* deq *)
    destruct n; cbn [slice]; auto using bot_lb.
    apply assert_r; auto.
    intm. unfold fsup. rewrite !apply_sup. eapply (sup_at (exist _ _ _)). cbn [proj1_sig].
    rewrite !apply_ret. reflexivity.
    Unshelve. cbn.
    apply bq_rb_intro with (n := n); auto.
    + apply Nat.mod_upper_bound; auto.
    + lia.
    + rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia.
Qed.

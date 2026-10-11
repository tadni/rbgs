(** * Certified abstraction layers on the tree model

  This is [examples/CAL.v] redone on top of [models/ISpecTree.v].
  The point of the exercise is that the lemmas which had to be
  admitted there ([srun_slift], [srun_bind], [srun_int],
  [srel_push_pull], and the use of [bind_bind]) are all proved here,
  with functional extensionality as the only axiom. *)

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat Lia.
From Stdlib Require Import Morphisms RelationClasses Setoid.
Require Import coqrel.LogicalRelations.
Require Import structures.Effects.
Require Import models.ISpecTree.

Import ISpec.


(** * Preliminaries *)

Notation "x >>= f" := (bind f x)
  (at level 40, left associativity).

Notation "v <- x ; M" := (x >>= fun v => M)
  (at level 65, right associativity).

Definition assert {E : esig} (P : Prop) : t E unit :=
  sup H : P, ret tt.


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
  interactions is a fold over the tree.  Compare [stateful_play] in
  [examples/CAL.v], which had to be extended from plays to the whole
  lattice by [ISpec.ext]. *)

Fixpoint srun {E S A} (k : S) (x : t E A) : t (E # S) (A * S) :=
  match x with
    | Ret a => Ret (a, k)
    | Vis m κ => Vis (st m k) (fun p => srun (snd p) (κ (fst p)))
    | Sup κ => Sup (fun i => srun k (κ i))
    | Inf κ => Inf (fun i => srun k (κ i))
  end.

Definition slift {E F S} (σ : E ~> F) : E#S ~> F#S :=
  fun ar m =>
    match m with st m k => srun k (σ _ m) end.

Definition layer {E F S} (M : E ~> F) (L : 0 ~> E#S) : 0 ~> F#S :=
  slift M @ L.

(** ** Properties *)

Lemma srun_ret {E S A} (k : S) (a : A) :
  srun (E:=E) k (ret a) = ret (a, k).
Proof. reflexivity. Qed.

Lemma srun_bind {E S A B} (k : S) (f : A -> t E B) (x : t E A) :
  srun k (x >>= f) = srun k x >>= fun p => srun (snd p) (f (fst p)).
Proof.
  revert k. induction x; intros s; cbn; try reflexivity;
    f_equal; apply functional_extensionality; auto.
Qed.

Lemma srun_int {E S ar} (k : S) (m : E ar) :
  srun k (int m) = int (st m k).
Proof.
  unfold int. cbn. f_equal. apply functional_extensionality. intros [n k']. reflexivity.
Qed.

Lemma srun_slift {E F S A} (k : S) (x : t F A) (σ : E ~> F) :
  srun k x / slift σ = srun k (x / σ).
Proof.
  revert k. induction x; intros s; cbn; try reflexivity.
  - rewrite srun_bind. f_equal. apply functional_extensionality. intros p. auto.
  - f_equal. apply functional_extensionality. auto.
  - f_equal. apply functional_extensionality. auto.
Qed.



Lemma srun_mono {E S A} (k : S) (x y : t E A) :
  x [= y -> srun k x [= srun k y.
Proof.
  revert k y. induction x as [a | ar m κ IH | I κ IH | I κ IH];
    intros k y; induction y as [b | ar' m' κ' IH' | J κ' IH' | J κ' IH'];
    intros H; unfold Ref.ref in H; cbn in H; cbn [srun]; try contradiction.
  - subst. reflexivity.
  - destruct H as [j Hj]. apply (sup_at j). apply (IH' j Hj).
  - apply inf_glb. intros j. apply (IH' j (H j)).
  - destruct H as [e Hk]. destruct e. apply vis_mono. intros [n k'].
    cbn. apply (IH n k' _ (Hk n)).
  - destruct H as [j Hj]. apply (sup_at j). apply (IH' j Hj).
  - apply inf_glb. intros j. apply (IH' j (H j)).
  - apply sup_lub. intros i. apply (IH i k _ (H i)).
  - apply sup_lub. intros i. apply (IH i k _ (H i)).
  - apply sup_lub. intros i. apply (IH i k (Sup κ') (H i)).
  - apply sup_lub. intros i. apply (IH i k (Inf κ') (H i)).
  - destruct H as [i Hi]. apply (inf_at i). apply (IH i k _ Hi).
  - destruct H as [i Hi]. apply (inf_at i). apply (IH i k _ Hi).
  - destruct H as [[i Hi] | [j Hj]].
    + apply (inf_at i). apply (IH i k (Sup κ') Hi).
    + apply (sup_at j). apply (IH' j Hj).
  - apply inf_glb. intros j. apply (IH' j (H j)).
Qed.

Global Instance srun_ref_proper E S A k :
  Proper (Ref.ref ==> Ref.ref) (@srun E S A k).
Proof. intros x y. apply srun_mono. Qed.

Global Instance srun_eqv_proper E S A k :
  Proper (eqv ==> eqv) (@srun E S A k).
Proof. intros x y [H1 H2]. split; apply srun_mono; auto. Qed.

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
  @srun_ret
  @srun_bind
  @srun_int
  : intm.

Ltac intm :=
  repeat progress (autorewrite with intm; cbn [Subst.apply bind srun Subst.compose slift CALspec_mor M_bq L_rb L_bq fst snd]).

(** ** Example *)

Goal
  forall f, 5 < N ->
    srun (f, 2, 5) (int deq) / layer M_bq L_rb [=] ret (f 2, (f, 3, 5)).
Proof.
  intros f HN. unfold layer.
  rewrite <- apply_assoc. intm.
  rewrite assert_true by lia. intm.
  rewrite Nat.mod_small by lia.
  reflexivity.
Qed.


(** * Data refinement *)

(** ** Simulation relations as morphisms *)

Definition srel_push {E S1 S2} (R : rel S1 S2) : E#S2 ~> E#S1 :=
  fun _ '(st m k1) =>
    sup {k2 | R k1 k2}, int (st m k2) >>= fun '(n, k2') =>
    inf {k1' | R k1' k2'}, ret (n, k1').

Definition srel_pull {E S1 S2} (R : rel S1 S2) : E#S1 ~> E#S2 :=
  fun _ '(st m k2) =>
    inf {k1 | R k1 k2}, int (st m k1) >>= fun '(n, k1') =>
    sup {k2' | R k1' k2'}, ret (n, k2').

(** The two are adjoint.  In the lattice-based model this needed a
  normal form argument; here it is a direct calculation with the
  monad laws and monotonicity. *)


Lemma srel_push_pull {E S1 S2} (R : rel S1 S2) (σ : 0 ~> E#S2) (τ : 0 ~> E#S1) :
  srel_push R @ σ [~= τ <-> σ [~= srel_pull R @ τ.
Proof.
  unfold Subst.compose, srel_push, srel_pull, fsup, finf. split.
  - intros H _ [ar m k2]. cbn [Subst.apply].
    apply inf_glb. intros [k1 Hk]. cbn [proj1_sig].
    rewrite apply_bind, apply_int_r.
    specialize (H _ (st m k1)). cbn [Subst.apply] in H.
    rewrite Ref.sup_l in H. specialize (H (exist _ k2 Hk)). cbn [proj1_sig] in H.
    rewrite apply_bind, apply_int_r in H.
    match type of H with bind ?g _ [= _ => set (g0 := g) in H end.
    match goal with |- _ [= bind ?g' _ => set (g1 := g') end.
    transitivity (bind (fun a => bind g1 (g0 a)) (σ _ (st m k2))).
    + rewrite <- (bind_ret_l (σ _ (st m k2))) at 1.
      apply bind_mono; [ | reflexivity ].
      intros [n k2']. subst g0 g1. cbn.
      apply inf_glb. intros [k1' Hk']. cbn.
      apply (sup_at (exist _ k2' Hk')). reflexivity.
    + rewrite <- bind_bind. apply bind_mono; [ intros a; reflexivity | exact H ].
  - intros H _ [ar m k1]. cbn [Subst.apply].
    apply sup_lub. intros [k2 Hk]. cbn [proj1_sig].
    rewrite apply_bind, apply_int_r.
    specialize (H _ (st m k2)). cbn [Subst.apply] in H.
    rewrite Ref.inf_r in H. specialize (H (exist _ k1 Hk)). cbn [proj1_sig] in H.
    rewrite apply_bind, apply_int_r in H.
    match type of H with _ [= bind ?g _ => set (g0 := g) in H end.
    match goal with |- bind ?g' _ [= _ => set (g1 := g') end.
    transitivity (bind (fun a => bind g1 (g0 a)) (τ _ (st m k1))).
    + rewrite <- bind_bind. apply bind_mono; [ intros a; reflexivity | exact H ].
    + rewrite <- (bind_ret_l (τ _ (st m k1))) at 2.
      apply bind_mono; [ | reflexivity ].
      intros [n k1']. subst g0 g1. cbn.
      apply sup_lub. intros [k2' Hk']. cbn.
      apply (inf_at (exist _ k1' Hk')). reflexivity.
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
  intros H. unfold assert. cbn [bind]. apply sup_lub. intros HP. apply H. assumption.
Qed.

Lemma assert_r {E A} (P : Prop) (x y : t E A) :
  x [= y -> P ->
  x [= _ <- assert P; y.
Proof.
  intros Hxy HP. unfold assert. cbn [bind]. apply (sup_at HP). assumption.
Qed.

Lemma bq_rb_correct :
  L_bq [~= srel_pull rb_bq @ slift M_bq @ L_rb.
Proof.
  intros _ [ar m q]. unfold Subst.compose, srel_pull, finf. cbn [Subst.apply CALspec_mor].
  apply inf_glb. intros [[[f c1] c2] H]. cbn [proj1_sig].
  inversion H; clear H; subst.
  assert (HN : N <> O) by lia.
  destruct m; intm.
  - (* enq *)
    apply assert_l. intros Hlen. rewrite slice_length in Hlen.
    apply assert_r. 2: apply Nat.mod_upper_bound; auto.
    unfold fsup. eapply (sup_at (exist _ _ _)); cbn [proj1_sig].
    reflexivity.
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
    unfold fsup. eapply (sup_at (exist _ _ _)); cbn [proj1_sig].
    reflexivity.
    Unshelve. cbn.
    apply bq_rb_intro with (n := n); auto.
    + apply Nat.mod_upper_bound; auto.
    + lia.
    + rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia.
Qed.

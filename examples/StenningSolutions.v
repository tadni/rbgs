(** * StenningSolutions: Refining a reliable channel to a retransmission protocol *)

(** In this chapter we use the coinductive interaction specifications
    of [models/ISpecCoTree.v] to specify and verify a classic protocol
    from the distributed systems literature: Stenning's data transfer
    protocol (N. V. Stenning, "A data transfer protocol", 1976).

    The problem is the following.  A _sender_ wants to pass a stream
    of messages to a _receiver_ over a network that is unreliable: a
    packet may be

      - lost,
      - duplicated, or
      - delivered out of order, possibly long after it was sent.

    We would like the receiving application to see the messages
    exactly once each, and in the order in which they were sent.  In
    other words, on top of a bad network we would like to implement a
    _reliable FIFO channel_.

    Stenning's solution is to tag every message with a _sequence
    number_.  The sender retransmits the current message, tagged with
    its sequence number, until it is acknowledged.  The receiver keeps
    track of the next sequence number it expects; it delivers a packet
    only if it carries that number, ignores all others, and keeps
    acknowledging what it has received so far.  Since the network may
    replay arbitrarily old packets, sequence numbers are _unbounded_:
    this is what distinguishes Stenning's protocol from the
    alternating bit protocol, which only works on FIFO channels.

    We follow the methodology of certified abstraction layers, as in
    [examples/CALCoTree.v], which this chapter builds upon:

      - the _specification_ [L_rc] is a layer interface describing a
        reliable channel, in which [transmit v] simply appends [v] to
        the list of delivered messages;
      - the _code_ [M_st] is a layer implementation, written as an
        interaction tree that calls the primitives of a lower layer;
      - the _underlying layer_ [L_net] models the network and the
        local memory of the two endpoints;
      - correctness is the refinement

          [L_rc [~= srel_pull R @ slift M_st @ L_net]

        for a suitable simulation relation [R].

    The retransmission loop of the sender may in principle run
    forever, so [M_st] is an infinite tree built with [iter].  This is
    where the coinductive model is essential.  We will see that, in
    this model, silent divergence is the bottom element: a loop that
    never terminates satisfies no specification.  To prove that the
    loop terminates we will therefore need a _fairness_ assumption on
    the network, and the proof will proceed by induction on a measure
    while the trees involved are infinite.

    As in Software Foundations, the chapter contains exercises marked
    with a difficulty rating.  Replace each [(* FILL IN HERE *)
    Admitted.] with a proof ending in [Qed.].  Every exercise can be
    solved using only the lemmas stated before it. *)

From Stdlib Require Import List PeanoNat Lia.
From Stdlib Require Import Morphisms RelationClasses Setoid.
Require Import coqrel.LogicalRelations.
Require Import structures.Effects.
Require Import models.ISpecCoTree.
Require Import examples.CALCoTree.

Import ISpec.

(** Beware: [structures/Effects.v] declares [0] as a notation for the
    empty effect signature, so in this chapter the natural number zero
    is written [O]. *)


(* ################################################################# *)
(** * Reminders on the refinement order *)

(** Specifications are trees of type [t E A].  Besides interactions
    [Vis m k] and return values [ret a], a tree can contain _angelic_
    choices [Sup k] (made in our favor) and _demonic_ choices [Inf k]
    (made by an adversary).  The refinement [x [= y] reads "[y] is at
    least as good as [x]": [y] may resolve the demonic choices of [x],
    and must handle every demonic choice of its own.  Dually, [y] must
    match every branch of an angelic choice of [x], and may pick a
    branch of its own angelic choices.

    In the coinductive model, a tree can be infinite.  The refinement
    game treats the two sides asymmetrically: the moves that consume
    the left tree may continue forever, but the moves that consume the
    right tree must reach an interaction or a return value in finitely
    many steps.  As a consequence, a tree that loops forever without
    interacting, such as [spin], is below every other tree.

    Our first exercise shows that [spin] is _strictly_ below a
    terminating computation.  This is the reason why fairness will be
    unavoidable later on: a retransmission loop that can be starved
    forever is equivalent to [spin], and hence cannot implement any
    terminating specification. *)

(** **** Exercise: 3 stars, standard (ret_not_ref_spin)

    Hint: unfold the refinement with [Ref.ref_unfold] and proceed by
    induction on the resulting derivation of [Ref.refF].  You will need
    to [remember] both sides first, and the tactic [inj_pair] from
    [models/ISpecCoTree.v] is useful to invert an equation between
    [SupF] nodes. *)

Lemma ret_not_ref_spin {E A} (a : A) :
  ~ (ret (E := E) a [= spin).
Proof.
  intros H. apply Ref.ref_unfold in H.
  remember (observe (ret (E := E) a)) as ox eqn:Hox.
  remember (observe (spin (E := E) (A := A))) as oy eqn:Hoy.
  cbn in Hox. induction H; try discriminate.
  cbn in Hoy. injection Hoy. intros Hk HI. subst J. inj_pair.
  apply IHrefF; auto.
Qed.
(** [] *)


(* ################################################################# *)
(** * Total correctness assertions *)

(** Refinement proofs about the protocol will mostly have the following
    shape: some tree [x], obtained by running code against a layer, is
    shown to compute a result satisfying a postcondition [P], whatever
    the demonic choices of the environment.  We capture this with the
    following predicate.  [sat x P] holds when, for any continuation
    [K] which is above [y] on all results satisfying [P], the
    sequential composition [x >>= K] is also above [y]. *)

Definition sat {E A} (x : t E A) (P : A -> Prop) : Prop :=
  forall B (y : t E B) (K : A -> t E B),
    (forall a, P a -> y [= K a) ->
    y [= x >>= K.

(** Because [sat] is stated in continuation-passing style, the proof
    rules for it are straightforward.  Here is the first one. *)

Lemma sat_weaken {E A} (x : t E A) (P Q : A -> Prop) :
  sat x P -> (forall a, P a -> Q a) -> sat x Q.
Proof.
  intros Hx HPQ B y K HK. apply Hx. auto.
Qed.

(** **** Exercise: 1 star, standard (sat_ret) *)

Lemma sat_ret {E A} (a : A) (P : A -> Prop) :
  P a -> sat (E := E) (ret a) P.
Proof.
  intros Ha B y K HK. rewrite bind_ret_r. auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sat_bind) *)

Lemma sat_bind {E A B} (x : t E A) (f : A -> t E B) (P : B -> Prop) :
  sat x (fun a => sat (f a) P) ->
  sat (x >>= f) P.
Proof.
  intros Hx C y K HK. rewrite bind_bind. apply Hx. intros a Ha. apply Ha. exact HK.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sat_inf_sup)

    Demonic choices must be handled for all branches, angelic choices
    may be resolved by picking one branch. *)

Lemma sat_inf {E A I} (k : I -> t E A) (P : A -> Prop) :
  (forall i, sat (k i) P) -> sat (Inf k) P.
Proof.
  intros H B y K HK. rewrite bind_inf. apply inf_glb. intros i. apply H. exact HK.
Qed.

Lemma sat_sup {E A I} (k : I -> t E A) (P : A -> Prop) (i : I) :
  sat (k i) P -> sat (Sup k) P.
Proof.
  intros H B y K HK. rewrite bind_sup. apply (sup_at i). apply H. exact HK.
Qed.
(** [] *)

(** The following consequences are proved for you. *)

Lemma sat_meet {E A} (x y : t E A) (P : A -> Prop) :
  sat x P -> sat y P -> sat (x && y) P.
Proof.
  intros Hx Hy. apply sat_inf. intros []; auto.
Qed.

Lemma sat_finf {E A I} (Q : I -> Prop) (f : I -> t E A) (P : A -> Prop) :
  (forall i, Q i -> sat (f i) P) -> sat (finf Q f) P.
Proof.
  intros H. apply sat_inf. intros [i Hi]. apply H. exact Hi.
Qed.

Lemma sat_tau {E A} (x : t E A) (P : A -> Prop) :
  sat x P -> sat (Tau x) P.
Proof.
  intros H. unfold Tau. apply (sat_sup _ _ tt). exact H.
Qed.

(** **** Exercise: 2 stars, standard (sat_ref)

    [sat] is upward closed with respect to refinement.  Deduce that it
    is compatible with [[=]], which allows us to [rewrite] with the
    equational laws of [models/ISpecCoTree.v] in [sat] goals. *)

Lemma sat_ref {E A} (x x' : t E A) (P : A -> Prop) :
  x [= x' -> sat x P -> sat x' P.
Proof.
  intros Hxx' Hx B y K HK. etransitivity; [ apply Hx; exact HK | ].
  apply bind_mono; [ intros a; reflexivity | exact Hxx' ].
Qed.

Global Instance sat_eqv_proper E A :
  Proper (eqv ==> eq ==> iff) (@sat E A).
Proof.
  intros x x' [H1 H2] P _ []. split; apply sat_ref; auto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (sat_iff)

    What does [sat] mean in terms of the refinement order alone?  The
    following characterization says that [sat x P] holds exactly when
    [x] is better than the most demonic computation whose results
    satisfy [P]. *)

Lemma sat_iff {E A} (x : t E A) (P : A -> Prop) :
  sat x P <-> (inf {a | P a}, ret a) [= x.
Proof.
  split.
  - intros Hx. rewrite <- (bind_ret_l x). apply Hx.
    intros a Ha. apply (inf_at (exist _ a Ha)). reflexivity.
  - intros Hx B y K HK. etransitivity.
    + instantiate (1 := (inf {a | P a}, ret a) >>= K).
      unfold finf. rewrite bind_inf. apply inf_glb. intros [a Ha]. cbn.
      rewrite bind_ret_r. auto.
    + apply bind_mono; [ intros a; reflexivity | exact Hx ].
Qed.
(** [] *)


(* ################################################################# *)
(** * Running loops against a layer *)

(** Code is executed against a layer by threading the layer state with
    [srun] (from [examples/CALCoTree.v]) and then substituting the
    layer for the resulting stateful operations.  We first add two
    laws about [srun] which we will need for loops. *)

Lemma srun_sup {E S A I} (k : S) (κ : I -> t E A) :
  srun k (Sup κ) [=] Sup (fun i => srun k (κ i)).
Proof.
  split; apply Ref.ref_fold; rewrite observe_srun; cbn; apply refF_refl_ref.
Qed.

Lemma srun_tau {E S A} (k : S) (x : t E A) :
  srun k (Tau x) [=] Tau (srun k x).
Proof.
  apply srun_sup.
Qed.

(** The central proof rule for loops is the following.  To show that
    a loop [iter body i] terminates with a result satisfying [P], it
    suffices to find an invariant [I] on the loop variable and the
    layer state, and a measure [μ] on the layer state, such that every
    execution of the body either exits with a result satisfying [P],
    or continues in a state satisfying the invariant with a strictly
    smaller measure.

    Notice that the left-hand side of the refinement game is entirely
    hidden inside [sat], and that the tree [iter body i] may well be
    infinite: the measure is what makes sure that the _right_ moves
    of the game only ever explore a finite part of it. *)

(** **** Exercise: 3 stars, standard (sat_loop)

    Hint: proceed by strong induction, for instance by first proving
    [forall n i k, μ k < n -> I i k -> ...] by induction on [n].
    Unfold the loop once with [iter_unfold], and use [srun_bind],
    [apply_bind], [srun_tau], [apply_tau], [srun_ret] and
    [apply_ret]. *)

Lemma sat_loop {E S X A} (L : 0 ~> E # S) (body : X -> t E (X + A))
  (I : X -> S -> Prop) (μ : S -> nat) (P : A * S -> Prop) :
  (forall i k,
     I i k ->
     sat (srun k (body i) / L)
         (fun p => match fst p with
                   | inl i' => I i' (snd p) /\ μ (snd p) < μ k
                   | inr a => P (a, snd p)
                   end)) ->
  forall i k, I i k -> sat (srun k (iter body i) / L) P.
Proof.
  intros Hbody.
  assert (H : forall n i k, μ k < n -> I i k -> sat (srun k (iter body i) / L) P).
  { induction n as [ | n IHn]; intros i k Hn Hi; [ lia | ].
    rewrite iter_unfold, srun_bind, apply_bind. apply sat_bind.
    eapply sat_weaken; [ apply Hbody; exact Hi | ].
    intros [[i' | a] k'] Hr; cbn in Hr |- *.
    - destruct Hr as [Hi' Hlt].
      rewrite srun_tau, apply_tau. apply sat_tau.
      apply IHn; [ lia | exact Hi' ].
    - rewrite srun_ret, apply_ret. apply sat_ret. exact Hr. }
  intros i k Hi. eapply H; eauto.
Qed.
(** [] *)


(* ################################################################# *)
(** * The specification: a reliable channel *)

(** We take messages from the type [val] of [examples/CALCoTree.v].

    The high-level interface has a single operation: [transmit v]
    sends the message [v] to the receiving application.  The state of
    the specification is the list of messages delivered so far, and
    transmitting [v] appends [v] to it.  This says, in one line, that
    every message is delivered exactly once and in order. *)

Inductive rc_sig : esig :=
  | transmit (v : val) : rc_sig unit.

Definition L_rc : CALspec rc_sig (list val) :=
  fun _ m log =>
    match m with
      | transmit v => ret (tt, log ++ v :: nil)
    end.


(* ################################################################# *)
(** * The underlying layer: an unreliable network *)

(** ** The primitive operations *)

(** The protocol is implemented on top of the following primitives:

      - the sender has a register holding the next sequence number
        [get_seq], which can be incremented with [next_seq];
      - the receiver has a register holding the sequence number it
        expects next, [get_exp], and it can [deliver] a message to the
        receiving application, which also increments its register;
      - the data channel, from the sender to the receiver, carries
        packets [(n, v)] made of a sequence number and a message;
      - the acknowledgment channel, from the receiver to the sender,
        carries sequence numbers. *)

Inductive net_sig : esig :=
  | get_seq : net_sig nat
  | next_seq : net_sig unit
  | get_exp : net_sig nat
  | deliver (v : val) : net_sig unit
  | send_data (n : nat) (v : val) : net_sig unit
  | recv_data : net_sig (option (nat * val))
  | send_ack (n : nat) : net_sig unit
  | recv_ack : net_sig (option nat).

(** ** The network model *)

(** A channel is modelled by the history of all the packets ever sent
    on it, the most recent first.  When asked for a packet, the
    channel either returns the most recent one, or misbehaves: it
    loses the packet, returning [None], or it replays any packet
    from its history.  Replaying captures both duplication and
    reordering.

    The choice is _demonic_: the protocol must cope with all of these
    behaviors.  Without further constraint, however, the channel could
    misbehave forever and no protocol could succeed (recall
    [ret_not_ref_spin]).  We use a simple finitary form of fairness: a
    _budget_ [b] bounds the number of misbehaviors that may still
    occur.  The initial budget is arbitrary, and the protocol cannot
    observe it, so the implementation is correct for networks that
    misbehave any finite number of times. *)

Definition rx {P : Type} (h : list P) (b : nat) : t 0 (option P * nat) :=
  match h with
    | nil => ret (None, b)
    | p :: _ =>
      ret (Some p, b) &&
      (inf {o : option P | b <> O /\ (o = None \/ exists q, o = Some q /\ In q h)},
       ret (o, b - 1))
  end.

(** The state of the network layer gathers the registers of the two
    endpoints, the histories of the two channels, the fairness budget
    shared by the two channels, and the messages delivered so far to
    the receiving application. *)

Record net_state :=
  mk_net {
    sseq : nat;
    rexp : nat;
    dchan : list (nat * val);
    achan : list nat;
    budget : nat;
    delivered : list val;
  }.

Definition L_net : CALspec net_sig net_state :=
  fun _ m '(mk_net s e dc ac b out) =>
    match m with
      | get_seq => ret (s, mk_net s e dc ac b out)
      | next_seq => ret (tt, mk_net (S s) e dc ac b out)
      | get_exp => ret (e, mk_net s e dc ac b out)
      | deliver v => ret (tt, mk_net s (S e) dc ac b (out ++ v :: nil))
      | send_data n v => ret (tt, mk_net s e ((n, v) :: dc) ac b out)
      | recv_data =>
        p <- rx dc b;
        ret (fst p, mk_net s e dc ac (snd p) out)
      | send_ack n => ret (tt, mk_net s e dc (n :: ac) b out)
      | recv_ack =>
        p <- rx ac b;
        ret (fst p, mk_net s e dc ac (snd p) out)
    end.

(** **** Exercise: 2 stars, standard (rx_sat)

    The following lemma summarizes the possible outcomes of a channel.
    It is the only fact about [rx] you will need afterwards. *)

Definition rx_ok {P} (h : list P) (b : nat) (o : option P) (b' : nat) : Prop :=
  (o = hd_error h /\ b' = b) \/
  (b <> O /\ b' = b - 1 /\ (o = None \/ exists q, o = Some q /\ In q h)).

Lemma rx_sat {P} (h : list P) (b : nat) (Q : option P * nat -> Prop) :
  (forall o b', rx_ok h b o b' -> Q (o, b')) ->
  sat (rx h b) Q.
Proof.
  intros H. destruct h as [ | p h]; cbn.
  - apply sat_ret. apply H. left. auto.
  - apply sat_meet.
    + apply sat_ret. apply H. left. auto.
    + apply sat_finf. intros o [Hb Ho]. apply sat_ret. apply H. right. auto.
Qed.
(** [] *)


(* ################################################################# *)
(** * The code: Stenning's protocol *)

(** We are working with a single sequential client, so the two
    endpoints have to share the processor.  We use the simplest
    schedule: each round of the sender's retransmission loop gives the
    receiver one step.

    The receiver takes one packet from the data channel.  If it carries
    the expected sequence number, the message is delivered.  In any
    case the receiver acknowledges by sending back the sequence number
    it now expects; such _cumulative_ acknowledgments say "I have
    received everything before this number". *)

Definition recv_step : t net_sig unit :=
  p <- int recv_data;
  match p with
    | None => ret tt
    | Some (n, w) =>
      e <- int get_exp;
      _ <- (if Nat.eqb n e then int (deliver w) else ret tt);
      e' <- int get_exp;
      int (send_ack e')
  end.

(** One round of the sender transmits the packet [(s, v)], lets the
    receiver run, and checks the acknowledgment channel.  The loop
    exits once the receiver has acknowledged [s], that is, once it
    expects [S s]. *)

Definition send_round (s : nat) (v : val) (_ : unit) : t net_sig (unit + unit) :=
  _ <- int (send_data s v);
  _ <- recv_step;
  a <- int recv_ack;
  match a with
    | Some n =>
      if Nat.eqb n (S s) then
        _ <- int next_seq; ret (inr tt)
      else
        ret (inl tt)
    | None =>
      ret (inl tt)
  end.

Definition M_st : net_sig ~> rc_sig :=
  fun _ m =>
    match m with
      | transmit v =>
        s <- int get_seq;
        iter (send_round s v) tt
    end.

(** **** Exercise: 1 star, standard, optional (M_st_infinite)

    Convince yourself that [M_st _ (transmit v)] is an infinite tree.
    Why could we not have written it in the inductive model of
    [models/ISpecTree.v]?  (No proof required.) *)
(** [] *)


(* ################################################################# *)
(** * The invariants *)

(** Between two calls to [transmit], the network state is
    _quiescent_: both registers are equal to the number of messages
    delivered so far, the receiving application has received exactly
    the messages transmitted so far, and the channels only contain
    packets and acknowledgments that refer to the past.  This is the
    simulation relation of the refinement. *)

Definition quiescent (log : list val) (k : net_state) : Prop :=
  sseq k = length log /\
  rexp k = length log /\
  delivered k = log /\
  (forall n w, In (n, w) (dchan k) -> n < length log) /\
  (forall a, In a (achan k) -> a <= length log).

Definition R_st : rel net_state (list val) :=
  fun k log => quiescent log k.

(** While the message [v] is being transmitted with sequence number
    [s = length log], the system is in one of two phases.  In the
    first one, the receiver has not yet delivered [v].  In the second
    one, it has, and since then the most recent acknowledgment is
    [S s].  In both phases the packets with sequence number [s] carry
    the message [v]. *)

Definition data_ok (s : nat) (v : val) (dc : list (nat * val)) : Prop :=
  forall n w, In (n, w) dc -> n < s \/ (n = s /\ w = v).

Inductive inv (log : list val) (v : val) : net_state -> Prop :=
  | inv_waiting dc ac b :
      data_ok (length log) v dc ->
      (forall a, In a ac -> a <= length log) ->
      inv log v (mk_net (length log) (length log) dc ac b log)
  | inv_delivered dc ac b :
      data_ok (length log) v dc ->
      (forall a, In a ac -> a <= S (length log)) ->
      inv log v (mk_net (length log) (S (length log)) dc
                        (S (length log) :: ac) b (log ++ v :: nil)).

(** Every round either finishes the transmission, or consumes some
    budget, or moves from the first phase to the second.  The
    following measure therefore decreases at every round that does not
    exit the loop. *)

Definition measure (k : net_state) : nat :=
  budget k + (S (sseq k) - rexp k).

(** **** Exercise: 1 star, standard (inv_init) *)

Lemma inv_init log v k :
  quiescent log k -> inv log v k.
Proof.
  destruct k as [s e dc ac b out]. intros (Hs & He & Hout & Hdc & Hac). cbn in *. subst.
  constructor; auto.
  intros n w Hnw. left. eauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (quiescent_init)

    Initially, nothing has been sent or delivered. *)

Lemma quiescent_init b :
  quiescent nil (mk_net O O nil nil b nil).
Proof.
  repeat split; cbn; intros; contradiction.
Qed.
(** [] *)


(* ################################################################# *)
(** * Correctness of one round *)

(** The following tactic performs one step of symbolic execution of
    code against the layer [L_net]. *)

Ltac sat_step :=
  match goal with
    | |- sat (Subst.apply _ (srun _ (bind _ _))) _ =>
      rewrite srun_bind, apply_bind; apply sat_bind
    | |- sat (Subst.apply _ (srun _ (int _))) _ =>
      rewrite srun_int, apply_int_r; cbn [CALspec_mor L_net]
    | |- sat (Subst.apply _ (srun _ (ret _))) _ =>
      rewrite srun_ret, apply_ret
    | |- sat (ret _) _ =>
      apply sat_ret; cbn [fst snd]
    | |- sat (bind _ _) _ =>
      apply sat_bind
  end.

(** Here is how it is used on a simple example. *)

Example get_seq_example log :
  sat (srun (mk_net (length log) (length log) nil nil O log) (int get_seq) / L_net)
      (fun p => fst p = length log).
Proof.
  sat_step. sat_step. reflexivity.
Qed.

(** **** Exercise: 4 stars, standard (recv_step_correct)

    After the sender has put [(s, v)] on the data channel, the
    receiver's step preserves the invariant and does not increase the
    measure.  Moreover, if the measure stays the same, then the
    receiver is in the second phase.

    Hint: begin with [destruct Hinv], then use [sat_step] and
    [rx_sat], and look at all the cases of [rx_ok].  You will need
    [Nat.eqb_spec] or [Nat.eqb_refl] to evaluate the comparisons, and
    [lia] to discharge the conditions on the measure. *)

Lemma recv_step_correct log v k dc :
  inv log v k ->
  dchan k = (length log, v) :: dc ->
  sat (srun k recv_step / L_net)
      (fun p => inv log v (snd p) /\
                measure (snd p) <= measure k /\
                (measure (snd p) < measure k \/ rexp (snd p) = S (length log))).
Proof.
  intros Hinv Hdc.
  destruct Hinv as [dc0 ac b Hd Ha | dc0 ac b Hd Ha]; cbn in Hdc; subst dc0;
    unfold recv_step; sat_step; sat_step; sat_step;
    apply rx_sat; intros o b' Hok; sat_step;
    destruct Hok as [[-> ->] | (Hb & -> & [-> | ([n w] & -> & Hq)])]; cbn [hd_error];
    repeat sat_step.
  - (* waiting, good delivery *)
    rewrite Nat.eqb_refl. repeat sat_step.
    split; [ constructor; auto | unfold measure; cbn; lia ].
  - (* waiting, loss *)
    split; [ constructor; auto | unfold measure; cbn; lia ].
  - (* waiting, replay *)
    apply Hd in Hq.
    destruct (Nat.eqb_spec n (length log)) as [-> | Hn].
    + destruct Hq as [Hq | [_ ->]]; [ lia | ].
      repeat sat_step.
      split; [ constructor; auto | unfold measure; cbn; lia ].
    + repeat sat_step.
      split; [ | unfold measure; cbn; lia ].
      constructor; auto.
      intros a [<- | Ha']; auto.
  - (* delivered, good delivery *)
    destruct (Nat.eqb_spec (length log) (S (length log))) as [Hn | _]; [ lia | ].
    repeat sat_step.
    split; [ | unfold measure; cbn; lia ].
    constructor; auto.
    intros a [<- | Ha']; auto.
  - (* delivered, loss *)
    split; [ constructor; auto | unfold measure; cbn; lia ].
  - (* delivered, replay *)
    apply Hd in Hq.
    destruct (Nat.eqb_spec n (S (length log))) as [Hn | _]; [ lia | ].
    repeat sat_step.
    split; [ | unfold measure; cbn; lia ].
    constructor; auto.
    intros a [<- | Ha']; auto.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard (send_round_correct)

    Each round of the sender either exits in a quiescent state where
    [v] has been delivered, or continues with the invariant and a
    smaller measure.

    Hint: after the first [sat_step]s, use [sat_weaken] and
    [recv_step_correct] for the receiver's step, then [destruct] the
    invariant it gives you so that the state becomes concrete again.
    When the round exits, conclude with [quiescent_next] below.  To
    rule out an early exit in the first phase, remember that all the
    acknowledgments are then at most [length log]. *)

Lemma data_ok_cons (log : list val) v dc :
  data_ok (length log) v dc ->
  data_ok (length log) v ((length log, v) :: dc).
Proof.
  intros H n w [Hnw | Hnw]; auto.
  injection Hnw as -> ->. auto.
Qed.

Lemma quiescent_next (log : list val) v dc ac b :
  data_ok (length log) v dc ->
  (forall a, In a ac -> a <= S (length log)) ->
  quiescent (log ++ v :: nil)
            (mk_net (S (length log)) (S (length log)) dc
                    (S (length log) :: ac) b (log ++ v :: nil)).
Proof.
  intros Hd Ha. unfold quiescent. cbn. rewrite length_app. cbn.
  repeat split; try lia.
  - intros n w Hnw. apply Hd in Hnw. lia.
  - intros a [<- | Hin]; [ lia | apply Ha in Hin; lia ].
Qed.

Lemma send_round_correct log v k :
  inv log v k ->
  sat (srun k (send_round (length log) v tt) / L_net)
      (fun p => match fst p with
                | inl _ => inv log v (snd p) /\ measure (snd p) < measure k
                | inr _ => quiescent (log ++ v :: nil) (snd p)
                end).
Proof.
  intros Hinv. unfold send_round.
  destruct Hinv as [dc ac b Hd Ha | dc ac b Hd Ha];
    sat_step; sat_step; sat_step; sat_step;
    (eapply sat_weaken;
     [ apply (recv_step_correct log v _ dc);
       [ constructor; auto using data_ok_cons | reflexivity ] | ]);
    intros [[] k'] (Hinv' & Hle & Hlt); cbn [fst snd] in Hinv', Hle, Hlt |- *;
    revert Hle Hlt; destruct Hinv' as [dc' ac' b' Hd' Ha' | dc' ac' b' Hd' Ha'];
    intros Hle Hlt; unfold measure in Hle, Hlt; cbn [budget sseq rexp] in Hle, Hlt;
    repeat sat_step;
    apply rx_sat; intros o b'' Hok; sat_step;
    destruct Hok as [[-> ->] | (Hb & -> & [-> | (q & -> & Hq)])]; cbn [hd_error].
  (* We get twelve goals: two phases for the state before the round,
     two phases after the receiver's step, and three possible outcomes
     of the acknowledgment channel.  In goals 1-3 and 7-9 the receiver
     has not yet delivered [v], so its acknowledgments are at most [s]
     and the round cannot exit.  In goals 4-6 and 10-12 it has.  We
     treat the goals from last to first so that the numbering of the
     remaining ones does not change. *)
  12: destruct (Nat.eqb_spec q (S (length log))) as [-> | Hn].
  10: rewrite Nat.eqb_refl.
  9: destruct (Nat.eqb_spec q (S (length log))) as [Hn | Hn];
       [ exfalso; apply Ha' in Hq; lia | ].
  7: destruct ac' as [ | a ac']; cbn [hd_error];
       [ | destruct (Nat.eqb_spec a (S (length log))) as [Hn | Hn];
           [ exfalso; assert (a <= length log) by (apply Ha'; left; auto); lia | ] ].
  6: destruct (Nat.eqb_spec q (S (length log))) as [-> | Hn].
  4: rewrite Nat.eqb_refl.
  3: destruct (Nat.eqb_spec q (S (length log))) as [Hn | Hn];
       [ exfalso; apply Ha' in Hq; lia | ].
  1: destruct ac' as [ | a ac']; cbn [hd_error];
       [ | destruct (Nat.eqb_spec a (S (length log))) as [Hn | Hn];
           [ exfalso; assert (a <= length log) by (apply Ha'; left; auto); lia | ] ].
  all: repeat sat_step.
  all: first [ apply quiescent_next; auto
             | split; [ constructor; auto | unfold measure; cbn [budget sseq rexp]; lia ] ].
Qed.
(** [] *)


(* ################################################################# *)
(** * Correctness of the protocol *)

(** **** Exercise: 2 stars, standard (transmit_correct)

    Use [sat_loop], with the invariant [inv] and the [measure]. *)

Lemma transmit_correct log v k :
  quiescent log k ->
  sat (srun k (M_st _ (transmit v)) / L_net)
      (fun p => quiescent (log ++ v :: nil) (snd p)).
Proof.
  intros Hq. pose proof (inv_init log v k Hq) as Hinv.
  destruct Hinv as [dc ac b Hd Ha | dc ac b Hd Ha].
  2: { destruct Hq as (_ & He & _). cbn in He. lia. }
  cbn [M_st]. sat_step. sat_step. sat_step.
  apply sat_loop with (I := fun _ k => inv log v k) (μ := measure).
  - intros [] k' Hk'. apply send_round_correct. exact Hk'.
  - constructor; auto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (stenning_correct)

    We can now prove the main theorem: Stenning's protocol, running on
    an unreliable but eventually fair network, refines the reliable
    channel specification.

    Hint: follow the beginning of the proof of [bq_rb_correct] in
    [examples/CALCoTree.v].  Once the right-hand side has the shape
    [srun k (M_st _ (transmit v)) / L_net >>= K], use the definition
    of [sat] and [transmit_correct]. *)

Theorem stenning_correct :
  L_rc [~= srel_pull R_st @ slift M_st @ L_net.
Proof.
  intros _ [ar m log]. unfold Subst.compose, srel_pull, finf. cbn [CALspec_mor].
  rewrite !apply_inf. apply inf_glb. intros [k Hk]. cbn [proj1_sig].
  destruct m as [v]. cbn [L_rc].
  rewrite !apply_bind, apply_int_r. cbn [slift].
  apply (transmit_correct log v k Hk).
  intros [[] k'] Hk'. cbn.
  unfold fsup. rewrite !apply_sup. apply (sup_at (exist _ (log ++ v :: nil) Hk')). cbn.
  rewrite !apply_ret. reflexivity.
Qed.
(** [] *)


(* ################################################################# *)
(** * Further exercises *)

(** **** Exercise: 3 stars, standard, optional (bounded_seq)

    The alternating bit protocol is Stenning's protocol with sequence
    numbers taken modulo 2.  Modify [M_st] so that it only ever
    transmits [s mod 2] and compares acknowledgments modulo 2, and
    find a network behavior allowed by [L_net] under which a message
    is delivered twice.  Which part of the proof breaks? *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fresh_budget)

    The budget of [L_net] bounds the misbehaviors of the network over
    its whole lifetime.  A weaker assumption gives each channel its
    own budget, which is reset to a demonically chosen value whenever
    the channel behaves well: [inf b', ret (Some p, b')].  Adapt
    [L_net] and the invariants, and check that the protocol is still
    correct.  Hint: the measure becomes lexicographic: the data
    budget matters in the first phase, and the acknowledgment budget
    in the second. *)
(** [] *)

(** * StenningPlaysSolutions: Specifying and verifying a network protocol *)

(** This chapter introduces _interaction specifications_, as
    formalized in [models/ISpecCoTree.v], through a complete example:
    the verification of a classic network protocol.  No prior
    knowledge of the library is assumed.

    ** The problem

    A _sender_ wants to pass a stream of messages to a _receiver_ over
    a network that is unreliable: a packet may be

      - lost,
      - duplicated, or
      - delivered out of order, possibly long after it was sent.

    We would like the receiving application to obtain every message
    exactly once, in the order in which the sending application
    produced them.  In other words, on top of a bad network we would
    like to implement a _reliable channel_.

    Stenning's protocol (N. V. Stenning, "A data transfer protocol",
    1976) solves this problem with _sequence numbers_.  The sender
    tags every message with a number and retransmits it until it is
    acknowledged.  The receiver keeps track of the number it expects
    next: it passes a message on to the receiving application only if
    it carries that number, and it keeps telling the sender which
    number it is waiting for.  Because the network may replay
    arbitrarily old packets, the sequence numbers are unbounded.

    ** The plan

    We will

      - describe the behavior we want, a reliable channel, as a
        _specification_ [reliable];
      - write the protocol as two programs, [sender_step] and
        [receiver_step], running in parallel on top of a model of the
        network;
      - prove that the implementation _refines_ the specification,
        that is, [reliable [= impl init].

    Both the specification and the implementation run forever, so we
    need a way to reason about infinite behaviors.  We will use a
    single proof rule for this, [forever_ref], which works much like a
    loop invariant.

    As in Software Foundations, the chapter contains exercises marked
    with a difficulty rating.  Replace each [(* FILL IN HERE *)
    Admitted.] with a proof ending in [Qed.].  Every exercise can be
    solved using the lemmas stated before it. *)

From Stdlib Require Import List PeanoNat Lia.
From Stdlib Require Import Morphisms RelationClasses Setoid.
Require Import structures.Effects.
Require Import models.ISpecCoTree.
Require Import examples.CALCoTree.

Import ISpec.

(** A technical remark: the library declares [0] as a notation for the
    empty set of events, so in this chapter the natural number zero is
    written [O]. *)


(* ################################################################# *)
(** * Interaction specifications *)

(* ================================================================= *)
(** ** Events *)

(** A program interacts with its environment by performing _events_.
    The events available to a program are described by an _effect
    signature_ [E : esig], which is a family of types: an event
    [m : E ar] expects an answer of type [ar] from the environment.

    Here are the events by which our system interacts with the two
    applications: [input] asks the sending application for the next
    message, and [output v] hands the message [v] to the receiving
    application, which answers with the trivial value [tt].  Messages
    have type [val], an arbitrary type. *)

Inductive io_sig : esig :=
  | input : io_sig val
  | output (v : val) : io_sig unit.

(* ================================================================= *)
(** ** Trees *)

(** A program, or a specification, is a tree of type [t E A], where
    [A] is the type of the value it returns if it terminates.  Trees
    are built with the following operations:

      - [ret a] returns the value [a];
      - [int m] performs the event [m] and returns the answer;
      - [a <- x; f a], also written [x >>= f], runs [x] and then
        continues with [f a], where [a] is the value returned by [x];
      - [sup i : I, f i] lets the _system_ choose a value [i : I] and
        continues with [f i];
      - [inf i : I, f i] lets the _environment_ choose [i].

    The two kinds of choice are called _angelic_ ([sup]) and _demonic_
    ([inf]).  We write [x || y] and [x && y] for the binary versions,
    and [sup {i | P i}, f i] and [inf {i | P i}, f i] when the choice
    is restricted to the values satisfying [P].

    For example, the following tree reads a message and outputs it
    twice.  It returns [tt] once done. *)

Example echo_twice : t io_sig unit :=
  v <- int input;
  _ <- int (output v);
  int (output v).

(** Trees may be infinite.  A program that runs forever, like a
    server, is an infinite tree.  We will build infinite trees with
    two combinators, [forever] and [interleave], defined below. *)

(* ================================================================= *)
(** ** Refinement *)

(** The refinement relation [x [= y] states that the implementation
    [y] is at least as good as the specification [x].  To understand
    how it treats choices, think of a demonic choice [inf] as a choice
    made by an adversary, which we do not control, and of an angelic
    choice [sup] as a choice made in our favor.  Then:

      - a demonic choice in the specification [x] is a _freedom_ for
        the implementer: [y] may implement any one of the branches;
      - a demonic choice in the implementation [y], for instance the
        misbehavior of a network, is a _duty_: [y] must refine [x]
        whatever the adversary chooses;
      - dually, an angelic choice in [x] must be matched by [y] for
        every branch, while an angelic choice in [y] may be resolved
        in the way that suits us best;
      - visible events must match, and their continuations must be
        related, for every possible answer of the environment.

    Refinement is a preorder, and [x [=] y] means that both [x [= y]
    and [y [= x] hold.  Both relations can be used with [rewrite],
    [reflexivity] and [etransitivity].

    These are the basic properties of the choice operators: *)

Check sup_ub.    (* k i [= (sup j, k j) *)
Check sup_lub.   (* (forall i, k i [= y) -> (sup j, k j) [= y *)
Check sup_at.    (* x [= k i -> x [= (sup j, k j) *)
Check inf_lb.    (* (inf j, k j) [= k i *)
Check inf_glb.   (* (forall i, x [= k i) -> x [= (inf j, k j) *)
Check inf_at.    (* k i [= y -> (inf j, k j) [= y *)

(** The binary choices [x || y] and [x && y] are defined as choices
    over the booleans: see [join] and [meet], and the lemmas
    [join_ub_l], [join_lub], [meet_lb_l], [meet_glb], etc.

    [Vis m k] is the tree which performs the event [m] and continues
    with [k n], where [n] is the answer.  It is related to [int] by
    the law [bind_int].  Two trees that start with the same event are
    compared by comparing their continuations. *)

Check bind_int.  (* bind f (int m) [=] Vis m f *)
Check vis_mono.  (* (forall n, k n [= k' n) -> Vis m k [= Vis m k' *)

(** Sequential composition satisfies the laws of monads, distributes
    over choices, and is monotonic. *)

Check bind_ret_r. (* bind f (ret a) [=] f a *)
Check bind_ret_l. (* bind ret x [=] x *)
Check bind_bind.  (* bind g (bind f x) [=] bind (fun a => bind g (f a)) x *)
Check bind_sup.   (* bind f (sup j, k j) [=] (sup i, bind f (k i)) *)
Check bind_inf.   (* bind f (inf j, k j) [=] (inf i, bind f (k i)) *)
Check bind_mono.  (* (forall a, f a [= f' a) -> x [= x' -> bind f x [= bind f' x' *)

(** **** Exercise: 1 star, standard (choices)

    The implementation may resolve a demonic choice of the
    specification, and use an angelic choice of its own to match the
    specification. *)

Example choices (a b : nat) :
  ret (E := io_sig) a && ret b [= ret a /\
  ret (E := io_sig) a [= ret a || ret b.
Proof.
  split.
  - apply meet_lb_l.
  - apply join_ub_l.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (choose_then_add)

    Hint: [x && y] is defined as [meet x y]; [unfold] it to obtain an
    [Inf] over the booleans. *)

Example choose_then_add :
  (x <- (ret 1 && ret 2); ret (x + 1)) [= ret (E := io_sig) 2.
Proof.
  unfold meet. rewrite bind_inf. apply (inf_at true). rewrite bind_ret_r. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (duty)

    On the other hand, a demonic choice of the implementation must be
    handled in all cases.  Here the implementation returns [0] in both
    of them, so it does refine [ret 0]. *)

Example duty (n : nat) :
  ret (E := io_sig) O [= (x <- (ret n && ret (S n)); ret (x - x)).
Proof.
  unfold meet. rewrite bind_inf. apply inf_glb. intros [ | ];
    rewrite bind_ret_r, Nat.sub_diag; reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Silent steps and divergence *)

(** A silent step [Tau x] is an internal computation step, invisible
    to the environment. *)

Check tau_eqv.  (* Tau x [=] x *)

(** A program can also run forever without ever interacting with its
    environment, for instance [spin], which performs infinitely many
    silent steps.  Such a program is useless, and indeed it is the
    worst possible implementation: it refines nothing but the most
    permissive specifications. *)

Check spin_bot.  (* spin [= x *)

Lemma ret_not_ref_spin {E A} (a : A) :
  ~ (ret (E := E) a [= spin).
Proof.
  (* This proof requires knowledge of the internals of the library,
     and can be skipped. *)
  intros H. apply Ref.ref_unfold in H.
  remember (observe (ret (E := E) a)) as ox eqn:Hox.
  remember (observe (spin (E := E) (A := A))) as oy eqn:Hoy.
  cbn in Hox. induction H; try discriminate.
  cbn in Hoy. injection Hoy. intros Hk HI. subst J. inj_pair.
  apply IHrefF; auto.
Qed.

(** This has an important consequence for us.  The sender of our
    protocol retransmits its message until it is acknowledged.  If the
    network can lose every single packet, the sender may loop forever
    without anything visible happening, and the implementation would
    be no better than [spin].  We will therefore need to assume that
    the network is _fair_: it cannot misbehave forever. *)


(* ################################################################# *)
(** * Infinite behaviors *)

(* ================================================================= *)
(** ** Doing something forever *)

(** The combinator [forever body] runs [body] again and again, with a
    silent step between two iterations.  It never returns, so its
    result type [A] is arbitrary. *)

Definition forever {E A} (body : t E unit) : t E A :=
  cofix loop := _ <- body; Tau loop.

Lemma forever_unfold {E A} (body : t E unit) :
  forever (A := A) body [=] (_ <- body; Tau (forever body)).
Proof.
  split; apply Ref.ref_fold; exact (refF_refl_ref _).
Qed.

(** Our specification is now one line: a reliable channel forever
    reads a message from the sending application and gives it to the
    receiving application. *)

Definition reliable {A} : t io_sig A :=
  forever (v <- int input; int (output v)).

(** How can we prove that a program refines an infinite specification
    like [reliable]?  Unfolding [forever] repeatedly does not work:
    there would always be more to unfold.  Instead we use the following
    rule, which is the analogue of a loop invariant.

    Suppose that we have a family of implementations [impl σ], indexed
    by some states [σ], and an invariant [I] on these states.  To show
    that [forever body] is refined by [impl σ] when [I σ] holds, it
    suffices to show that each [impl σ] performs one iteration of
    [body], and then continues as one of the [impl σ'] with [I σ'].
    "One of" is expressed with a demonic choice: at the end of the
    iteration we may not know which state we are in, and [impl] has to
    be good in all of them. *)

Lemma forever_ref {E A S} (body : t E unit) (I : S -> Prop) (impl : S -> t E A) :
  (forall σ, I σ -> (_ <- body; inf {σ' | I σ'}, impl σ') [= impl σ) ->
  forall σ, I σ -> forever body [= impl σ.
Proof.
  (* This proof uses coinduction, a proof technique for infinite
     objects which is beyond the scope of this chapter, and can be
     skipped. *)
  intros H.
  set (J := inf {σ' | I σ'}, impl σ').
  set (u0 := forever (A := A) body).
  set (R := fun u w => (u = u0 \/ u = Tau u0) /\ w = J).
  assert (Htau : Ref.refF (upclo R) (observe (Tau u0)) (observe J)).
  { constructor. intros _. exists J. split; [ left; split; auto | apply go_observe_r ]. }
  assert (HJ : u0 [= J).
  { apply (ref_coind_up R); [ | split; auto ].
    intros u w [[-> | ->] ->]; [ | exact Htau ].
    change (observe J) with (@InfF E A (t E A) (sig I) (fun z => impl (proj1_sig z))).
    apply Ref.refF_inf_r. intros [σ Hσ]. cbn [proj1_sig].
    specialize (H σ Hσ). apply Ref.ref_unfold in H. rewrite observe_bind in H.
    change (observe u0) with (observe (bind (fun _ => Tau u0) body)).
    rewrite observe_bind.
    eapply Ref.refF_mono; [ | eapply Ref.cut_r with (X := upclo R); [ | exact H ] ].
    - intros a c (b & (v & Hav & Hvb) & Hbc).
      exists v. split; [ exact Hav | etransitivity; eauto ].
    - apply bindclo_layer with (L := fun a b => a = Tau u0 /\ b = J).
      + intros a b (X & y & y' & k & k' & Ha & Hb & Hy & Hk).
        exists b. split; [ | reflexivity ]. right. right.
        exists X, y, y', k, k'. split; [ exact Ha | ]. split; [ exact Hb | ].
        split; [ exact Hy | ]. intros x. destruct (Hk x) as [-> ->]. split; auto.
      + intros a b [-> ->]. exact Htau.
      + intros _. split; reflexivity.
      + apply refF_refl_ref. }
  intros σ Hσ. etransitivity; [ exact HJ | ].
  exact (inf_lb (fun z : sig I => impl (proj1_sig z)) (exist _ σ Hσ)).
Qed.

(** **** Exercise: 2 stars, standard (echo)

    An echo server that takes a silent step before answering is a
    reliable channel.  Use [forever_ref] with a trivial invariant. *)

Definition slow_echo {A} : t io_sig A :=
  forever (v <- int input; _ <- Tau (ret tt); int (output v)).

Example slow_echo_reliable {A} :
  reliable (A := A) [= slow_echo.
Proof.
  apply (forever_ref _ (fun _ : unit => True) (fun _ => slow_echo)); [ | exact tt | exact I ].
  intros [] _. unfold slow_echo at 2. rewrite forever_unfold.
  apply bind_mono.
  - intros _. etransitivity; [ | apply tau_r ].
    apply (inf_at (exist _ tt I)). reflexivity.
  - apply bind_mono; [ intros v | reflexivity ].
    rewrite tau_eqv, bind_ret_r. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Running two processes in parallel *)

(** The implementation consists of two processes, each described by a
    _step function_ [f : X -> t E X] which performs one step from a
    local state of type [X] and returns the new local state.  The
    combinator [interleave f g] runs them forever, in rounds: at each
    round the first process takes a step, then the second one.  The
    process states are passed from one round to the next. *)

Definition both {E X Y} (f : X -> t E X) (g : Y -> t E Y) (xy : X * Y) : t E (X * Y) :=
  let '(x, y) := xy in
  x' <- f x;
  y' <- g y;
  ret (x', y').

Definition interleave {E X Y A} (f : X -> t E X) (g : Y -> t E Y) : X * Y -> t E A :=
  iter (fun xy => p <- both f g xy; ret (inl p)).

Lemma interleave_unfold {E X Y A} (f : X -> t E X) (g : Y -> t E Y) xy :
  interleave (A := A) f g xy [=] (p <- both f g xy; Tau (interleave f g p)).
Proof.
  unfold interleave at 1. rewrite iter_unfold, bind_bind.
  apply bind_eqv_proper; [ | reflexivity ].
  intros p. rewrite bind_ret_r. reflexivity.
Qed.


(* ################################################################# *)
(** * The network *)

(** The sender and the receiver communicate through two channels: the
    data channel carries packets [(n, v)] made of a sequence number and
    a message, and the acknowledgment channel carries sequence numbers
    back to the sender. *)

Inductive chan_sig : esig :=
  | send_data (n : nat) (v : val) : chan_sig unit
  | recv_data : chan_sig (option (nat * val))
  | send_ack (n : nat) : chan_sig unit
  | recv_ack : chan_sig (option nat).

(** A channel is modelled by the history of all the packets ever sent
    on it, the most recent first.  When asked for a packet, the
    channel either returns the most recent one, or it misbehaves: it
    loses the packet, returning [None], or it replays any packet from
    its history.  Replaying captures both duplication and reordering.

    The network is the adversary, so all of these choices are demonic.
    To make the network fair, we give it a _budget_ [b]: every
    misbehavior costs one unit, and a network with an empty budget
    must behave.  The initial budget is arbitrary, and the protocol
    cannot observe it: the protocol has to work for networks that
    misbehave any finite number of times. *)

Definition rx {E P} (h : list P) (b : nat) : t E (option P * nat) :=
  match h with
    | nil => ret (None, b)
    | p :: _ =>
      ret (Some p, b) &&
      (inf {o : option P | b <> O /\ (o = None \/ exists q, o = Some q /\ In q h)},
       ret (o, b - 1))
  end.

Record chan_state :=
  mk_chan {
    dchan : list (nat * val);
    achan : list nat;
    budget : nat;
  }.

Definition L_chan {E} : forall ar, chan_sig ar -> chan_state -> t E (ar * chan_state) :=
  fun _ m '(mk_chan dc ac b) =>
    match m with
      | send_data n v => ret (tt, mk_chan ((n, v) :: dc) ac b)
      | recv_data => p <- rx dc b; ret (fst p, mk_chan dc ac (snd p))
      | send_ack n => ret (tt, mk_chan dc (n :: ac) b)
      | recv_ack => p <- rx ac b; ret (fst p, mk_chan dc ac (snd p))
    end.

(** **** Exercise: 2 stars, standard (rx_ref)

    The following lemma lists the possible outcomes of a channel.  It
    is the only fact about [rx] we will use afterwards: [y] is below
    [rx h b >>= f] if it is below all the possible continuations. *)

Definition rx_ok {P} (h : list P) (b : nat) (o : option P) (b' : nat) : Prop :=
  (o = hd_error h /\ b' = b) \/
  (b <> O /\ b' = b - 1 /\ (o = None \/ exists q, o = Some q /\ In q h)).

Lemma rx_ref {E P B} (h : list P) (b : nat) (y : t E B) (f : option P * nat -> t E B) :
  (forall o b', rx_ok h b o b' -> y [= f (o, b')) ->
  y [= rx h b >>= f.
Proof.
  intros H. destruct h as [ | p h]; cbn.
  - rewrite bind_ret_r. apply H. left. auto.
  - unfold meet. rewrite bind_inf. apply inf_glb. intros [ | ].
    + rewrite bind_ret_r. apply H. left. auto.
    + unfold finf. rewrite bind_inf. apply inf_glb. intros [o [Hb Ho]]. cbn.
      rewrite bind_ret_r. apply H. right. auto.
Qed.
(** [] *)

(** The processes perform both kinds of events.  We combine the two
    signatures, and write [io m] and [net m] for the corresponding
    operations. *)

Definition E_sys : esig := esum io_sig chan_sig.

Abbreviation io m := (int (E := E_sys) (einl m)).
Abbreviation net m := (int (E := E_sys) (einr m)).

(** To run a process [P] on the network, starting with channels in the
    state [c], we keep track of the state of the channels and
    interpret each [net] operation with [L_chan], while the [io]
    events are left untouched.  The result [run_net c P] is a tree
    which only performs [io] events, and returns the result of [P]
    together with the final state of the channels.  (We use the
    operations [srun] and [Subst.apply] from [examples/CALCoTree.v] and
    [models/ISpecCoTree.v], but you do not need to know how they
    work.) *)

Definition handle_sys {ar} (m : E_sys ar) (k : chan_state) : t io_sig (ar * chan_state) :=
  match m with
    | einl m' => x <- int m'; ret (x, k)
    | einr m' => L_chan _ m' k
  end.

Definition handle : io_sig ~> E_sys # chan_state :=
  fun _ '(st m k) => handle_sys m k.

Abbreviation run_net c P := (Subst.apply handle (srun c P)).


(* ################################################################# *)
(** * The protocol *)

(** The sender is either idle, in which case it asks the sending
    application for the next message, or busy transmitting a message
    [v] with sequence number [s].  At each step a busy sender
    transmits its packet and looks for an acknowledgment.  It becomes
    idle when the receiver acknowledges, by asking for [S s], that it
    has received the message. *)

Definition sender_state : Type := nat * option val.

Definition sender_step (x : sender_state) : t E_sys sender_state :=
  match x with
    | (s, None) =>
      v <- io input;
      ret (s, Some v)
    | (s, Some v) =>
      _ <- net (send_data s v);
      a <- net recv_ack;
      ret (match a with
             | Some n => if Nat.eqb n (S s) then (S s, None) else (s, Some v)
             | None => (s, Some v)
           end)
  end.

(** The receiver's state is the sequence number [e] it expects next.
    At each step it takes a packet from the data channel.  If the
    packet carries [e], the message is passed on to the receiving
    application.  In any case the receiver acknowledges by sending
    back the number it now expects. *)

Definition receiver_step (e : nat) : t E_sys nat :=
  p <- net recv_data;
  match p with
    | None => ret e
    | Some (n, w) =>
      if Nat.eqb n e then
        _ <- io (output w);
        _ <- net (send_ack (S e));
        ret (S e)
      else
        _ <- net (send_ack e);
        ret e
  end.

(** A _configuration_ of the system consists of the states of the two
    processes and of the network.  The behavior of a configuration is
    that of the two processes interleaved, running on the network. *)

Definition config : Type := sender_state * nat * chan_state.

Definition impl (σ : config) : t io_sig (False * chan_state) :=
  run_net (snd σ) (interleave sender_step receiver_step (fst σ)).

(** The goal of this chapter is to prove that the initial
    configuration, in which both sequence numbers are [O] and nothing
    has been sent yet, implements a reliable channel, whatever the
    budget [b] of the network:

      [reliable [= impl ((O, None), O, mk_chan nil nil b)]. *)


(* ################################################################# *)
(** * Symbolic execution *)

(** The behavior of a configuration is one round, followed by a silent
    step and the behavior of the resulting configuration.  The proof
    uses some laws about [srun] and [Subst.apply], and can be
    skipped. *)

Lemma srun_tau {E S A} (k : S) (x : t E A) :
  srun k (Tau x) [=] Tau (srun k x).
Proof.
  split; apply Ref.ref_fold; rewrite observe_srun; cbn; apply refF_refl_ref.
Qed.

Lemma impl_unfold xy c :
  impl (xy, c) [=] (σ <- run_net c (both sender_step receiver_step xy); Tau (impl σ)).
Proof.
  unfold impl. cbn [fst snd].
  rewrite interleave_unfold, srun_bind, apply_bind.
  apply bind_eqv_proper; [ | reflexivity ].
  intros [p c']. cbn [fst snd].
  rewrite srun_tau, apply_tau. reflexivity.
Qed.

(** We will reason about the behavior of a round by _symbolic
    execution_: the following tactic executes the first operation of
    the round, on goals of the form [y [= σ <- run_net c P; K σ].  It
    stops when the next step depends on a value which is not known,
    typically the outcome of a channel. *)

Ltac run :=
  match goal with
    | |- _ [= bind _ (Subst.apply _ (srun _ (bind _ _))) =>
      rewrite srun_bind, apply_bind, bind_bind
    | |- _ [= bind _ (Subst.apply _ (srun _ (ret _))) =>
      rewrite srun_ret, apply_ret, bind_ret_r; cbn [fst snd]
    | |- _ [= bind _ (Subst.apply _ (srun _ (int (einr _)))) =>
      rewrite srun_int, apply_int_r; cbn [handle handle_sys L_chan]
    | |- _ [= bind _ (Subst.apply _ (srun _ (int (einl _)))) =>
      rewrite srun_int, apply_int_r; cbn [handle handle_sys]; rewrite bind_bind, bind_int
    | |- _ [= bind _ (ret _) =>
      rewrite bind_ret_r; cbn [fst snd]
    | |- _ [= bind _ (bind _ (rx _ _)) =>
      rewrite bind_bind; apply rx_ref;
      let o := fresh "o" in let b := fresh "b" in let Hok := fresh "Hok" in
      intros o b Hok; cbn [fst snd]
    | |- Vis ?m _ [= Vis ?m _ =>
      apply vis_mono; let v := fresh "v" in intros v; cbn [fst snd]
  end.

(** Note that when [run] meets a channel operation, it introduces the
    outcome [o], the new budget [b], and the hypothesis [Hok] which
    describes the possible outcomes.  When it meets an [io] event, the
    goal must have the form [Vis m k [= Vis m k']], and [run] moves on
    to the continuations. *)


(* ################################################################# *)
(** * Invariants *)

(** We now describe which configurations correspond to each point of
    the specification [reliable].  Either the specification is [Ready]
    to read a new message, or it has read [v] and is about to output
    it, which we write [Pending v]. *)

Inductive spec_state :=
  | Ready
  | Pending (v : val).

(** When the specification is [Ready], either the sender is idle, or
    the receiver has already output the sender's current message but
    the sender has not yet received the acknowledgment.  When the
    specification is [Pending v], the sender is transmitting [v] and
    the receiver has not output it yet.  In each case, the invariant
    also bounds the sequence numbers found in the channels.  In
    particular, while [v] is pending, every packet with the sequence
    number [s] carries [v]: this is why the receiver never outputs a
    wrong message. *)

Inductive good : config -> spec_state -> Prop :=
  | good_idle s dc ac b :
      Forall (fun p => fst p < s) dc ->
      Forall (fun a => a <= s) ac ->
      good ((s, None), s, mk_chan dc ac b) Ready
  | good_acking s v dc ac b :
      Forall (fun p => fst p <= s) dc ->
      Forall (fun a => a <= S s) ac ->
      good ((s, Some v), S s, mk_chan dc (S s :: ac) b) Ready
  | good_sending s v dc ac b :
      Forall (fun p => fst p < s \/ p = (s, v)) dc ->
      Forall (fun a => a <= s) ac ->
      good ((s, Some v), s, mk_chan dc ac b) (Pending v).

Lemma good_init b :
  good ((O, None), O, mk_chan nil nil b) Ready.
Proof.
  constructor; constructor.
Qed.

(** The following tactic proves the [Forall] conditions which arise
    when checking that a new configuration is [good]. *)

Ltac bounds :=
  repeat match goal with
         | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
         end;
  cbn [fst] in *;
  repeat (apply Forall_cons; [ cbn; first [ lia | left; cbn; lia | right; reflexivity ] | ]);
  try first
    [ eassumption
    | eapply Forall_impl; [ | eassumption ];
       intros ? Hp; cbn in Hp |- *;
       first [ lia | left; lia | destruct Hp as [Hp | ->]; cbn; lia ] ].

Lemma Forall_In_cons {X} (P : X -> Prop) x l y :
  P x -> Forall P l -> In y (x :: l) -> P y.
Proof.
  intros Hx Hl [<- | Hy]; auto. rewrite Forall_forall in Hl. auto.
Qed.

(** The implementation of a point [q] of the specification is the
    demonic choice of all the configurations corresponding to [q]. *)

Definition impls (q : spec_state) : t io_sig (False * chan_state) :=
  inf {σ | good σ q}, impl σ.

(** **** Exercise: 1 star, standard (impls_tau) *)

Lemma impls_tau q σ :
  good σ q -> impls q [= Tau (impl σ).
Proof.
  intros H. etransitivity; [ | apply tau_r ].
  apply (inf_at (exist _ σ H)). reflexivity.
Qed.
(** [] *)


(* ################################################################# *)
(** * Progress *)

(** It remains to show that each configuration does what the
    specification expects.  The difficulty is that the next visible
    event may take several rounds to happen: while the network loses
    packets, the processes only communicate silently.  The fairness
    budget ensures that this does not go on forever.  We measure the
    amount of silent work that may remain as follows: in an [acking]
    configuration, one silent round may be needed to come back to the
    idle state, hence the extra unit. *)

Definition measure (σ : config) : nat :=
  budget (snd σ) + (snd (fst σ) - fst (fst (fst σ))).

(** Hint for the two exercises below: proceed by strong induction on
    the measure, as in the following skeleton.  Then [inversion] the
    invariant, unfold one round with [impl_unfold], unfold [both],
    [sender_step] and [receiver_step], and use the tactic [run].  When
    [run] stops on a [match] or an [if], do the case analysis with the
    hypothesis [Hok], [Nat.eqb_spec] or [Nat.eqb_refl].  At the end of
    a round, use [impls_tau] if the expected event has happened, and
    the induction hypothesis together with [tau_r] otherwise.  The
    tactic [bounds] proves the [Forall] conditions. *)

(** **** Exercise: 4 stars, standard (progress_ready)

    From a configuration corresponding to [Ready], the system
    eventually reads a message [v] and reaches a configuration
    corresponding to [Pending v]. *)

Lemma progress_ready σ :
  good σ Ready ->
  Vis input (fun v => impls (Pending v)) [= impl σ.
Proof.
  set (y := Vis input (fun v => impls (Pending v))).
  assert (H : forall m σ, measure σ < m -> good σ Ready -> y [= impl σ).
  2: { intros Hσ. eapply H; eauto. }
  induction m as [ | m IHm]; intros σ' Hm Hσ; [ lia | ].
  inversion Hσ as [s dc ac b Hd Ha | s v dc ac b Hd Ha | ]; subst; clear Hσ;
    unfold measure in Hm; cbn [fst snd budget] in Hm;
    rewrite impl_unfold; unfold both, sender_step, receiver_step; cbn [fst snd].
  - (* idle: the sender reads the next message, the receiver only
       sees old packets *)
    unfold y. repeat run.
    destruct Hok as [[-> ->] | (Hb & -> & [-> | ([n w] & -> & Hq)])].
    + destruct dc as [ | [n w] dc]; cbn [hd_error]; repeat run.
      * apply impls_tau. constructor; bounds.
      * pose proof (Forall_inv Hd) as Hn. cbn in Hn.
        destruct (Nat.eqb_spec n s); [ lia | ]. repeat run.
        apply impls_tau. constructor; bounds.
    + repeat run. apply impls_tau. constructor; bounds.
    + rewrite Forall_forall in Hd. apply Hd in Hq. cbn in Hq.
      destruct (Nat.eqb_spec n s); [ lia | ]. repeat run.
      apply impls_tau. rewrite <- Forall_forall in Hd. constructor; bounds.
  - (* acking: the sender waits for the acknowledgment *)
    repeat run.
    destruct Hok as [[-> ->] | (Hb & -> & [-> | (q & -> & Hq)])]; cbn [hd_error];
      [ rewrite Nat.eqb_refl | | destruct (Nat.eqb_spec q (S s)) as [-> | Hq'] ];
      destruct Hok0 as [[-> ->] | (Hb' & -> & [-> | ([n w] & -> & Hq0)])]; cbn [hd_error];
      try (destruct (Nat.eqb_spec s (S s)); [ lia | ]);
      try (assert (n <= s)
             by (apply (Forall_In_cons (fun p => fst p <= s) (s, v) dc (n, w)); auto);
           destruct (Nat.eqb_spec n (S s)); [ lia | ]);
      repeat run;
      (etransitivity; [ apply IHm | apply tau_r ]);
      solve [ unfold measure; cbn [fst snd budget]; lia | constructor; bounds ].
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard (progress_pending)

    From a configuration corresponding to [Pending v], the system
    eventually outputs [v] and reaches a configuration corresponding to
    [Ready].  This is where the sequence numbers matter: the receiver
    outputs a message only when it carries the expected sequence
    number, and the invariant guarantees that all such packets carry
    [v]. *)

Lemma progress_pending v σ :
  good σ (Pending v) ->
  Vis (output v) (fun _ => impls Ready) [= impl σ.
Proof.
  set (y := Vis (output v) (fun _ => impls Ready)).
  assert (H : forall m σ, measure σ < m -> good σ (Pending v) -> y [= impl σ).
  2: { intros Hσ. eapply H; eauto. }
  induction m as [ | m IHm]; intros σ' Hm Hσ; [ lia | ].
  inversion Hσ as [ | | s v' dc ac b Hd Ha]; subst; clear Hσ.
  unfold measure in Hm; cbn [fst snd budget] in Hm.
  rewrite impl_unfold; unfold both, sender_step, receiver_step; cbn [fst snd].
  repeat run.
  (* The acknowledgments are all old: the sender keeps transmitting. *)
  assert (Ho : forall n, o = Some n -> n <> S s).
  { intros n ->. destruct Hok as [[Ho _] | (_ & _ & [Ho | (q & Ho & Hq)])].
    - destruct ac as [ | a ac]; cbn in Ho; inversion Ho; subst.
      apply Forall_inv in Ha. lia.
    - discriminate.
    - injection Ho as <-. rewrite Forall_forall in Ha. apply Ha in Hq. lia. }
  assert (Hb0 : b0 <= b) by (destruct Hok as [[_ ->] | (_ & -> & _)]; lia).
  assert (Hst : match o with
                | Some n => if n =? S s then (S s, None) else (s, Some v)
                | None => (s, Some v)
                end = (s, Some v)).
  { destruct o as [n | ]; auto. destruct (Nat.eqb_spec n (S s)); auto.
    exfalso. eapply Ho; eauto. }
  rewrite Hst. clear Hst Ho.
  destruct Hok0 as [[-> ->] | (Hb' & -> & [-> | ([n w] & -> & Hq0)])]; cbn [hd_error].
  - (* the packet goes through *)
    rewrite Nat.eqb_refl. unfold y. repeat run.
    apply impls_tau. constructor; bounds.
  - (* the packet is lost *)
    repeat run.
    etransitivity; [ apply IHm | apply tau_r ].
    + unfold measure; cbn [fst snd budget]. lia.
    + constructor; bounds.
  - (* an older packet, or a copy of the current one, is replayed *)
    assert (Hnw : fst (n, w) < s \/ (n, w) = (s, v)).
    { apply (Forall_In_cons (fun p => fst p < s \/ p = (s, v)) (s, v) dc); auto. }
    destruct Hnw as [Hn | Hnw].
    + cbn [fst] in Hn. destruct (Nat.eqb_spec n s); [ lia | ]. repeat run.
      etransitivity; [ apply IHm | apply tau_r ].
      * unfold measure; cbn [fst snd budget]. lia.
      * constructor; bounds.
    + injection Hnw as -> ->. rewrite Nat.eqb_refl. unfold y. repeat run.
      apply impls_tau. constructor; bounds.
Qed.
(** [] *)


(* ################################################################# *)
(** * Correctness *)

(** **** Exercise: 3 stars, standard (stenning_correct)

    Stenning's protocol, running on a network which misbehaves finitely
    often, implements a reliable channel.

    Hint: use [forever_ref] with the invariant [fun σ => good σ Ready].
    The demonic choice it introduces is exactly [impls Ready].  Rewrite
    the iteration of the body with [bind_bind] and [bind_int], then
    combine [progress_ready] and [progress_pending]. *)

Theorem stenning_correct b :
  reliable [= impl ((O, None), O, mk_chan nil nil b).
Proof.
  apply (forever_ref _ (fun σ => good σ Ready) impl); [ | apply good_init ].
  intros σ Hσ. rewrite bind_bind, bind_int.
  etransitivity; [ | apply progress_ready; exact Hσ ].
  apply vis_mono. intros v. rewrite bind_int.
  unfold impls at 1. unfold finf at 2. apply inf_glb. intros [σ' Hσ']. cbn [proj1_sig].
  apply progress_pending. exact Hσ'.
Qed.
(** [] *)


(* ################################################################# *)
(** * Further exercises *)

(** **** Exercise: 2 stars, standard, optional (why_inf)

    In [forever_ref], why does the continuation of each iteration
    have to be a demonic choice of configurations?  Find a step of
    [progress_ready] after which the configuration reached depends on
    a choice of the network. *)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bounded_seq)

    The alternating bit protocol is Stenning's protocol with sequence
    numbers taken modulo 2.  Modify [sender_step] and [receiver_step]
    accordingly, and find a behavior of the network under which a
    message is output twice.  Which part of the proof breaks? *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (demonic_scheduler)

    The combinator [interleave] uses a fixed round-robin schedule.
    Define a variant in which the environment decides, at each round,
    which process runs, subject to a fairness budget of its own, and
    adapt the proof. *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (fresh_budget)

    The budget bounds the misbehaviors of the network over its whole
    lifetime.  A weaker assumption gives each channel its own budget,
    which is reset to a demonically chosen value whenever the channel
    behaves well.  Adapt [L_chan], the invariants and the measure, and
    check that the protocol is still correct. *)
(** [] *)

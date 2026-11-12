(** * StenningIntSpec: Specifying and verifying a network protocol *)

(** This chapter introduces _interaction specifications_, as
    formalized in [models/IntSpec.v], through a complete example:
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
        that is, [reliable Ready [= impl init].

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
From Stdlib Require Import FunctionalExtensionality.
Require Import models.IntSpec.

Import ISpec.

Parameter val : Type.

Notation "x >>= f" := (bind f x)
  (at level 40, left associativity).

Notation "v <- x ; M" := (x >>= fun v => M)
  (at level 65, right associativity).

Notation "' p <- x ; M" := (x >>= fun p => M)
  (at level 65, p pattern at level 0, right associativity, only parsing).


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
(** ** Specifications *)

(** A program, or a specification, is an element of type [t E A],
    where [A] is the type of the value it returns if it terminates.
    Specifications are built with the following operations:

      - [ret a] returns the value [a];
      - [int m] performs the event [m] and returns the answer;
      - [a <- x; f a], also written [x >>= f], runs [x] and then
        continues with [f a], where [a] is the value returned by [x];
      - [sup i, f i] lets the _system_ choose a value [i] and
        continues with [f i];
      - [inf i, f i] lets the _environment_ choose [i].

    The two kinds of choice are called _angelic_ ([sup]) and _demonic_
    ([inf]).  We write [x || y] and [x && y] for the binary versions,
    and [sup {i | P i}, f i] and [inf {i | P i}, f i] when the choice
    is restricted to the values satisfying [P].

    For example, the following specification reads a message and
    outputs it twice.  It returns [tt] once done. *)

Example echo_twice : t io_sig unit :=
  v <- int input;
  _ <- int (output v);
  int (output v).

Definition p := (v <- int input; ret tt).
Print p.

(** Under the hood, a specification is described by the finite
    _plays_ it allows: sequences of events, each with the answer of
    the environment, possibly ended by a return value.  [t E A] is the
    free completely distributive lattice over these plays, which is
    where [sup] and [inf] come from.  You will not need to know more
    than this.

    A program that runs forever, like a server, is described by all
    the finite prefixes of its runs.  We will build such programs with
    one combinator, [forever], defined below. *)

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

    Refinement is a partial order: two specifications which refine
    each other are equal ([antisymmetry]).  So the laws below are
    stated as equations, and can be used with [rewrite].  Refinement
    itself can be used with [reflexivity] and [etransitivity].

    These are the basic properties of the choice operators: *)

Check sup_ub.    (* k i [= (sup j, k j) *)
Check sup_lub.   (* (forall i, k i [= y) -> (sup j, k j) [= y *)
Check sup_at.    (* x [= k i -> x [= (sup j, k j) *)
Check inf_lb.    (* (inf j, k j) [= k i *)
Check inf_glb.   (* (forall i, x [= k i) -> x [= (inf j, k j) *)
Check inf_at.    (* k i [= y -> (inf j, k j) [= y *)

(** The restricted versions have the same properties: see [fsup_ub],
    [fsup_lub], [fsup_at], [finf_lb], [finf_glb] and [finf_at].  The
    binary choices [x || y] and [x && y] have the properties
    [join_ub_l], [join_ub_r], [join_lub], [meet_lb_l], [meet_lb_r] and
    [meet_glb].

    Sequential composition distributes over choices, and two programs
    that do the same thing first are compared by comparing their
    continuations. *)

Lemma bind_sup {E A B I} (f : A -> t E B) (k : I -> t E A) :
  bind f (sup i, k i) = sup i, bind f (k i).
Proof. apply (Sup.mor (f := bind f)). Qed.

Lemma bind_inf {E A B I} (f : A -> t E B) (k : I -> t E A) :
  bind f (inf i, k i) = inf i, bind f (k i).
Proof. apply (Inf.mor (f := bind f)). Qed.

Section BINARY.
  (* The library keeps [join] and [meet] opaque; we open them up just
     long enough to prove these two laws. *)
  Local Transparent join meet.

  Lemma bind_join {E A B} (f : A -> t E B) (x y : t E A) :
    bind f (x || y) = bind f x || bind f y.
  Proof.
    unfold join. rewrite bind_sup. f_equal.
    apply functional_extensionality. intros [ | ]; reflexivity.
  Qed.

  Lemma bind_meet {E A B} (f : A -> t E B) (x y : t E A) :
    bind f (x && y) = bind f x && bind f y.
  Proof.
    unfold meet. rewrite bind_inf. f_equal.
    apply functional_extensionality. intros [ | ]; reflexivity.
  Qed.
End BINARY.

Check bind_mono. (* (forall a, f a [= g a) -> bind f x [= bind g x *)

(** The unit laws of monads hold as usual. *)

Check bind_ret_r. (* bind f (ret a) = f a *)
Check bind_ret_l. (* bind ret x = x *)

(** Associativity is more delicate.  In [models/IntSpec.v] the full
    law [bind_bind] needs a classical assumption, but one direction
    holds outright: *)

Check bind_bind_le.
(* bind (fun a => bind g (f a)) x [= bind g (bind f x) *)

(** This is the direction we need on the side of the implementation:
    to show [y [= bind g (bind f x)], it is enough to show [y] below
    the right-nested version.  We package this as a lemma. *)

Lemma reassoc {E A B C} (y : t E C) (g : B -> t E C) (f : A -> t E B) (x : t E A) :
  y [= bind (fun a => bind g (f a)) x ->
  y [= bind g (bind f x).
Proof.
  intros H. etransitivity; [ exact H | apply bind_bind_le ].
Qed.

(** When the inner computation ends with [ret], the law holds in both
    directions.  We will use it on the side of the specification. *)

Check bind_bind_ret.
(* bind g (bind (fun a => ret (h a)) x) = bind (fun a => g (h a)) x *)

(** **** Exercise: 1 star, standard (choices)

    The implementation may resolve a demonic choice of the
    specification, and use an angelic choice of its own to match the
    specification. *)

Example choices (a b : nat) :
  ret (E := io_sig) a && ret b [= ret a /\
  ret (E := io_sig) a [= ret a || ret b.
Proof.
  (*
    binary choices [x || y] and [x && y] have the properties
    [join_ub_l], [join_ub_r], [join_lub], [meet_lb_l], [meet_lb_r] and
    [meet_glb].
  *)
  split.
  - apply meet_lb_l.
  - apply join_ub_l.
  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (choose_then_add)

    Hint: [bind_meet]. *)

Example choose_then_add :
  (x <- (ret 1 && ret 2); ret (x + 1)) [= ret (E := io_sig) 2.
Proof.
  Search ret ref.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (duty)

    On the other hand, a demonic choice of the implementation must be
    handled in all cases.  Here the implementation returns [0] in both
    of them, so it does refine [ret 0]. *)

Example duty (n : nat) :
  ret (E := io_sig) 0 [= (x <- (ret n && ret (S n)); ret (x - x)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Divergence *)

(** A program can run forever without ever interacting with its
    environment.  The simplest one is [spin], the least solution of
    the equation [spin = spin].  It allows no play at all, so it is
    the least element and the worst possible implementation: it
    refines nothing but the most permissive specifications. *)

Definition spin {E A} : t E A :=
  lfp (fun x => x).

Lemma spin_bot {E A} (x : t E A) :
  spin [= x.
Proof.
  apply lfp_least. reflexivity.
Qed.

Lemma ret_not_ref_spin {E A} (a : A) :
  ~ (ret (E := E) a [= spin).
Proof.
  (* This proof requires knowledge of the internals of the library,
     and can be skipped. *)
  intros H.
  assert (Hb : ret (E := E) a [= bot) by (rewrite H; apply spin_bot).
  apply (has_bot (C := Upset.Fpos (play_poset E A)) (@Upset.up (play_poset E A) (pret a))).
  apply Hb. apply FCD.emb_has. intros ? Hp. exact Hp.
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

(** A program that runs forever is described by a _step function_
    [step : S -> t E S], which performs one step from a state of type
    [S] and returns the new state.  The combinator [forever step s]
    runs [step] again and again, starting from the state [s].  It
    never returns, so its result type [A] is arbitrary.

    [t E A] is a complete lattice, and so are the functions from [S]
    into it, ordered pointwise ([PProd.Pccd]).  We define [forever] as
    the least fixed point of its unfolding.  No coinduction is
    needed. *)

Definition forever_body {E S A} (step : S -> t E S) (k : S -> t E A) : S -> t E A :=
  fun s => s' <- step s; k s'.

Definition forever {E S A} (step : S -> t E S) : S -> t E A :=
  lfp (L := PProd.Pccd (fun _ : S => t E A)) (forever_body step).

Global Instance forever_body_mor {E S A} (step : S -> t E S) :
  PosetMorphism (C := PProd.Pccd (fun _ : S => t E A))
                (D := PProd.Pccd (fun _ : S => t E A))
                (forever_body step).
Proof.
  intros k k' Hk s. apply bind_mono. intros s'. apply Hk.
Qed.

Lemma forever_unfold {E S A} (step : S -> t E S) (s : S) :
  forever (A := A) step s = (s' <- step s; forever step s').
Proof.
  unfold forever at 1.
  rewrite <- (lfp_fixed (L := PProd.Pccd (fun _ : S => t E A)) (forever_body step)).
  reflexivity.
Qed.

(** Our specification is a step function with two states.  Either the
    channel is [Ready] to read a new message, or it has read [v] and
    is about to output it, which we write [Pending v]. *)

Inductive spec_state :=
  | Ready
  | Pending (v : val).

Definition spec_step (q : spec_state) : t io_sig spec_state :=
  match q with
    | Ready => v <- int input; ret (Pending v)
    | Pending v => _ <- int (output v); ret Ready
  end.

(** A reliable channel, then, forever reads a message from the sending
    application and gives it to the receiving application. *)

Definition reliable {A} : spec_state -> t io_sig A :=
  forever spec_step.

(** How can we prove that a program refines an infinite specification
    like [reliable]?  Unfolding [forever] repeatedly does not work:
    there would always be more to unfold.  Instead we use the following
    rule, which is the analogue of a loop invariant.

    Suppose that we have a family of implementations [impl σ], indexed
    by some states [σ], and a relation [R] between the states [q] of
    the specification and the states [σ] of the implementation.  To
    show that [forever step q] is refined by [impl σ] when [R q σ]
    holds, it suffices to show that each [impl σ] performs one step of
    the specification, from [q] to some [q'], and then continues as
    one of the [impl σ'] with [R q' σ'].  "One of" is expressed with a
    demonic choice: at the end of the step we may not know which state
    we are in, and [impl] has to be good in all of them.

    Since [forever step] is a least fixed point, the rule is just the
    fact that it lies below every function [k] with
    [forever_body step k [= k] ([lfp_least]). *)

Lemma forever_ref {E Q S A} (step : Q -> t E Q) (R : Q -> S -> Prop) (impl : S -> t E A) :
  (forall q σ, R q σ -> (q' <- step q; inf {σ' | R q' σ'}, impl σ') [= impl σ) ->
  forall q σ, R q σ -> forever step q [= impl σ.
Proof.
  intros H.
  assert (Hk : @ref (PProd.Pccd (fun _ : Q => t E A))
                (forever step) (fun q => inf {σ | R q σ}, impl σ)).
  { apply lfp_least. intros q. apply finf_glb. intros σ Hσ. apply H. exact Hσ. }
  intros q σ Hσ. etransitivity; [ apply Hk | ].
  apply (finf_lb σ). exact Hσ.
Qed.

(** **** Exercise: 3 stars, standard (echo)

    An echo server, which has a single state, is a reliable channel.
    Use [forever_ref].  The implementation has to keep track of where
    it is in its loop: either at the beginning, or about to output
    [v].  So take [impl] to be [echo_at] below, and relate [Ready] to
    [None] and [Pending v] to [Some v].

    Hint: on the side of the specification, use [bind_bind_ret].  On
    the side of the implementation, unfold [forever] once, then use
    [reassoc]. *)

Definition echo {A} : t io_sig A :=
  forever (fun _ : unit => v <- int input; int (output v)) tt.

Definition echo_at {A} (o : option val) : t io_sig A :=
  match o with
    | None => echo
    | Some v => _ <- int (output v); echo
  end.

Example echo_reliable {A} :
  reliable (A := A) Ready [= echo.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Running two processes in parallel *)

(** The implementation consists of two processes, each described by a
    step function.  They share a state of type [C], which will be the
    state of the network: a step [f : X -> C -> t E (X * C)] starts
    from a local state of type [X] and a shared state, and returns the
    new values of both.  The combinator [interleave f g] runs the two
    processes forever, in rounds: at each round the first process
    takes a step, then the second one. *)

Definition both {E X Y C} (f : X -> C -> t E (X * C)) (g : Y -> C -> t E (Y * C))
  (σ : X * Y * C) : t E (X * Y * C) :=
  let '(x, y, c) := σ in
  '(x', c) <- f x c;
  '(y', c) <- g y c;
  ret (x', y', c).

Definition interleave {E X Y C A} (f : X -> C -> t E (X * C)) (g : Y -> C -> t E (Y * C)) :
  X * Y * C -> t E A :=
  forever (both f g).


(* ################################################################# *)
(** * The network *)

(** The sender and the receiver communicate through two channels: the
    data channel carries packets [(n, v)] made of a sequence number and
    a message, and the acknowledgment channel carries sequence numbers
    back to the sender.  These are the operations on the channels: *)

Inductive chan_op : Type -> Type :=
  | send_data (n : nat) (v : val) : chan_op unit
  | recv_data : chan_op (option (nat * val))
  | send_ack (n : nat) : chan_op unit
  | recv_ack : chan_op (option nat).

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
      (inf {o : option P | b <> 0 /\ (o = None \/ exists q, o = Some q /\ In q h)},
       ret (o, b - 1))
  end.

Record chan_state :=
  mk_chan {
    dchan : list (nat * val);
    achan : list nat;
    budget : nat;
  }.

Definition L_chan {E} : forall ar, chan_op ar -> chan_state -> t E (ar * chan_state) :=
  fun _ m '(mk_chan dc ac b) =>
    match m with
      | send_data n v => ret (tt, mk_chan ((n, v) :: dc) ac b)
      | recv_data => p <- rx dc b; ret (fst p, mk_chan dc ac (snd p))
      | send_ack n => ret (tt, mk_chan dc (n :: ac) b)
      | recv_ack => p <- rx ac b; ret (fst p, mk_chan dc ac (snd p))
    end.

(** The network has no visible behavior of its own, so its operations
    are not events.  A process uses the network by calling [L_chan]
    directly, passing the state of the channels along: [net m c]
    performs the operation [m] on the channels [c], and returns the
    answer together with the new state of the channels.

    (With [models/ISpecCoTree.v] one would instead write the processes
    with network events, and substitute [L_chan] for them afterwards.
    In [models/IntSpec.v] the law relating substitution and [bind] is
    still open, so we take this more direct route.) *)

Abbreviation net m c := (L_chan (E := io_sig) _ m c).

(** **** Exercise: 2 stars, standard (rx_ref)

    The following lemma lists the possible outcomes of a channel.  It
    is the only fact about [rx] we will use afterwards: [y] is below
    [rx h b >>= f] if it is below all the possible continuations.

    Hint: use [bind_meet].  [bind_inf] also applies to
    [inf {o | P o}, ...] once [finf] is unfolded. *)

Definition rx_ok {P} (h : list P) (b : nat) (o : option P) (b' : nat) : Prop :=
  (o = hd_error h /\ b' = b) \/
  (b <> 0 /\ b' = b - 1 /\ (o = None \/ exists q, o = Some q /\ In q h)).

Lemma rx_ref {E P B} (h : list P) (b : nat) (y : t E B) (f : option P * nat -> t E B) :
  (forall o b', rx_ok h b o b' -> y [= f (o, b')) ->
  y [= rx h b >>= f.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * The protocol *)

(** The sender is either idle, in which case it asks the sending
    application for the next message, or busy transmitting a message
    [v] with sequence number [s].  At each step a busy sender
    transmits its packet and looks for an acknowledgment.  It becomes
    idle when the receiver acknowledges, by asking for [S s], that it
    has received the message. *)

Definition sender_state : Type := nat * option val.

Definition sender_step (x : sender_state) (c : chan_state) :
  t io_sig (sender_state * chan_state) :=
  match x with
    | (s, None) =>
      v <- int input;
      ret ((s, Some v), c)
    | (s, Some v) =>
      '(_, c) <- net (send_data s v) c;
      '(a, c) <- net recv_ack c;
      ret (match a with
             | Some n => if Nat.eqb n (S s) then (S s, None) else (s, Some v)
             | None => (s, Some v)
           end, c)
  end.

(** The receiver's state is the sequence number [e] it expects next.
    At each step it takes a packet from the data channel.  If the
    packet carries [e], the message is passed on to the receiving
    application.  In any case the receiver acknowledges by sending
    back the number it now expects. *)

Definition receiver_step (e : nat) (c : chan_state) : t io_sig (nat * chan_state) :=
  '(p, c) <- net recv_data c;
  match p with
    | None => ret (e, c)
    | Some (n, w) =>
      if Nat.eqb n e then
        _ <- int (output w);
        '(_, c) <- net (send_ack (S e)) c;
        ret (S e, c)
      else
        '(_, c) <- net (send_ack e) c;
        ret (e, c)
  end.

(** A _configuration_ of the system consists of the states of the two
    processes and of the network.  The behavior of a configuration is
    that of the two processes interleaved. *)

Definition config : Type := sender_state * nat * chan_state.

Definition impl (σ : config) : t io_sig False :=
  interleave sender_step receiver_step σ.

(** The goal of this chapter is to prove that the initial
    configuration, in which both sequence numbers are [0] and nothing
    has been sent yet, implements a reliable channel, whatever the
    budget [b] of the network:

      [reliable Ready [= impl ((0, None), 0, mk_chan nil nil b)]. *)


(* ################################################################# *)
(** * Symbolic execution *)

(** The behavior of a configuration is one round, followed by the
    behavior of the resulting configuration. *)

Lemma impl_unfold σ :
  impl σ = (σ' <- both sender_step receiver_step σ; impl σ').
Proof.
  apply forever_unfold.
Qed.

(** We will reason about the behavior of a round by _symbolic
    execution_: the following tactic executes the first operation of
    the round, on goals of the form [y [= P >>= K].  It stops when the
    next step depends on a value which is not known, typically the
    outcome of a channel. *)

Ltac run :=
  match goal with
    | |- _ [= bind _ (bind _ _) =>
      apply reassoc
    | |- _ [= bind _ (ret _) =>
      rewrite bind_ret_r; cbn beta iota delta [fst snd]
    | |- _ [= bind _ (L_chan _ _ _) =>
      cbn beta iota delta [L_chan]
    | |- _ [= bind _ (rx _ _) =>
      apply rx_ref;
      let o := fresh "o" in let b := fresh "b" in let Hok := fresh "Hok" in
      intros o b Hok; cbn beta iota delta [fst snd]
    | |- bind _ (int ?m) [= bind _ (int ?m) =>
      apply bind_mono; let v := fresh "v" in intros v; cbn beta iota delta [fst snd]
  end.

(** Note that when [run] meets a channel operation, it introduces the
    outcome [o], the new budget [b], and the hypothesis [Hok] which
    describes the possible outcomes.  When it meets an event, the goal
    must have the form [int m >>= k [= int m >>= k'], and [run] moves
    on to the continuations. *)


(* ################################################################# *)
(** * Invariants *)

(** We now describe which configurations correspond to each state of
    the specification.  When the specification is [Ready], either the
    sender is idle, or the receiver has already output the sender's
    current message but the sender has not yet received the
    acknowledgment.  When the specification is [Pending v], the sender
    is transmitting [v] and the receiver has not output it yet.  In
    each case, the invariant also bounds the sequence numbers found in
    the channels.  In particular, while [v] is pending, every packet
    with the sequence number [s] carries [v]: this is why the receiver
    never outputs a wrong message. *)

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
  good ((0, None), 0, mk_chan nil nil b) Ready.
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

(** The implementation of a state [q] of the specification is the
    demonic choice of all the configurations corresponding to [q]. *)

Definition impls (q : spec_state) : t io_sig False :=
  inf {σ | good σ q}, impl σ.

(** **** Exercise: 1 star, standard (impls_lb) *)

Lemma impls_lb q σ :
  good σ q -> impls q [= impl σ.
Proof.
  (* FILL IN HERE *) Admitted.
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
    a round, use [impls_lb] if the expected event has happened, and
    the induction hypothesis otherwise.  The tactic [bounds] proves
    the [Forall] conditions. *)

(** **** Exercise: 4 stars, standard (progress_ready)

    From a configuration corresponding to [Ready], the system
    eventually reads a message [v] and reaches a configuration
    corresponding to [Pending v]. *)

Lemma progress_ready σ :
  good σ Ready ->
  (v <- int input; impls (Pending v)) [= impl σ.
Proof.
  set (y := (v <- int input; impls (Pending v))).
  assert (H : forall m σ, measure σ < m -> good σ Ready -> y [= impl σ).
  2: { intros Hσ. eapply H; eauto. }
  induction m as [ | m IHm]; intros σ' Hm Hσ; [ lia | ].
  (* FILL IN HERE *) Admitted.
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
  (_ <- int (output v); impls Ready) [= impl σ.
Proof.
  set (y := (_ <- int (output v); impls Ready)).
  assert (H : forall m σ, measure σ < m -> good σ (Pending v) -> y [= impl σ).
  2: { intros Hσ. eapply H; eauto. }
  induction m as [ | m IHm]; intros σ' Hm Hσ; [ lia | ].
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * Correctness *)

(** **** Exercise: 2 stars, standard (stenning_correct)

    Stenning's protocol, running on a network which misbehaves finitely
    often, implements a reliable channel.

    Hint: use [forever_ref] with the relation [fun q σ => good σ q].
    The demonic choice it introduces is exactly [impls q'].  Rewrite
    the step of the specification with [bind_bind_ret], then use
    [progress_ready] and [progress_pending]. *)

Theorem stenning_correct b :
  reliable Ready [= impl ((0, None), 0, mk_chan nil nil b).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * Further exercises *)

(** **** Exercise: 2 stars, standard, optional (why_inf)

    In [forever_ref], why does the continuation of each step have to
    be a demonic choice of configurations?  Find a step of
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

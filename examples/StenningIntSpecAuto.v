(** * StenningIntSpecAuto: Stenning's protocol with [ISpecTactics]

  The verification of [StenningIntSpecSolutions], redone with the
  symbolic execution tactics of [models/ISpecTactics.v].  The
  definitions are the same and the prose is left out; compare the
  proofs of [progress_ready] and [progress_pending]. *)

From Stdlib Require Import List PeanoNat Lia.
Require Import models.IntSpec models.ISpecTactics.

Import ISpec.

Parameter val : Type.

Notation "x >>= f" := (bind f x)
  (at level 40, left associativity).

Notation "v <- x ; M" := (x >>= fun v => M)
  (at level 65, right associativity).

Notation "' p <- x ; M" := (x >>= fun p => M)
  (at level 65, p pattern at level 0, right associativity, only parsing).


(** ** Specification *)

Inductive io_sig : esig :=
  | input : io_sig val
  | output (v : val) : io_sig unit.

Inductive spec_state :=
  | Ready
  | Pending (v : val).

Definition spec_step (q : spec_state) : t io_sig spec_state :=
  match q with
    | Ready => v <- int input; ret (Pending v)
    | Pending v => _ <- int (output v); ret Ready
  end.

Definition reliable {A} : spec_state -> t io_sig A :=
  forever spec_step.


(** ** Two processes in parallel *)

Definition both {E X Y C} (f : X -> C -> t E (X * C)) (g : Y -> C -> t E (Y * C))
  (σ : X * Y * C) : t E (X * Y * C) :=
  let '(x, y, c) := σ in
  '(x', c) <- f x c;
  '(y', c) <- g y c;
  ret (x', y', c).

Definition interleave {E X Y C A} (f : X -> C -> t E (X * C)) (g : Y -> C -> t E (Y * C)) :
  X * Y * C -> t E A :=
  forever (both f g).


(** ** The network *)

Inductive chan_op : Type -> Type :=
  | send_data (n : nat) (v : val) : chan_op unit
  | recv_data : chan_op (option (nat * val))
  | send_ack (n : nat) : chan_op unit
  | recv_ack : chan_op (option nat).

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

Abbreviation net m c := (L_chan (E := io_sig) _ m c).

(** The specification of a channel operation, in the form [istep]
    uses: the possible outcomes, chosen by the network.  An inductive
    type gives one case per behavior of the network. *)

Inductive rx_out {P} (b : nat) : list P -> option P -> nat -> Prop :=
  | rx_empty : rx_out b nil None b
  | rx_first p h : rx_out b (p :: h) (Some p) b
  | rx_lost h : b <> 0 -> rx_out b h None (b - 1)
  | rx_replay q h : b <> 0 -> In q h -> rx_out b h (Some q) (b - 1).

Global Instance rx_silent {E P} (h : list P) (b : nat) :
  Silent (E := E) (rx h b) (fun p => rx_out b h (fst p) (snd p)).
Proof.
  red. destruct h as [ | p h]; cbn.
  - apply (finf_lb (None, b)). constructor.
  - apply meet_glb.
    + apply (finf_lb (Some p, b)). constructor.
    + apply finf_glb. intros o [Hb Ho]. apply (finf_lb (o, b - 1)). cbn.
      destruct Ho as [-> | (q & -> & Hq)]; constructor; auto.
Qed.


(** ** The protocol *)

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

Definition config : Type := sender_state * nat * chan_state.

Definition impl (σ : config) : t io_sig False :=
  interleave sender_step receiver_step σ.

Lemma impl_unfold σ :
  impl σ = (σ' <- both sender_step receiver_step σ; impl σ').
Proof.
  apply forever_unfold.
Qed.

(** One round is unfolded on demand by [istep]. *)

Global Hint Unfold both sender_step receiver_step L_chan : ispec.


(** ** Invariants *)

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

Definition impls (q : spec_state) : t io_sig False :=
  inf {σ | good σ q}, impl σ.

Lemma impls_lb q σ :
  good σ q -> impls q [= impl σ.
Proof.
  intros H. apply (finf_lb σ). exact H.
Qed.

Definition measure (σ : config) : nat :=
  budget (snd σ) + (snd (fst σ) - fst (fst (fst σ))).


(** ** Domain tactics *)

(** [facts] turns what the context knows about the channels into
    arithmetic: it splits the [Forall] invariants and uses them on
    the packets the network delivered.  It plays the role of Floyd's
    [entailer] for the hypotheses. *)

Ltac facts :=
  repeat match goal with
         | H : Forall _ nil |- _ => clear H
         | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
         | H : In _ nil |- _ => destruct H
         | H : In _ (_ :: _) |- _ => destruct H as [H | H]
         | Hf : Forall ?P ?l, Hi : In ?q ?l |- _ =>
           apply (proj1 (Forall_forall P l) Hf) in Hi
         | H : _ \/ _ |- _ => destruct H as [H | H]
         | H : (_, _) = (_, _) |- _ => injection H as; subst
         | H : ?x = _ |- _ => is_var x; subst x
         | H : _ = ?x |- _ => is_var x; subst x
         end;
  cbn [fst snd] in *.

(** An outcome of the network. *)

Ltac outcome H :=
  inversion H; subst; clear H; facts.

(** The [Forall] conditions of a new configuration. *)

Ltac bounds :=
  repeat (apply Forall_cons; [ cbn; first [ lia | left; cbn; lia | right; reflexivity ] | ]);
  try apply Forall_nil;
  try first
    [ eassumption
    | eapply Forall_impl; [ | eassumption ];
       intros ? Hp; cbn in Hp |- *;
       first [ lia | left; lia | destruct Hp as [Hp | ->]; cbn; lia ] ].

(** The end of a round: either the expected event has happened, or we
    are back to a configuration of the same kind with a smaller
    measure. *)

Ltac close IH :=
  first
    [ apply impls_lb; constructor; bounds
    | apply IH; [ unfold measure; cbn [fst snd budget]; lia | constructor; bounds ] ].

(** One round, as far as it goes: run, take the network's outcomes
    and the branches of the protocol, and close. *)

Ltac round IH :=
  repeat first
    [ progress irun
    | match goal with H : rx_out _ _ _ _ |- _ => outcome H end
    | icase; facts ];
  try close IH.


(** ** Progress *)

Lemma progress_ready σ :
  good σ Ready ->
  (v <- int input; impls (Pending v)) [= impl σ.
Proof.
  imeasure measure σ IH. intros Hσ.
  inversion Hσ; subst; clear Hσ; rewrite impl_unfold; round IH.
Qed.

Lemma progress_pending v σ :
  good σ (Pending v) ->
  (_ <- int (output v); impls Ready) [= impl σ.
Proof.
  imeasure measure σ IH. intros Hσ.
  inversion Hσ; subst; clear Hσ; rewrite impl_unfold; round IH.
Qed.


(** ** Correctness *)

Theorem stenning_correct b :
  reliable Ready [= impl ((0, None), 0, mk_chan nil nil b).
Proof.
  unfold reliable.
  iloop (fun q σ => good σ q) impl; [ | apply good_init ].
  destruct q as [ | v]; cbn [spec_step]; istep.
  - apply progress_ready. exact Hinv.
  - apply progress_pending. exact Hinv.
Qed.

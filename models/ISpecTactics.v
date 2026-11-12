(** * ISpecTactics: symbolic execution for interaction specifications

  Refinement proofs [y [= x] between a specification [y] and an
  implementation [x] mostly consist of walking down both sides one
  operation at a time.  This file automates that walk, in the spirit
  of VST's Floyd.

    - [istep] performs one step: it decomposes a choice that needs no
      decision, re-associates a sequence, runs a [ret], matches two
      identical events, or uses the specification of a silent
      operation.  [irun] repeats it until something needs a decision.
    - [ichoose w], [ileft] and [iright] make the decisions that
      [istep] won't: resolving a demonic choice of the specification,
      or an angelic choice of the implementation.
    - [icase] does case analysis on the [match] or [if] which blocks
      the implementation.
    - [Silent x P] is the analogue of a function specification: [x]
      performs no event and returns some [a] with [P a], chosen by the
      adversary.  Register instances for the operations of a model
      and [istep] will use them.  Definitions that should simply be
      unfolded go in the hint database [ispec] with [Hint Unfold].
    - [iloop R impl] applies the loop rule [forever_ref], and
      [imeasure f x IH] sets up induction on a measure, to show that
      silent work eventually ends.

  Floyd never has to worry about associativity.  Here [bind_bind]
  needs a classical assumption, so sequences are re-associated in one
  direction only: towards the right, which is always sound on the
  side of the implementation ([bind_bind_le]).  On the side of the
  specification the tactics only use [bind_bind_ret], which holds in
  both directions.  Every rule below is stated for one side of [[=],
  and is used with [apply], never [rewrite]. *)

From Stdlib Require Import FunctionalExtensionality PeanoNat Lia.
Require Import models.IntSpec.

Import ISpec.


(** ** Laws *)

Section LAWS.
  Context {E : esig}.

  Lemma bind_sup {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (sup i, k i) = sup i, bind f (k i).
  Proof. apply (Sup.mor (f := bind f)). Qed.

  Lemma bind_inf {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (inf i, k i) = inf i, bind f (k i).
  Proof. apply (Inf.mor (f := bind f)). Qed.

  Lemma bind_fsup {A B I} (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) :
    bind f (fsup P k) = fsup P (fun i => bind f (k i)).
  Proof. apply (Sup.mor_fsup (bind f)). Qed.

  Lemma bind_finf {A B I} (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) :
    bind f (finf P k) = finf P (fun i => bind f (k i)).
  Proof. apply (Inf.mor_finf (bind f)). Qed.

  Lemma bind_join {A B} (f : A -> t E B) (x y : t E A) :
    bind f (x || y) = bind f x || bind f y.
  Proof. apply (Sup.mor_join (bind f)). Qed.

  Lemma bind_bot {A B} (f : A -> t E B) :
    bind f bot = bot.
  Proof. apply (Sup.mor_bot (bind f)). Qed.

  Section MEET.
    Local Transparent meet.

    Lemma bind_meet {A B} (f : A -> t E B) (x y : t E A) :
      bind f (x && y) = bind f x && bind f y.
    Proof.
      unfold meet. rewrite bind_inf. f_equal.
      apply functional_extensionality. intros [ | ]; reflexivity.
    Qed.
  End MEET.

  Lemma bind_ref {A B} (f : A -> t E B) (x y : t E A) :
    x [= y -> bind f x [= bind f y.
  Proof. apply pmor. Qed.

  Lemma meet_l {L : ccdlattice} (x y z : L) : x [= z -> x && y [= z.
  Proof. intros H. etransitivity; eauto using meet_lb_l. Qed.

  Lemma meet_r {L : ccdlattice} (x y z : L) : y [= z -> x && y [= z.
  Proof. intros H. etransitivity; eauto using meet_lb_r. Qed.

  (** [fsup_at] and [finf_at] with the side condition last. *)

  Lemma fsup_at' {L : ccdlattice} {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    x [= y i -> P i -> x [= fsup P y.
  Proof. intros. eapply fsup_at; eauto. Qed.

  Lemma finf_at' {L : ccdlattice} {I} (i : I) (P : I -> Prop) (x : I -> L) (y : L) :
    x i [= y -> P i -> finf P x [= y.
  Proof. intros. eapply finf_at; eauto. Qed.
End LAWS.


(** ** Silent operations *)

(** [Silent x P] says that [x] is at least as good as returning,
    without any event, a value [a] such that [P a], picked by the
    adversary.  It is all [istep] needs to know about [x]. *)

Class Silent {E A} (x : t E A) (P : A -> Prop) : Prop :=
  silent : finf P (@ret E A) [= x.

Lemma silent_weaken {E A} (x : t E A) (P Q : A -> Prop) :
  Silent x P -> (forall a, P a -> Q a) -> Silent x Q.
Proof.
  intros Hx HPQ. red. etransitivity; [ | apply Hx ].
  apply finf_glb. intros a Ha. apply finf_lb. auto.
Qed.


(** ** Rules for the implementation side *)

Section IMPL.
  Context {E : esig}.

  Lemma r_reassoc {A B C} (y : t E C) (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    y [= bind (fun a => bind g (f a)) x ->
    y [= bind g (bind f x).
  Proof. intros H. etransitivity; [ exact H | apply bind_bind_le ]. Qed.

  Lemma r_ret {A B} (y : t E B) (f : A -> t E B) (a : A) :
    y [= f a -> y [= bind f (ret a).
  Proof. rewrite bind_ret_r. auto. Qed.

  Lemma r_bind_ret {A} (y x : t E A) :
    y [= x -> y [= bind ret x.
  Proof. rewrite bind_ret_l. auto. Qed.

  Lemma r_inf {A B I} (y : t E B) (f : A -> t E B) (k : I -> t E A) :
    (forall i, y [= bind f (k i)) -> y [= bind f (linf k).
  Proof. intros H. rewrite bind_inf. apply inf_glb. auto. Qed.

  Lemma r_finf {A B I} (y : t E B) (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) :
    (forall i, P i -> y [= bind f (k i)) -> y [= bind f (finf P k).
  Proof. intros H. rewrite bind_finf. apply finf_glb. auto. Qed.

  Lemma r_meet {A B} (y : t E B) (f : A -> t E B) (a b : t E A) :
    y [= bind f a -> y [= bind f b -> y [= bind f (a && b).
  Proof. intros. rewrite bind_meet. apply meet_glb; auto. Qed.

  Lemma r_sup {A B I} (y : t E B) (f : A -> t E B) (k : I -> t E A) :
    y [= (sup i, bind f (k i)) -> y [= bind f (lsup k).
  Proof. rewrite bind_sup. auto. Qed.

  Lemma r_fsup {A B I} (y : t E B) (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) :
    y [= fsup P (fun i => bind f (k i)) -> y [= bind f (fsup P k).
  Proof. rewrite bind_fsup. auto. Qed.

  Lemma r_join {A B} (y : t E B) (f : A -> t E B) (a b : t E A) :
    y [= bind f a || bind f b -> y [= bind f (a || b).
  Proof. rewrite bind_join. auto. Qed.

  Lemma r_bot {A B} (y : t E B) (f : A -> t E B) :
    y [= bot -> y [= bind f bot.
  Proof. rewrite bind_bot. auto. Qed.

  Lemma r_silent {A B} (x : t E A) (P : A -> Prop) `{!Silent x P}
        (y : t E B) (f : A -> t E B) :
    (forall a, P a -> y [= f a) -> y [= bind f x.
  Proof.
    intros H. etransitivity; [ | apply bind_ref, silent ].
    rewrite bind_finf. apply finf_glb. intros a Ha.
    rewrite bind_ret_r. auto.
  Qed.

  Lemma r_silent_ret {A} (x : t E A) (P : A -> Prop) `{!Silent x P} (y : t E A) :
    (forall a, P a -> y [= ret a) -> y [= x.
  Proof.
    intros H. rewrite <- (bind_ret_l x). apply (r_silent x P). exact H.
  Qed.
End IMPL.


(** ** Rules for the specification side *)

Section SPEC.
  Context {E : esig}.

  Lemma l_ret {A B} (f : A -> t E B) (a : A) (x : t E B) :
    f a [= x -> bind f (ret a) [= x.
  Proof. rewrite bind_ret_r. auto. Qed.

  Lemma l_bind_ret {A} (x y : t E A) :
    x [= y -> bind ret x [= y.
  Proof. rewrite bind_ret_l. auto. Qed.

  Lemma l_map {A B C} (g : B -> t E C) (h : A -> B) (x : t E A) (z : t E C) :
    bind (fun a => g (h a)) x [= z ->
    bind g (bind (fun a => ret (h a)) x) [= z.
  Proof. rewrite bind_bind_ret. auto. Qed.

  Lemma l_sup {A B I} (f : A -> t E B) (k : I -> t E A) (x : t E B) :
    (forall i, bind f (k i) [= x) -> bind f (lsup k) [= x.
  Proof. intros H. rewrite bind_sup. apply sup_lub. auto. Qed.

  Lemma l_fsup {A B I} (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) (x : t E B) :
    (forall i, P i -> bind f (k i) [= x) -> bind f (fsup P k) [= x.
  Proof. intros H. rewrite bind_fsup. apply fsup_lub. auto. Qed.

  Lemma l_join {A B} (f : A -> t E B) (a b : t E A) (x : t E B) :
    bind f a [= x -> bind f b [= x -> bind f (a || b) [= x.
  Proof. intros. rewrite bind_join. apply join_lub; auto. Qed.

  Lemma l_bot {A B} (f : A -> t E B) (x : t E B) :
    bind f bot [= x.
  Proof. rewrite bind_bot. apply bot_lb. Qed.

  Lemma l_inf {A B I} (f : A -> t E B) (k : I -> t E A) (x : t E B) :
    (inf i, bind f (k i)) [= x -> bind f (linf k) [= x.
  Proof. rewrite bind_inf. auto. Qed.

  Lemma l_finf {A B I} (f : A -> t E B) (P : I -> Prop) (k : I -> t E A) (x : t E B) :
    finf P (fun i => bind f (k i)) [= x -> bind f (finf P k) [= x.
  Proof. rewrite bind_finf. auto. Qed.

  Lemma l_meet {A B} (f : A -> t E B) (a b : t E A) (x : t E B) :
    bind f a && bind f b [= x -> bind f (a && b) [= x.
  Proof. rewrite bind_meet. auto. Qed.
End SPEC.


(** ** Events *)

Section EVENTS.
  Context {E : esig}.

  Lemma ret_ref {A} (a b : A) :
    a = b -> ret (E := E) a [= ret b.
  Proof. intros ->. reflexivity. Qed.

  Lemma int_r {A} (m : E A) (k : A -> t E A) :
    (forall n, ret n [= k n) -> int m [= bind k (int m).
  Proof.
    intros H. rewrite <- (bind_ret_l (int m)) at 1. apply bind_mono. exact H.
  Qed.

  Lemma int_l {A} (m : E A) (k : A -> t E A) :
    (forall n, k n [= ret n) -> bind k (int m) [= int m.
  Proof.
    intros H. rewrite <- (bind_ret_l (int m)) at 2. apply bind_mono. exact H.
  Qed.
End EVENTS.


(** ** Loops *)

(** [forever step s] runs [step] again and again from the state [s].
    It is the least fixed point of its unfolding, so no coinduction is
    needed. *)

Definition forever_body {E S A} (step : S -> t E S) (k : S -> t E A) : S -> t E A :=
  fun s => bind k (step s).

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
  forever (A := A) step s = bind (forever step) (step s).
Proof.
  unfold forever at 1.
  rewrite <- (lfp_fixed (L := PProd.Pccd (fun _ : S => t E A)) (forever_body step)).
  reflexivity.
Qed.

Lemma r_unroll {E S A} (step : S -> t E S) (s : S) (y : t E A) :
  y [= bind (forever step) (step s) -> y [= forever step s.
Proof. rewrite forever_unfold. auto. Qed.

(** The loop rule, much like a loop invariant: if every [impl σ]
    performs one step of the specification from [q] to some [q'], and
    then behaves as any of the [impl σ'] related to [q'], then [impl]
    implements [forever step]. *)

Lemma forever_ref {E Q S A} (step : Q -> t E Q) (R : Q -> S -> Prop) (impl : S -> t E A) :
  (forall q σ, R q σ -> bind (fun q' => finf (R q') impl) (step q) [= impl σ) ->
  forall q σ, R q σ -> forever step q [= impl σ.
Proof.
  intros H.
  assert (Hk : @ref (PProd.Pccd (fun _ : Q => t E A))
                (forever step) (fun q => finf (R q) impl)).
  { apply lfp_least. intros q. apply finf_glb. intros σ Hσ. apply H. exact Hσ. }
  intros q σ Hσ. etransitivity; [ apply Hk | ].
  apply (finf_lb σ). exact Hσ.
Qed.

(** Induction on a measure, for the silent work that the fairness of
    the environment bounds. *)

Lemma measure_ind {X} (f : X -> nat) (P : X -> Prop) :
  (forall x, (forall y, f y < f x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros H.
  assert (Hn : forall n x, f x < n -> P x).
  { induction n as [ | n IHn]; intros x Hx; [ lia | ].
    apply H. intros y Hy. apply IHn. lia. }
  intros x. apply (Hn (S (f x))). lia.
Qed.


(** ** Tactics *)

Create HintDb ispec discriminated.

(** Clean up after a step: contract the beta-redexes which the rules
    leave behind, and reduce [match]es on known constructors. *)

Ltac ispec_simpl :=
  cbn beta iota delta [fst snd].

(** Introduce the result of a step.  It is named after the binder of
    the continuation [k] when there is one, and split if it is a
    pair, so that [let '(x, y) := p in ...] reduces. *)

Ltac ispec_split a :=
  lazymatch type of a with
  | prod _ _ =>
    let a1 := fresh "v" in let a2 := fresh "v" in
    destruct a as [a1 a2]; ispec_split a1; ispec_split a2
  | _ => idtac
  end.

Ltac ispec_intro_for k :=
  let a :=
    lazymatch k with
    | fun x => _ => fresh x
    | _ => fresh "v"
    end in
  intro a; ispec_split a.

Ltac ispec_post H :=
  cbn beta iota delta [fst snd] in H.

(** The search for a [Silent] instance.  It fails if there is none. *)

Ltac ispec_silent x k :=
  let Hs := fresh "Hs" in
  eassert (Hs : Silent x _); [ typeclasses eauto | ];
  apply (r_silent x _ (Silent0 := Hs)); clear Hs;
  ispec_intro_for k;
  let Hok := fresh "Hok" in intro Hok; ispec_post Hok.

Ltac ispec_step :=
  match goal with
  (* done *)
  | |- ?x [= ?x => reflexivity
  | |- bot [= _ => apply bot_lb
  | |- _ [= top => apply top_ub
  | |- ret _ [= ret _ =>
    apply ret_ref; try solve [ reflexivity | lia | congruence ]

  (* choices that need no decision *)
  | |- lsup ?k [= _ => apply sup_lub; ispec_intro_for k; ispec_simpl
  | |- fsup _ ?k [= _ => apply fsup_lub; ispec_intro_for k; intro; ispec_simpl
  | |- _ || _ [= _ => apply join_lub
  | |- _ [= linf ?k => apply inf_glb; ispec_intro_for k; ispec_simpl
  | |- _ [= finf _ ?k => apply finf_glb; ispec_intro_for k; intro; ispec_simpl
  | |- _ [= _ && _ => apply meet_glb

  (* the implementation *)
  | |- _ [= bind _ (bind _ _) => apply r_reassoc
  | |- _ [= bind ret _ => apply r_bind_ret
  | |- _ [= bind _ (ret _) => apply r_ret; ispec_simpl
  | |- _ [= bind _ bot => apply r_bot
  | |- _ [= bind _ (linf ?k) => apply r_inf; ispec_intro_for k; ispec_simpl
  | |- _ [= bind _ (finf _ ?k) => apply r_finf; ispec_intro_for k; intro; ispec_simpl
  | |- _ [= bind _ (_ && _) => apply r_meet; ispec_simpl
  | |- _ [= bind _ (lsup _) => apply r_sup; ispec_simpl
  | |- _ [= bind _ (fsup _ _) => apply r_fsup; ispec_simpl
  | |- _ [= bind _ (_ || _) => apply r_join; ispec_simpl
  | |- _ [= bind ?k ?x => ispec_silent x k; ispec_simpl

  (* the specification *)
  | |- bind ret _ [= _ => apply l_bind_ret
  | |- bind _ (ret _) [= _ => apply l_ret; ispec_simpl
  | |- bind _ (bind (fun a => ret (@?h a)) _) [= _ => apply (l_map _ h); ispec_simpl
  | |- bind _ bot [= _ => apply l_bot
  | |- bind _ (lsup ?k) [= _ => apply l_sup; ispec_intro_for k; ispec_simpl
  | |- bind _ (fsup _ ?k) [= _ => apply l_fsup; ispec_intro_for k; intro; ispec_simpl
  | |- bind _ (_ || _) [= _ => apply l_join; ispec_simpl
  | |- bind _ (linf _) [= _ => apply l_inf; ispec_simpl
  | |- bind _ (finf _ _) [= _ => apply l_finf; ispec_simpl
  | |- bind _ (_ && _) [= _ => apply l_meet; ispec_simpl

  (* events *)
  | |- bind ?k (int ?m) [= bind _ (int ?m) =>
    apply bind_mono; ispec_intro_for k; ispec_simpl
  | |- int ?m [= bind ?k (int ?m) => apply int_r; ispec_intro_for k; ispec_simpl
  | |- bind ?k (int ?m) [= int ?m => apply int_l; ispec_intro_for k; ispec_simpl

  (* a silent operation on its own *)
  | |- _ [= ?x =>
    let Hs := fresh "Hs" in
    eassert (Hs : Silent x _); [ typeclasses eauto | ];
    apply (r_silent_ret x _ (Silent0 := Hs)); clear Hs;
    let a := fresh "v" in let Hok := fresh "Hok" in
    intros a Hok; ispec_post Hok; ispec_simpl

  (* definitions registered for unfolding *)
  | |- _ => progress autounfold with ispec; ispec_simpl

  (* a [match] that has become reducible *)
  | |- _ => progress ispec_simpl
  end.

Ltac istep := ispec_step.
Ltac irun := repeat ispec_step.

(** Decisions.  [ichoose w] resolves a demonic choice of the
    specification, or an angelic choice of the implementation, with
    the witness [w].  A restricted choice leaves the side condition
    as a second goal.  [ileft] and [iright] do the same for the binary
    choices. *)

Ltac ichoose_with w :=
  lazymatch goal with
  | |- linf _ [= _ => apply (inf_at w)
  | |- finf _ _ [= _ => apply (finf_at' w)
  | |- _ [= lsup _ => apply (sup_at w)
  | |- _ [= fsup _ _ => apply (fsup_at' w)
  | |- _ => fail "ichoose: no choice to make"
  end; ispec_simpl.

Tactic Notation "ichoose" constr(w) := ichoose_with w.
Tactic Notation "ichoose" := ichoose_with open_constr:(_).

Ltac ileft :=
  lazymatch goal with
  | |- _ && _ [= _ => apply meet_l
  | |- _ [= _ || _ => apply join_l
  | |- _ => fail "ileft: no binary choice to make"
  end.

Ltac iright :=
  lazymatch goal with
  | |- _ && _ [= _ => apply meet_r
  | |- _ [= _ || _ => apply join_r
  | |- _ => fail "iright: no binary choice to make"
  end.

(** Case analysis on what blocks the implementation.  [icase] looks
    for the first [match] in the operation the implementation is about
    to run, or failing that anywhere in the implementation, and
    destructs its scrutinee.  Comparisons of natural numbers are
    destructed with [Nat.eqb_spec], and branches that contradict the
    arithmetic in the context are discarded. *)

Ltac ispec_head x :=
  lazymatch x with
  | bind _ ?y => ispec_head y
  | _ => x
  end.

Ltac ispec_destruct e :=
  lazymatch e with
  | Nat.eqb ?a ?b => destruct (Nat.eqb_spec a b)
  | _ => first [ is_var e; destruct e | destruct e eqn:? ]
  end;
  ispec_simpl;
  try (exfalso; lia).

Ltac icase :=
  lazymatch goal with
  | |- _ [= ?x =>
    let h := ispec_head x in
    first
      [ match h with
        | context [ match ?e with _ => _ end ] => ispec_destruct e
        end
      | match x with
        | context [ match ?e with _ => _ end ] => ispec_destruct e
        end
      | fail "icase: nothing to destruct" ]
  end.

(** The loop rule.  The first goal is the step obligation, with the
    two states and the invariant introduced; the second is the
    invariant for the initial states. *)

Ltac iloop R impl :=
  lazymatch goal with
  | |- forever ?step _ [= _ =>
    apply (forever_ref step R impl);
    [ let q := fresh "q" in let s := fresh "σ" in let H := fresh "Hinv" in
      intros q s H | ]
  | |- _ => fail "iloop: the specification is not a loop"
  end.

Ltac iunroll :=
  apply r_unroll; ispec_simpl.

Ltac imeasure f x IH :=
  generalize dependent x;
  refine (measure_ind f _ _);
  intros x IH.

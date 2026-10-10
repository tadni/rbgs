(** * A constructive strategy model

  [models.IntSpec] builds the interaction specification monad over
  the free constructively completely distributive lattice [FCD.F].
  That file also shows the limits of the approach: the three laws
  [ISpec.apply_int_r], [ISpec.apply_bind] and [ISpec.apply_assoc]
  stay admitted, [ISpec.bind_bind] holds only relative to
  [codistributive], and [codist_lem] identifies that principle with
  excluded middle.  [fcd_unique] rules out fixing this by presenting
  the free lattice differently, and [IRun] at the end of that file
  shows what does work: drop the demonic [inf], keep a plain
  [Downset.F], and define substitution as a single sup-extension
  over an inductively generated relation on interaction sequences.

  [IRun] pays for this by losing demonic nondeterminism.  This file
  gets it back, by taking the design of [models.IntStrat] -- Chapter
  3 of the thesis -- and building it on the constructive lattice.
  The point is that a strategy is a plain downset of plays:

    [strat i := Downset.F (play_poset i)]

  with no [Upset] and no [FCD] anywhere.  Demonic choice has moved
  out of the lattice and into the *game*: a position is [ready],
  [running] or [suspended], moves are split into opponent moves
  ([oq], [oa]) and player moves ([pq], [pa]), and a strategy must
  account for every opponent move it does not refuse.  The angelic
  [sup] is union; what used to be a demonic [inf] is the branching
  of the play on opponent moves.  And "nothing more happened here"
  is [pnil_suspended q m], a *located* bottom, rather than the
  global [bot] of thesis section 5.3.3 which is what obstructs
  [ISpec.bind_bind].

  The result is that layered composition, its unit laws and its
  associativity all go through with no axioms beyond functional and
  propositional extensionality. *)

Require Import models.IntSpec.
From Stdlib Require Import PropExtensionality.
From Stdlib Require Import Setoid.
From Stdlib Require Import Program.Equality.

(** ** [eq_rect_eq] is a theorem here

  Plays are indexed by positions, so their inversions are dependent
  and we use [dependent destruction].  That tactic appeals to
  [Eqdep.Eq_rect_eq.eq_rect_eq], which [Print Assumptions] duly
  reports.  It is not an extra assumption: propositional
  extensionality gives proof irrelevance, hence uniqueness of
  identity proofs, hence exactly that statement.  We record the
  proof so the audit can be read correctly. *)

Lemma eq_rect_eq_propext (U : Type) (p : U) (Q : U -> Type) (x : Q p)
      (h : p = p) :
  x = eq_rect p Q x p h.
Proof.
  rewrite (proof_irrel _ h (eq_refl p)). reflexivity.
Qed.


(** ** Effect signatures

  As in [models.IntStrat], and unlike [esig] in [models.IntSpec], a
  signature is a type of operations together with an arity for each.
  The two are interchangeable; this form is what the game needs. *)

Record isig :=
  {
    iop :> Type;
    iar : iop -> Type;
  }.

Arguments iar {_}.


(** * Strategies *)

Section STRAT.
  Context {E F : isig}.

  (** ** Positions, moves and plays (Def. 3.1)

    A strategy for [F] in terms of [E] is either waiting for an
    incoming question, running one, or suspended on an outgoing
    question.  The alternation is forced by the typing of [move]. *)

  Variant position :=
    | ready
    | running (q : F)
    | suspended (q : F) (m : E).

  Variant move : position -> position -> Type :=
    | oq (q : F) : move ready (running q)
    | pq {q} (m : E) : move (running q) (suspended q m)
    | oa {q m} (n : iar m) : move (suspended q m) (running q)
    | pa {q} (r : iar q) : move (running q) ready.

  Inductive play : position -> Type :=
    | pnil_ready : play ready
    | pnil_suspended q m : play (suspended q m)
    | pcons {i j} : move i j -> play j -> play i.

  (** The two [pnil] constructors are the located bottoms: a play may
    stop while ready, or stop while suspended on [m] inside [q].
    Nothing identifies the two, which is the whole difference from a
    lattice with a single global [bot]. *)

  Inductive pref : forall {i : position}, play i -> play i -> Prop :=
    | pnil_ready_pref t :
        pref pnil_ready t
    | pnil_suspended_pref {q m} t :
        pref (pnil_suspended q m) t
    | pcons_pref {i j} (e : move i j) s t :
        pref s t -> pref (pcons e s) (pcons e t).

  Lemma pref_refl {i} (s : play i) : pref s s.
  Proof.
    induction s; constructor; auto.
  Qed.

  Lemma pref_trans {i} (s t u : play i) : pref s t -> pref t u -> pref s u.
  Proof.
    intros Hst. revert u.
    induction Hst; intros u Htu; try constructor.
    dependent destruction Htu. constructor. auto.
  Qed.

  Lemma pref_antisym {i} (s t : play i) : pref s t -> pref t s -> s = t.
  Proof.
    intros Hst. induction Hst; intros Hts.
    - dependent destruction Hts. reflexivity.
    - dependent destruction Hts. reflexivity.
    - dependent destruction Hts. f_equal. auto.
  Qed.

  Definition play_poset (i : position) : poset :=
    {|
      poset_carrier := play i;
      ref := @pref i;
      ref_refl := @pref_refl i;
      ref_trans := @pref_trans i;
      ref_antisym := @pref_antisym i;
    |}.

  (** ** Strategies (Def. 3.1)

    And that is the whole lattice: the free *sup*-lattice over the
    poset of plays, which is constructively CCD by [Downset.dccd]. *)

  Definition strat (i : position) : ccdlattice :=
    Downset.F (play_poset i).

  Lemma strat_closed {i} (σ : strat i) (s t : play i) :
    Downset.has σ t -> pref s t -> Downset.has σ s.
  Proof.
    intros Ht Hst. eapply Downset.has_closed; eassumption.
  Qed.

  Lemma strat_eq {i} (σ τ : strat i) :
    (forall s, Downset.has σ s <-> Downset.has τ s) -> σ = τ.
  Proof.
    apply Downset.has_eq.
  Qed.

End STRAT.

Arguments position : clear implicits.
Arguments move _ _ _ _ : clear implicits.
Arguments play _ _ _ : clear implicits.
Arguments play_poset _ _ _ : clear implicits.
Arguments strat _ _ _ : clear implicits.

Notation "E ->> F" := (strat E F ready) (at level 99).

(** ** Building strategies from prefix-closed predicates *)

Definition mkstrat {E F} {i} (P : play E F i -> Prop)
           (H : dcl (C := play_poset E F i) P) : strat E F i :=
  Downset.Build_downset (play_poset E F i) P H.

Lemma has_mkstrat {E F i} P H (s : play E F i) :
  Downset.has (@mkstrat E F i P H) s <-> P s.
Proof.
  reflexivity.
Qed.


(** * Layered composition (Def. 3.4) *)

Section COMPOSE.
  Context {E F G : isig}.

  (** The three strategies run in lockstep, and [cpos] records which
    combinations of their positions can occur.  [cpos_right q m] is
    the interesting one: the outer strategy is suspended on [m]
    inside [q], which is exactly the state in which the inner
    strategy is running [m]. *)

  Variant cpos : position F G -> position E F -> position E G -> Type :=
    | cpos_ready :
        cpos ready ready ready
    | cpos_left (q : G) :
        cpos (running q) ready (running q)
    | cpos_right (q : G) (m : F) :
        cpos (suspended q m) (running m) (running q)
    | cpos_suspended (q : G) (m : F) (u : E) :
        cpos (suspended q m) (suspended m u) (suspended q u).

  Inductive comp_has :
    forall {i j k} (p : cpos i j k),
      play F G i -> play E F j -> play E G k -> Prop :=
    | comp_ready t :
        comp_has cpos_ready pnil_ready t pnil_ready
    | comp_oq q s t w :
        comp_has (cpos_left q) s t w ->
        comp_has cpos_ready (pcons (oq q) s) t (pcons (oq q) w)
    | comp_lq q m s t w :
        comp_has (cpos_right q m) s t w ->
        comp_has (cpos_left q) (pcons (pq m) s) (pcons (oq m) t) w
    | comp_rq q m u s t w :
        comp_has (cpos_suspended q m u) s t w ->
        comp_has (cpos_right q m) s (pcons (pq u) t) (pcons (pq u) w)
    | comp_suspended q m u s :
        comp_has (cpos_suspended q m u) s
                 (pnil_suspended m u) (pnil_suspended q u)
    | comp_oa q m u (v : iar u) s t w :
        comp_has (cpos_right q m) s t w ->
        comp_has (cpos_suspended q m u) s (pcons (oa v) t) (pcons (oa v) w)
    | comp_ra q m (n : iar m) s t w :
        comp_has (cpos_left q) s t w ->
        comp_has (cpos_right q m) (pcons (oa n) s) (pcons (pa n) t) w
    | comp_la q (r : iar q) s t w :
        comp_has cpos_ready s t w ->
        comp_has (cpos_left q) (pcons (pa r) s) t (pcons (pa r) w).

  Hint Constructors comp_has : core.
  Hint Constructors pref : core.

  (** A prefix of an observed interaction comes from prefixes of the
    two components.  This is the analogue of [IRun.runs_down], and
    it is what makes the composite a downset. *)

  Lemma comp_has_pref {i j k} (p : cpos i j k) s t w :
    comp_has p s t w ->
    forall w', pref w' w ->
    exists s' t', pref s' s /\ pref t' t /\ comp_has p s' t' w'.
  Proof.
    induction 1.
    - intros w' Hw'. dependent destruction Hw'.
      eauto using pref_refl.
    - intros w' Hw'. dependent destruction w'; eauto using pref_refl.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - intros w' Hw'. dependent destruction w'; eauto using pref_refl.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - intros w' Hw'. dependent destruction w'; eauto using pref_refl.
      inversion Hw'.
    - intros w' Hw'. dependent destruction w'; eauto using pref_refl.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - intros w' Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
    - intros w' Hw'. dependent destruction w'; eauto using pref_refl.
      dependent destruction Hw'.
      edestruct IHcomp_has as (s' & t' & Hs' & Ht' & Hw''); eauto 10.
  Qed.

  Lemma comp_closed {i j k} (p : cpos i j k)
        (s : strat F G i) (t : strat E F j) :
    dcl (C := play_poset E G k)
        (fun w => exists u v,
                    Downset.has s u /\ Downset.has t v /\ comp_has p u v w).
  Proof.
    intros w' w Hw' (u & v & Hu & Hv & Hw).
    edestruct (comp_has_pref p u v w Hw w' Hw')
      as (u' & v' & Hu' & Hv' & Hw'').
    exists u', v'. split; [ | split ].
    - eapply Downset.has_closed; eassumption.
    - eapply Downset.has_closed; eassumption.
    - assumption.
  Qed.

  Definition compose_when {i j k} (p : cpos i j k)
             (s : strat F G i) (t : strat E F j) : strat E G k :=
    mkstrat _ (comp_closed p s t).

  Lemma has_compose {i j k} (p : cpos i j k) s t w :
    Downset.has (compose_when p s t) w <->
    exists u v, Downset.has s u /\ Downset.has t v /\ comp_has p u v w.
  Proof.
    reflexivity.
  Qed.

  (** Composition is a complete join homomorphism in each argument.
    It is *not* a meet homomorphism, and does not need to be: the
    demonic content of a strategy is the branching of its plays on
    opponent moves, not an [inf] of the lattice. *)

  Global Instance compose_sup_l {i j k} (p : cpos i j k) (t : strat E F j) :
    Sup.Morphism (fun s => compose_when p s t).
  Proof.
    red. intros I x. apply strat_eq. intros w.
    rewrite has_compose, Downset.has_lsup. split.
    - intros (u & v & (n & Hu) & Hv & Hw).
      exists n. apply has_compose. eauto.
    - intros (n & Hn). apply has_compose in Hn as (u & v & Hu & Hv & Hw).
      exists u, v. split; [ | split ]; eauto.
      apply Downset.has_lsup. eauto.
  Qed.

  Global Instance compose_sup_r {i j k} (p : cpos i j k) (s : strat F G i) :
    Sup.Morphism (fun t => compose_when p s t).
  Proof.
    red. intros I x. apply strat_eq. intros w.
    rewrite has_compose, Downset.has_lsup. split.
    - intros (u & v & Hu & (n & Hv) & Hw).
      exists n. apply has_compose. eauto.
    - intros (n & Hn). apply has_compose in Hn as (u & v & Hu & Hv & Hw).
      exists u, v. split; [ | split ]; eauto.
      apply Downset.has_lsup. eauto.
  Qed.

End COMPOSE.

Arguments cpos _ _ _ _ _ _ : clear implicits.
Arguments compose_when {E F G i j k} p s t.

Abbreviation compose := (compose_when cpos_ready).

(** * The identity strategy

  [id E] answers each incoming question by asking the very same
  question of the environment, and relays the answer back.  It may
  also stop, either while [ready] or while [suspended] -- the two
  located bottoms. *)

Inductive id_has {E : isig} : forall {i : position E E}, play E E i -> Prop :=
  | id_nil_ready :
      id_has pnil_ready
  | id_nil_susp (q : E) :
      id_has (pnil_suspended q q)
  | id_oq (q : E) (s : play E E (suspended q q)) :
      id_has s -> id_has (pcons (oq q) (pcons (pq q) s))
  | id_oa (q : E) (r : iar q) (s : play E E ready) :
      id_has s -> id_has (pcons (oa r) (pcons (pa r) s)).

Lemma id_pref {E : isig} {i : position E E} (s' s : play E E i) :
  pref s' s -> id_has s -> id_has s'.
Proof.
  intros Hs' Hs. revert s' Hs'.
  induction Hs; intros s' Hs'.
  - dependent destruction Hs'. constructor.
  - dependent destruction Hs'. constructor.
  - dependent destruction Hs'. { constructor. }
    dependent destruction Hs'. constructor. auto.
  - dependent destruction Hs'. { constructor. }
    dependent destruction Hs'. constructor. auto.
Qed.

Lemma id_closed {E : isig} (i : position E E) :
  dcl (C := play_poset E E i) (@id_has E i).
Proof.
  intros s' s Hs' Hs. apply (id_pref s' s Hs' Hs).
Qed.

Definition idstrat {E : isig} (i : position E E) : strat E E i :=
  mkstrat _ (id_closed i).

Abbreviation sid E := (@idstrat E ready).


(** * Theorem 3.5: layered composition is a category *)

Section COMPOSE_ID.
  Context {E F : isig}.

  Hint Constructors id_has comp_has pref : core.

  (** ** The identity on the left *)

  Definition id_pos_l (i : position E F) : position F F :=
    match i with
      | ready => ready
      | running q => suspended q q
      | suspended q m => suspended q q
    end.

  Definition id_cpos_l (i : position E F) : cpos E F F (id_pos_l i) i i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_right q q
      | suspended q m => cpos_suspended q q m
    end.

  Lemma compose_id_has_l_gt {i} (s : play E F i) :
    exists t, @id_has F (id_pos_l i) t /\ comp_has (id_cpos_l i) t s s.
  Proof.
    induction s; cbn; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn in *; eauto 10.
  Qed.

  Lemma compose_id_has_l_lt {i} (s s' : play E F i)
        (t : play F F (id_pos_l i)) :
    @id_has F (id_pos_l i) t ->
    comp_has (id_cpos_l i) t s s' ->
    pref s' s.
  Proof.
    revert t s'.
    induction s; cbn; intros t s' Ht Hs'.
    - dependent destruction Hs'. { constructor. }
      dependent destruction Ht.
      dependent destruction Hs'.
    - dependent destruction Hs'. constructor.
    - dependent destruction Hs'; cbn in *.
      + constructor.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
  Qed.

  Lemma compose_id_l_when (i : position E F) (σ : strat E F i) :
    compose_when (id_cpos_l i) (idstrat (id_pos_l i)) σ = σ.
  Proof.
    apply strat_eq. intros w. rewrite has_compose. split.
    - intros (u & v & Hu & Hv & Hw).
      apply has_mkstrat in Hu.
      eapply (Downset.has_closed σ w v); [ | assumption ].
      eapply compose_id_has_l_lt; eassumption.
    - intros Hw.
      destruct (compose_id_has_l_gt w) as (t & Ht & Hwt).
      exists t, w. split; [ | split ]; auto.
  Qed.

  (** ** The identity on the right *)

  Definition id_pos_r (i : position E F) : position E E :=
    match i with
      | ready => ready
      | running q => ready
      | suspended q m => suspended m m
    end.

  Definition id_cpos_r (i : position E F) : cpos E E F i (id_pos_r i) i :=
    match i with
      | ready => cpos_ready
      | running q => cpos_left q
      | suspended q m => cpos_suspended q m m
    end.

  Lemma compose_id_has_r_gt {i} (s : play E F i) :
    exists t, @id_has E (id_pos_r i) t /\ comp_has (id_cpos_r i) s t s.
  Proof.
    induction s; cbn; eauto 10.
    destruct IHs as (t & Ht & Hst).
    dependent destruction m; cbn in *; eauto 10.
  Qed.

  Lemma compose_id_has_r_lt {i} (s s' : play E F i)
        (t : play E E (id_pos_r i)) :
    @id_has E (id_pos_r i) t ->
    comp_has (id_cpos_r i) s t s' ->
    pref s' s.
  Proof.
    revert t s'.
    induction s; cbn; intros t s' Ht Hs'.
    - dependent destruction Hs'. constructor.
    - dependent destruction Hs'. { constructor. }
      dependent destruction Ht.
      dependent destruction Hs'.
    - dependent destruction Hs'; cbn in *.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
      + dependent destruction Ht.
        dependent destruction Hs'.
        constructor; eauto.
      + constructor; eauto.
  Qed.

  Lemma compose_id_r_when (i : position E F) (σ : strat E F i) :
    compose_when (id_cpos_r i) σ (idstrat (id_pos_r i)) = σ.
  Proof.
    apply strat_eq. intros w. rewrite has_compose. split.
    - intros (u & v & Hu & Hv & Hw).
      apply has_mkstrat in Hv.
      eapply (Downset.has_closed σ w u); [ | assumption ].
      eapply compose_id_has_r_lt; eassumption.
    - intros Hw.
      destruct (compose_id_has_r_gt w) as (t & Ht & Hwt).
      exists w, t. split; [ | split ]; auto.
  Qed.

  Theorem compose_id_l (σ : E ->> F) :
    compose (sid F) σ = σ.
  Proof.
    apply (compose_id_l_when ready).
  Qed.

  Theorem compose_id_r (σ : E ->> F) :
    compose σ (sid E) = σ.
  Proof.
    apply (compose_id_r_when ready).
  Qed.

End COMPOSE_ID.

(** * Associativity of layered composition

  The two halves say that an interaction of [(s1 . s2) . s3] can
  be re-bracketed as one of [s1 . (s2 . s3)] and conversely, up
  to taking prefixes of the three component plays -- which is
  harmless because each strategy is a downset.  This is the same
  shape as [IRun.runs_rcompose], and like it, it is an induction on
  the inductive relation with no lattice identity involved. *)

Section COMPOSE_COMPOSE.
  Context {E F G H : isig}.

  Variant ccpos :
    forall {i1 i2 i3 i12 i23 i123},
      cpos F G H i1 i2 i12 ->
      cpos E F G i2 i3 i23 ->
      cpos E G H i1 i23 i123 ->
      cpos E F H i12 i3 i123 -> Type :=
    | ccpos_ready :
        ccpos cpos_ready cpos_ready cpos_ready cpos_ready
    | ccpos_left (q1 : H) :
        ccpos (cpos_left q1) cpos_ready (cpos_left q1) (cpos_left q1)
    | ccpos_mid (q1 : H) (q2 : G) :
        ccpos (cpos_right q1 q2) (cpos_left q2)
              (cpos_right q1 q2) (cpos_left q1)
    | ccpos_right (q1 : H) (q2 : G) (q3 : F) :
        ccpos (cpos_suspended q1 q2 q3) (cpos_right q2 q3)
              (cpos_right q1 q2) (cpos_right q1 q3)
    | ccpos_suspended (q1 : H) (q2 : G) (q3 : F) (q4 : E) :
        ccpos (cpos_suspended q1 q2 q3) (cpos_suspended q2 q3 q4)
              (cpos_suspended q1 q2 q4) (cpos_suspended q1 q3 q4).

  Hint Constructors pref comp_has : core.

  Ltac destruct_comp_has :=
    repeat
      match goal with
      | Hx : comp_has _ (_ _) _ _ |- _ => dependent destruction Hx
      | Hx : comp_has _ _ (_ _) _ |- _ => dependent destruction Hx
      | Hx : comp_has _ _ _ (_ _) |- _ => dependent destruction Hx
      | px : ccpos _ _ _ _ |- _ => dependent destruction px
      end.

  Lemma comp_has_assoc_1 {i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3} :
    @ccpos i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3 ->
    forall s t st u stu,
      comp_has p12 s t st ->
      comp_has p12_3 st u stu ->
      exists s' t' u' tu,
        pref s' s /\ pref t' t /\ pref u' u /\
        comp_has p23 t' u' tu /\
        comp_has p1_23 s' tu stu.
  Proof.
    intros p s t st u stu Hst Hst_u.
    revert i3 i23 i123 p23 p1_23 p12_3 p u stu Hst_u.
    induction Hst; intros.
    - destruct_comp_has; eauto 10.
    - destruct_comp_has; eauto 10.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_left q) _ _ Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - destruct_comp_has; eauto 10.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_mid q m) _ _ Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - destruct_comp_has; eauto 10.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_right q m u) _ _ Hst_u)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      eauto 100.
    - rename u into x, u0 into u.
      revert i23 i123 p23 p12_3 p1_23 p stu Hst_u.
      induction u as [ | xx e | ? ? [ | ? e | ? e f | xx yy] u IHu]; intros;
      dependent destruction p;
      dependent destruction Hst_u;
      eauto 100.
      + edestruct (IHu _ _ _ _ _ (ccpos_suspended q m q0 e))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + edestruct (IHu _ _ _ _ _ (ccpos_right q m q0))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - rename u into x, u0 into u.
      revert i23 i123 p23 p12_3 p1_23 p stu Hst_u.
      induction u as [ | xx e | ? ? [ | ? e | ? e f | xx yy] u IHu]; intros;
      dependent destruction p;
      dependent destruction Hst_u;
      eauto 100.
      + edestruct (IHu _ _ _ _ _ (ccpos_suspended q m q0 e))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + edestruct (IHu _ _ _ _ _ (ccpos_right q m q0))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
      + edestruct (IHHst _ _ _ _ _ _ (ccpos_mid q m))
          as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - dependent destruction p.
      edestruct (IHHst _ _ _ _ _ _ (ccpos_left q))
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
    - dependent destruction p.
      dependent destruction Hst_u.
      edestruct (IHHst _ _ _ _ _ _ ccpos_ready)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu); eauto 100.
  Qed.

  Lemma comp_has_assoc_2 {i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3} :
    @ccpos i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3 ->
    forall s t u tu stu,
      comp_has p23 t u tu ->
      comp_has p1_23 s tu stu ->
      exists s' t' u' st,
        pref s' s /\ pref t' t /\ pref u' u /\
        comp_has p12 s' t' st /\
        comp_has p12_3 st u' stu.
  Proof.
    intros p s t u tu stu Htu Hs_tu.
    revert i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3 p t u tu stu Htu Hs_tu.
    induction s as [ | | _ _ [ | | | ] ]; intros.
    - destruct_comp_has; eauto 100.
    - revert i12 i123 p12 p1_23 p12_3 p stu Hs_tu.
      induction Htu; intros;
      dependent destruction p;
      dependent destruction Hs_tu;
      eauto 100.
      + edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + edestruct (IHHtu _ _ _ _ _ (ccpos_suspended _ _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + edestruct (IHHtu _ _ _ _ _ (ccpos_mid _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_left _))
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_mid _ _))
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - revert i12 i123 p12 p1_23 p12_3 p stu Hs_tu.
      induction Htu; intros.
      + destruct_comp_has.
      + destruct_comp_has.
      + dependent destruction p.
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHHtu _ _ _ _ _ (ccpos_suspended _ _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + dependent destruction p.
        dependent destruction Hs_tu.
        eauto 100.
      + dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHHtu _ _ _ _ _ (ccpos_right _ _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + dependent destruction p.
        edestruct (IHHtu _ _ _ _ _ (ccpos_mid _ _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
      + dependent destruction p.
        dependent destruction Hs_tu.
        edestruct (IHs _ _ _ _ _ _ _ _ _ (ccpos_left _))
          as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
    - destruct_comp_has; eauto 100.
      edestruct (IHs _ _ _ _ _ _ _ _ _ ccpos_ready)
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hstu); eauto 100.
  Qed.

  Lemma compose_assoc_when {i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3} :
    @ccpos i1 i2 i3 i12 i23 i123 p12 p23 p1_23 p12_3 ->
    forall s1 s2 s3,
      compose_when p12_3 (compose_when p12 s1 s2) s3 =
      compose_when p1_23 s1 (compose_when p23 s2 s3).
  Proof.
    intros p s1 s2 s3. apply strat_eq. intros stu.
    rewrite !has_compose. split.
    - intros (st & u & Hst & Hu & Hstu).
      apply has_compose in Hst as (s & t & Hs & Ht & Hst).
      edestruct (comp_has_assoc_1 p s t st u stu Hst Hstu)
        as (s' & t' & u' & tu & Hs' & Ht' & Hu' & Htu & Hs_tu).
      exists s', tu. split; [ | split ].
      + eapply Downset.has_closed; eassumption.
      + apply has_compose. exists t', u'. split; [ | split ].
        * eapply Downset.has_closed; eassumption.
        * eapply Downset.has_closed; eassumption.
        * assumption.
      + assumption.
    - intros (s & tu & Hs & Htu & Hstu).
      apply has_compose in Htu as (t & u & Ht & Hu & Htu).
      edestruct (comp_has_assoc_2 p s t u tu stu Htu Hstu)
        as (s' & t' & u' & st & Hs' & Ht' & Hu' & Hst & Hst_u).
      exists st, u'. split; [ | split ].
      + apply has_compose. exists s', t'. split; [ | split ].
        * eapply Downset.has_closed; eassumption.
        * eapply Downset.has_closed; eassumption.
        * assumption.
      + eapply Downset.has_closed; eassumption.
      + assumption.
  Qed.

  Theorem compose_assoc (s1 : G ->> H) (s2 : F ->> G) (s3 : E ->> F) :
    compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
  Proof.
    apply (compose_assoc_when ccpos_ready).
  Qed.

End COMPOSE_COMPOSE.


(** * Residuals

  [next e s] is what is left of the strategy [s] after the move [e]
  has been played.  Composition interacts with residuals exactly as
  the game dictates; these are the equations that drive the
  refinement square proofs below. *)

Definition mkds {C : poset} (P : C -> Prop) (H : dcl P) : Downset.F C :=
  Downset.Build_downset C P H.

Lemma has_mkds {C : poset} P H (c : C) :
  Downset.has (@mkds C P H) c <-> P c.
Proof.
  reflexivity.
Qed.

Lemma next_closed {E F} {i j} (e : move E F i j) (sg : strat E F i) :
  dcl (C := play_poset E F j) (fun s => Downset.has sg (pcons e s)).
Proof.
  intros x y Hxy Hy. eapply Downset.has_closed; [ | eassumption ].
  apply pcons_pref. exact Hxy.
Qed.

Definition next {E F} {i j} (e : move E F i j) (sg : strat E F i)
  : strat E F j :=
  mkds _ (next_closed e sg).

Lemma has_next {E F i j} (e : move E F i j) (sg : strat E F i) s :
  Downset.has (next e sg) s <-> Downset.has sg (pcons e s).
Proof.
  reflexivity.
Qed.

Section NEXT_COMPOSE.
  Context {E F G : isig}.

  Hint Constructors comp_has : core.

  Lemma compose_next_oq (q : G) (s : strat F G ready) (t : strat E F ready) :
    compose_when (cpos_left q) (next (oq q) s) t =
    next (oq q) (compose_when cpos_ready s t).
  Proof.
    apply strat_eq. intros w. rewrite has_compose, has_next, has_compose.
    split.
    - intros (u & v & Hu & Hv & Hw).
      exists (pcons (oq q) u), v. split; [ | split ]; auto.
    - intros (u & v & Hu & Hv & Hw).
      dependent destruction Hw.
      exists s0, v. split; [ | split ]; auto.
  Qed.

  Lemma compose_next_lq {q : G} (m : F)
        (s : strat F G (running q)) (t : strat E F ready) :
    compose_when (cpos_right q m) (next (pq m) s) (next (oq m) t) [=
    compose_when (cpos_left q) s t.
  Proof.
    intros w Hw. apply has_compose in Hw as (u & v & Hu & Hv & Hw).
    apply has_compose.
    exists (pcons (pq m) u), (pcons (oq m) v). split; [ | split ]; auto.
  Qed.

  Lemma compose_next_rq {q : G} {m : F} (u : E)
        (s : strat F G (suspended q m)) (t : strat E F (running m)) :
    compose_when (cpos_suspended q m u) s (next (pq u) t) [=
    next (pq u) (compose_when (cpos_right q m) s t).
  Proof.
    intros w Hw. apply has_compose in Hw as (x & y & Hx & Hy & Hw).
    apply has_next, has_compose.
    exists x, (pcons (pq u) y). split; [ | split ]; auto.
  Qed.

  Lemma compose_next_oa {q : G} {m : F} {u : E} (v : iar u)
        (s : strat F G (suspended q m)) (t : strat E F (suspended m u)) :
    compose_when (cpos_right q m) s (next (oa v) t) =
    next (oa v) (compose_when (cpos_suspended q m u) s t).
  Proof.
    apply strat_eq. intros w. rewrite has_compose, has_next, has_compose.
    split.
    - intros (x & y & Hx & Hy & Hw).
      exists x, (pcons (oa v) y). split; [ | split ]; auto.
    - intros (x & y & Hx & Hy & Hw).
      dependent destruction Hw.
      exists x, t0. split; [ | split ]; auto.
  Qed.

  Lemma compose_next_ra {q : G} {m : F} (n : iar m)
        (s : strat F G (suspended q m)) (t : strat E F (running m)) :
    compose_when (cpos_left q) (next (oa n) s) (next (pa n) t) [=
    compose_when (cpos_right q m) s t.
  Proof.
    intros w Hw. apply has_compose in Hw as (x & y & Hx & Hy & Hw).
    apply has_compose.
    exists (pcons (oa n) x), (pcons (pa n) y). split; [ | split ]; auto.
  Qed.

  Lemma compose_next_la {q : G} (r : iar q)
        (s : strat F G (running q)) (t : strat E F ready) :
    compose_when cpos_ready (next (pa r) s) t [=
    next (pa r) (compose_when (cpos_left q) s t).
  Proof.
    intros w Hw. apply has_compose in Hw as (x & y & Hx & Hy & Hw).
    apply has_next, has_compose.
    exists (pcons (pa r) x), y. split; [ | split ]; auto.
  Qed.

End NEXT_COMPOSE.


(** * Refinement conventions (Def. 4.1)

  A simulation relation is *not* a strategy.  A strategy's
  nondeterminism is angelic in its own moves, so it cannot
  demonically quantify over which question to ask -- an [inf] of
  strategies that ask different questions collapses.  That is
  precisely what [CAL.srel_pull] does in the [FCD] model, and why
  it has to be a morphism built from [inf] there.

  In the game model a simulation relation is a *refinement
  convention*: a relation between the two games rather than a
  strategy for one of them.  Its plays record which questions are
  allowed to correspond, and which pairs of answers are forbidden
  (meaning the simulation breaks).  And once again the carrier is a
  plain downset. *)

Section RC.
  Context {E1 E2 : isig}.

  Inductive rcp :=
    | rcp_allow (m1 : E1) (m2 : E2)
    | rcp_forbid (m1 : E1) (m2 : E2) (n1 : iar m1) (n2 : iar m2)
    | rcp_cont (m1 : E1) (m2 : E2) (n1 : iar m1) (n2 : iar m2) (k : rcp).

  Inductive rcp_ref : rcp -> rcp -> Prop :=
    | rcp_allow_ref m1 m2 :
        rcp_ref (rcp_allow m1 m2) (rcp_allow m1 m2)
    | rcp_allow_cont_ref m1 m2 n1 n2 k :
        rcp_ref (rcp_allow m1 m2) (rcp_cont m1 m2 n1 n2 k)
    | rcp_allow_forbid_ref m1 m2 n1 n2 :
        rcp_ref (rcp_allow m1 m2) (rcp_forbid m1 m2 n1 n2)
    | rcp_cont_ref m1 m2 n1 n2 k k' :
        rcp_ref k k' ->
        rcp_ref (rcp_cont m1 m2 n1 n2 k) (rcp_cont m1 m2 n1 n2 k')
    | rcp_cont_forbid_ref m1 m2 n1 n2 k :
        rcp_ref (rcp_cont m1 m2 n1 n2 k) (rcp_forbid m1 m2 n1 n2)
    | rcp_forbid_ref m1 m2 n1 n2 :
        rcp_ref (rcp_forbid m1 m2 n1 n2) (rcp_forbid m1 m2 n1 n2).

  Lemma rcp_ref_refl w : rcp_ref w w.
  Proof.
    induction w; constructor; auto.
  Qed.

  Lemma rcp_ref_trans x y z : rcp_ref x y -> rcp_ref y z -> rcp_ref x z.
  Proof.
    intros Hxy. revert z.
    induction Hxy; intros z Hyz;
    dependent destruction Hyz; constructor; auto.
  Qed.

  Lemma rcp_ref_antisym x y : rcp_ref x y -> rcp_ref y x -> x = y.
  Proof.
    intros Hxy Hyx.
    induction Hxy; dependent destruction Hyx; firstorder congruence.
  Qed.

  Definition rcp_poset : poset :=
    {|
      poset_carrier := rcp;
      ref := rcp_ref;
      ref_refl := rcp_ref_refl;
      ref_trans := rcp_ref_trans;
      ref_antisym := rcp_ref_antisym;
    |}.

  Definition conv : ccdlattice := Downset.F rcp_poset.

  (** The residual of a convention after a question pair has been
    answered. *)

  Lemma rcnext_closed (q1 : E1) (q2 : E2) (r1 : iar q1) (r2 : iar q2)
        (R : conv) :
    dcl (C := rcp_poset) (fun w => Downset.has R (rcp_cont q1 q2 r1 r2 w)).
  Proof.
    intros s t Hst Hs. eapply Downset.has_closed; [ | eassumption ].
    apply rcp_cont_ref. exact Hst.
  Qed.

  Definition rcnext (q1 : E1) (q2 : E2) (r1 : iar q1) (r2 : iar q2)
             (R : conv) : conv :=
    mkds _ (rcnext_closed q1 q2 r1 r2 R).

  Lemma has_rcnext q1 q2 r1 r2 R w :
    Downset.has (rcnext q1 q2 r1 r2 R) w <->
    Downset.has R (rcp_cont q1 q2 r1 r2 w).
  Proof.
    reflexivity.
  Qed.

  (** Downward closure, spelled out for [auto]. *)

  Lemma conv_has_cont_allow q1 q2 r1 r2 k (R : conv) :
    Downset.has R (rcp_cont q1 q2 r1 r2 k) ->
    Downset.has R (rcp_allow q1 q2).
  Proof.
    intros H. eapply Downset.has_closed; [ | eassumption ]. constructor.
  Qed.

  Lemma conv_has_forbid_allow q1 q2 r1 r2 (R : conv) :
    Downset.has R (rcp_forbid q1 q2 r1 r2) ->
    Downset.has R (rcp_allow q1 q2).
  Proof.
    intros H. eapply Downset.has_closed; [ | eassumption ]. constructor.
  Qed.

  Lemma conv_has_forbid_cont q1 q2 r1 r2 k (R : conv) :
    Downset.has R (rcp_forbid q1 q2 r1 r2) ->
    Downset.has R (rcp_cont q1 q2 r1 r2 k).
  Proof.
    intros H. eapply Downset.has_closed; [ | eassumption ]. constructor.
  Qed.

End RC.

Arguments rcp : clear implicits.
Arguments rcp_poset : clear implicits.
Arguments conv : clear implicits.

Global Hint Immediate
  conv_has_cont_allow
  conv_has_forbid_allow
  conv_has_forbid_cont : core.

(** * Refinement squares (Def. 4.2)

  [rsq R S s t] says that the strategy [s] refines [t] along the
  refinement conventions [R] (on the underlay) and [S] (on the
  overlay).  This is the CAL statement: [s] is an implementation,
  [t] a specification, and [R], [S] the simulation relations that
  connect their interfaces.  Note that the clauses for opponent
  moves quantify over *all* related moves -- that is where the
  demonic content lives, and it is a [forall] in a definition, not
  an [inf] in a lattice. *)

Lemma next_mono {E F i j} (e : move E F i j) (s t : strat E F i) :
  s [= t -> next e s [= next e t.
Proof.
  intros Hst w Hw. apply Hst. exact Hw.
Qed.

Section RSQ.
  Context {E1 E2 F1 F2 : isig}.

  Variant rspos : position E1 F1 -> position E2 F2 -> Type :=
    | rs_ready :
        rspos ready ready
    | rs_running (q1 : F1) (q2 : F2) :
        rspos (running q1) (running q2)
    | rs_suspended (q1 : F1) (q2 : F2) (m1 : E1) (m2 : E2) :
        rspos (suspended q1 m1) (suspended q2 m2).

  Inductive rsp (R : conv E1 E2) (S : conv F1 F2) :
    forall {i1 i2}, rspos i1 i2 ->
                    play E1 F1 i1 -> strat E2 F2 i2 -> Prop :=
    | rsp_ready (t : strat E2 F2 ready) :
        Downset.has t pnil_ready ->
        rsp R S rs_ready pnil_ready t
    | rsp_oq (q1 : F1) (s : play E1 F1 (running q1))
             (t : strat E2 F2 ready) :
        Downset.has t pnil_ready ->
        (forall q2 : F2, Downset.has S (rcp_allow q1 q2) ->
                    rsp R S (rs_running q1 q2) s (next (oq q2) t)) ->
        rsp R S rs_ready (pcons (oq q1) s) t
    | rsp_pq (q1 : F1) (q2 : F2) (m1 : E1) (m2 : E2)
             (s : play E1 F1 (suspended q1 m1))
             (t : strat E2 F2 (running q2)) :
        Downset.has R (rcp_allow m1 m2) ->
        rsp R S (rs_suspended q1 q2 m1 m2) s (next (pq m2) t) ->
        rsp R S (rs_running q1 q2) (pcons (pq m1) s) t
    | rsp_suspended (q1 : F1) (q2 : F2) (m1 : E1) (m2 : E2)
                    (t : strat E2 F2 (suspended q2 m2)) :
        Downset.has t (pnil_suspended q2 m2) ->
        rsp R S (rs_suspended q1 q2 m1 m2) (pnil_suspended q1 m1) t
    | rsp_oa (q1 : F1) (q2 : F2) (m1 : E1) (m2 : E2) (n1 : iar m1)
             (s : play E1 F1 (running q1))
             (t : strat E2 F2 (suspended q2 m2)) :
        Downset.has t (pnil_suspended q2 m2) ->
        (forall n2 : iar m2,
           ~ Downset.has R (rcp_forbid m1 m2 n1 n2) ->
           rsp (rcnext m1 m2 n1 n2 R) S (rs_running q1 q2) s
               (next (oa n2) t)) ->
        rsp R S (rs_suspended q1 q2 m1 m2) (pcons (oa n1) s) t
    | rsp_pa (q1 : F1) (q2 : F2) (r1 : iar q1) (r2 : iar q2)
             (s : play E1 F1 ready)
             (t : strat E2 F2 (running q2)) :
        ~ Downset.has S (rcp_forbid q1 q2 r1 r2) ->
        rsp R (rcnext q1 q2 r1 r2 S) rs_ready s (next (pa r2) t) ->
        rsp R S (rs_running q1 q2) (pcons (pa r1) s) t.

  Definition rsq_when (R : conv E1 E2) (S : conv F1 F2) {i1 i2}
             (p : rspos i1 i2) (s : strat E1 F1 i1) (t : strat E2 F2 i2) :=
    forall u, Downset.has s u -> rsp R S p u t.

  Definition rsq R S (s : E1 ->> F1) (t : E2 ->> F2) :=
    rsq_when R S rs_ready s t.

  (** A refinement square is preserved when the target strategy is
    weakened.  This is all the monotonicity the horizontal
    composition proof needs. *)

  Lemma rsp_ref_target {R S i1 i2} {p : rspos i1 i2}
        {s : play E1 F1 i1} {t t' : strat E2 F2 i2} :
    t [= t' -> rsp R S p s t -> rsp R S p s t'.
  Proof.
    intros Htt' H. revert t' Htt'.
    induction H; intros t' Htt'.
    - constructor. apply Htt'. assumption.
    - constructor.
      + apply Htt'. assumption.
      + intros q2 Hq2. apply H1; auto. apply next_mono. assumption.
    - econstructor; [ eassumption | ].
      apply IHrsp. apply next_mono. assumption.
    - constructor. apply Htt'. assumption.
    - constructor.
      + apply Htt'. assumption.
      + intros n2 Hn2. apply H1; auto. apply next_mono. assumption.
    - econstructor; [ eassumption | ].
      apply IHrsp. apply next_mono. assumption.
  Qed.

End RSQ.

Arguments rspos _ _ _ _ _ _ : clear implicits.


(** * Theorem 4.3: horizontal composition of refinement squares

  This is the CAL principle.  If [s1] implements [s2] along [S] and
  [T], and [t1] implements [t2] along [R] and [S], then the
  composite implementation refines the composite specification along
  [R] and [T].  Layers compose, and so do the simulation relations
  that justify them. *)

Section RSQ_COMP.
  Context {E1 E2 : isig} (R : conv E1 E2).
  Context {F1 F2 : isig} (S : conv F1 F2).
  Context {G1 G2 : isig} (T : conv G1 G2).

  Variant rscpos : forall {i1 j1 k1 i2 j2 k2},
    cpos E1 F1 G1 i1 j1 k1 -> cpos E2 F2 G2 i2 j2 k2 ->
    rspos F1 F2 G1 G2 i1 i2 ->
    rspos E1 E2 F1 F2 j1 j2 ->
    rspos E1 E2 G1 G2 k1 k2 -> Type :=
    | rsc_ready :
        rscpos cpos_ready cpos_ready rs_ready rs_ready rs_ready
    | rsc_left (q1 : G1) (q2 : G2) :
        rscpos (cpos_left q1) (cpos_left q2)
               (rs_running q1 q2) rs_ready (rs_running q1 q2)
    | rsc_right (q1 : G1) (q2 : G2) (m1 : F1) (m2 : F2) :
        rscpos (cpos_right q1 m1) (cpos_right q2 m2)
               (rs_suspended q1 q2 m1 m2) (rs_running m1 m2)
               (rs_running q1 q2)
    | rsc_suspended (q1 : G1) (q2 : G2) (m1 : F1) (m2 : F2)
                    (u1 : E1) (u2 : E2) :
        rscpos (cpos_suspended q1 m1 u1) (cpos_suspended q2 m2 u2)
               (rs_suspended q1 q2 m1 m2) (rs_suspended m1 m2 u1 u2)
               (rs_suspended q1 q2 u1 u2).

  Hint Constructors comp_has pref rscpos : core.

  Lemma rsp_comp {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (s : play F1 G1 i1) (t : play E1 F1 j1)
           (sg : strat F2 G2 i2) (tu : strat E2 F2 j2)
           (w : play E1 G1 k1),
      comp_has p1 s t w ->
      rsp S T pi s sg ->
      rsp R S pj t tu ->
      rsp R T pk w (compose_when p2 sg tu).
  Proof.
    intros p s t sg tu w Hw Hs Ht.
    revert R S T i2 j2 k2 p2 pi pj pk p sg tu Hs Ht.
    induction Hw; intros.
    - (* ready *)
      dependent destruction p. dependent destruction Hs.
      constructor. apply has_compose.
      exists pnil_ready, pnil_ready. repeat apply conj; eauto.
      dependent destruction Ht; eauto.
    - (* incoming question *)
      dependent destruction p. dependent destruction Hs.
      constructor.
      + apply has_compose.
        exists pnil_ready, pnil_ready. repeat apply conj; eauto.
        dependent destruction Ht; eauto.
      + intros q2 Hq. rewrite <- (compose_next_oq q2). eauto.
    - (* internal question *)
      dependent destruction p. dependent destruction Hs.
      dependent destruction Ht.
      eapply rsp_ref_target; [ apply compose_next_lq | ]. eauto.
    - (* outgoing question *)
      dependent destruction p. dependent destruction Ht.
      econstructor; [ eassumption | ].
      eapply rsp_ref_target; [ apply compose_next_rq | ]. eauto.
    - (* suspended *)
      dependent destruction p. dependent destruction Ht.
      constructor. apply has_compose.
      eexists (pnil_suspended _ _), (pnil_suspended _ _).
      repeat apply conj; eauto.
      dependent destruction Hs; eauto.
    - (* environment answer *)
      dependent destruction p. dependent destruction Ht.
      constructor.
      + apply has_compose.
        eexists (pnil_suspended _ _), (pnil_suspended _ _).
        repeat apply conj; eauto.
        dependent destruction Hs; eauto.
      + intros n2 Hn. rewrite <- compose_next_oa. eauto.
    - (* answer of the inner strategy *)
      dependent destruction p. dependent destruction Hs.
      dependent destruction Ht.
      eapply rsp_ref_target; [ apply compose_next_ra | ]. eauto.
    - (* answer of the outer strategy *)
      dependent destruction p. dependent destruction Hs.
      econstructor; [ eassumption | ].
      eapply rsp_ref_target; [ apply compose_next_la | ]. eauto.
  Qed.

  Lemma rsq_comp_when {i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk} :
    @rscpos i1 j1 k1 i2 j2 k2 p1 p2 pi pj pk ->
    forall (s1 : strat F1 G1 i1) (t1 : strat E1 F1 j1)
           (s2 : strat F2 G2 i2) (t2 : strat E2 F2 j2),
      rsq_when S T pi s1 s2 ->
      rsq_when R S pj t1 t2 ->
      rsq_when R T pk (compose_when p1 s1 t1) (compose_when p2 s2 t2).
  Proof.
    intros p s1 t1 s2 t2 Hs Ht w1 Hw1.
    apply has_compose in Hw1 as (u & v & Hu & Hv & Huv).
    eapply rsp_comp; eauto.
  Qed.

  Theorem rsq_comp (s1 : F1 ->> G1) (t1 : E1 ->> F1)
          (s2 : F2 ->> G2) (t2 : E2 ->> F2) :
    rsq S T s1 s2 ->
    rsq R S t1 t2 ->
    rsq R T (compose s1 t1) (compose s2 t2).
  Proof.
    apply (rsq_comp_when rsc_ready).
  Qed.

End RSQ_COMP.

(** * Why simulation relations cannot be strategies

  In the [FCD] model of [examples/CAL.v] a simulation relation is a
  morphism, [CAL.srel_pull], built with an [inf] over the related
  states: on an incoming call it demonically picks a related state
  and asks the corresponding question.  A strategy cannot do that.
  Its nondeterminism is angelic in its own moves, so a strategy
  refining several strategies that ask *different* questions cannot
  ask any question at all. *)

Inductive uop := ua1 | ua2.
Definition U : isig := {| iop := uop; iar := fun _ => unit |}.
Inductive vop := vq.
Definition V : isig := {| iop := vop; iar := fun _ => unit |}.

Definition ask1 : play U V ready :=
  pcons (oq (vq : V)) (pcons (pq (ua1 : U)) (pnil_suspended (vq : V) (ua1 : U))).

Definition ask2 : play U V ready :=
  pcons (oq (vq : V)) (pcons (pq (ua2 : U)) (pnil_suspended (vq : V) (ua2 : U))).

Lemma no_demonic_question (sigma : U ->> V) :
  sigma [= (Downset.emb (C := play_poset U V ready) ask1 : U ->> V) ->
  sigma [= (Downset.emb (C := play_poset U V ready) ask2 : U ->> V) ->
  forall p, ~ Downset.has sigma (pcons (oq (vq : V)) p).
Proof.
  intros H1 H2 p Hp.
  specialize (H1 _ Hp). specialize (H2 _ Hp).
  assert (pref (pcons (oq (vq : V)) p) ask1) as K1 by exact H1.
  assert (pref (pcons (oq (vq : V)) p) ask2) as K2 by exact H2.
  unfold ask1 in K1. unfold ask2 in K2.
  dependent destruction K1. dependent destruction K2.
  dependent destruction K1. dependent destruction K2.
Qed.

(** So [meet (emb ask1) (emb ask2)] -- the demonic choice between
  asking [ua1] and asking [ua2] -- is a perfectly good element of
  the lattice [U ->> V], but it is not a strategy that does
  anything: it refuses every question.  This is why thesis Chapter 4
  makes a simulation relation a *refinement convention*, a relation
  between the two games, rather than a morphism of the category.  A
  pleasant consequence for the [CAL] development: the adjunction
  [CAL.srel_push_pull] -- which that file leaves admitted, and which
  is the hard step there -- has no counterpart to prove here.  [rsq]
  is the refinement relation directly. *)
(** * Bottom is located

  In [FCD.F] there is a single global [bot], so a computation that
  aborts after issuing [m] is identified with one that aborts
  immediately -- thesis section 5.3.3, and the reason
  [ISpec.pbind] has to join [emb (pmove m)] onto its recursive call.
  Here the two are different generators, and so different
  strategies. *)

Lemma stall_ne_bot {E F : isig} (q : F) (m : E) :
  (Downset.emb (C := play_poset E F ready)
     (pcons (oq q) (pcons (pq m) (pnil_suspended q m))) : strat E F ready)
  <> bot.
Proof.
  intros Hc.
  assert (Downset.has (bot : strat E F ready)
            (pcons (oq q) (pcons (pq m) (pnil_suspended q m)))) as Hb.
  { rewrite <- Hc. apply pref_refl. }
  pose proof (bot_lb (Downset.emb (C := play_poset E F ready) pnil_ready
                      : strat E F ready) _ Hb) as Hp.
  assert (pref (pcons (oq q) (pcons (pq m) (pnil_suspended q m)))
               (@pnil_ready E F)) as Hp' by exact Hp.
  inversion Hp'.
Qed.
(** * Modelling CAL

  What [examples/CAL.v] needs, and where it stands here.

  Available now, constructively:

  - Layers as morphisms and layer composition: [compose],
    [compose_id_l], [compose_id_r], [compose_assoc].
  - Simulation relations: [conv], with residuals [rcnext].
  - The refinement relation between an implementation and a
    specification along two simulation relations: [rsq].
  - The CAL soundness principle -- layers compose and so do the
    simulations that justify them: [rsq_comp].

  Still to be built, but with no apparent obstruction:

  - The empty signature, and the state-carrying signature [E # S] of
    [CAL.state_sig], so that a layer interface is a morphism out of
    the empty signature.  Both are just [isig]s.
  - [CAL.slift], the state-passing lift of a strategy.  In the
    strategy model this is a transformation of plays, so it should
    be an inductive relation and a [Downset] like everything else
    here, rather than the [ISpec.ext] of [CAL.stateful_play].

  Not available, and the one place where the classical reasoning of
  [models.IntStrat] actually bites:

  - Vertical composition of refinement squares, thesis Theorem 4.8.
    The object [vcomp R S] and its properties ([vcomp_expand],
    [rcnext_vcomp_at]) look constructive -- they are [firstorder]
    reasoning about downsets -- but the square-composition theorem
    [rsq_vcomp] goes through [rsp_inf], and that proof uses
    [not_all_ex_not] to turn

      [~ Downset.has (inf i, R i) (rcp_forbid m1 m2 n1 n2)]

    into a witness [i] with [~ Downset.has (R i) (rcp_forbid ...)].
    That step is genuinely classical, and it also needs the target
    strategy to be [Deterministic].  The root cause is that
    refinement conventions are specified *negatively*, by which
    answer pairs are forbidden: a negated universal is not a source
    of witnesses constructively.  A positive presentation -- which
    answer pairs are *allowed* -- would not have that problem, but
    changing it is a redesign, not a translation, and we have not
    attempted it here.

  So: horizontal composition, which is what makes layers compose, is
  constructive.  Chaining refinements vertically is not, as the
  argument currently stands. *)

(** * Summary

  Collecting the above, strategies and layered composition form a
  category, constructively:

    objects        effect signatures [isig]
    morphisms      [E ->> F = strat E F ready], a [Downset.F]
    identity       [sid]
    composition    [compose]

  with [compose_id_l], [compose_id_r] and [compose_assoc] proved,
  and composition a complete join homomorphism in each argument
  ([compose_sup_l], [compose_sup_r]).  [Print Assumptions] on each
  reports functional extensionality, propositional extensionality
  and [Eqdep.Eq_rect_eq.eq_rect_eq] -- the last of which is
  [eq_rect_eq_propext] above, a consequence of propositional
  extensionality, not a new assumption.  No excluded middle, no
  choice.

  Compare the situation in [models.IntSpec].  There
  [ISpec.compose] is associative only via [ISpec.apply_assoc],
  which is admitted; the lattice-theoretic reduction
  [ISpec.compose_assoc_of_bind] leaves an exchange law for which
  neither inclusion is provable, and [codist_lem] shows the
  distributivity that would be needed is excluded middle.  Three
  differences account for the change, and they are the same three
  that made [IRun] work:

  - The lattice is a plain [Downset.F], so composition is a single
    existential over an inductive relation ([comp_has]) rather than
    two nested [FCD.ext]s.  Nothing ever has to move an [inf] past a
    [join].

  - [comp_has] is downward closed in its result ([comp_has_pref]),
    because each strategy is a downset.  So the composite is a
    downset too, and associativity is an equivalence of inductive
    relations ([comp_has_assoc_1], [comp_has_assoc_2]) rather than a
    lattice identity.

  - Bottom is located.  [pnil_ready] and [pnil_suspended q m] are
    distinct generators, so "stopped having already asked [m] inside
    [q]" is not identified with "stopped immediately".  That
    identification is the global [bot] of thesis section 5.3.3, and
    it is what forces the [emb (pmove m) ||] in [ISpec.pbind] and
    hence the appeal to codistributivity.

  What makes it possible to give up the demonic [inf] without
  losing demonic nondeterminism is that the game carries the
  alternation: [position] distinguishes [ready], [running] and
  [suspended], and the typing of [move] forces opponent and player
  to alternate.  A strategy that must handle every answer [n : iar m]
  does so by containing a play for each, not by being an [inf].

  What is *not* ported here is everything from thesis Chapter 4 on:
  refinement conventions, the simulation-relation machinery and the
  spatial/temporal structure.  That is where the classical reasoning
  in [models.IntStrat] actually lives -- 27 of its 45 uses of
  [classic] decide [Downset.has R (rcp_forbid q1 q2 r1 r2)], and
  most of the rest decide equality of answer values.  Those are
  decidability assumptions about concrete data, dischargeable per
  signature, rather than a lattice law that no model satisfies. *)


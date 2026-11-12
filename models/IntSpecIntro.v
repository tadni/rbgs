(** * IntSpecIntro: Choice, Excluded Middle, and Interaction *)

(** This chapter is a guided tour of [IntSpec.v].  It does not
    rebuild that file.  It asks two questions about it and answers
    them with small Rocq proofs:

    - The classical version of the development needed the axiom
      of choice.  The constructive one does not.  Where exactly
      did choice use to come in, and what took its place?

    - The constructive version still proves [ISpec.bind_bind]
      only under a hypothesis that amounts to excluded middle.
      Is that a weakness of the proof, or of the statement?

    The short answers are: choice came in through one equation,
    the law of complete distributivity, and it goes away once we
    restate that law the way Fawcett and Wood do.  And excluded
    middle is not an artifact of the proof.  At the end of the
    chapter we prove that [bind_bind] _implies_ excluded middle.

    We assume you have skimmed the header comment of [IntSpec.v]
    and know roughly what a complete lattice is. *)

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import RelationClasses Morphisms Setoid.
From models Require Import IntSpec.

(* ################################################################ *)
(** * The Setting *)

(** An interaction specification [ISpec.t E V] describes a
    computation that talks to an environment through the effect
    signature [E] and may return a value of type [V].  Its
    elements are built from _plays_, finite traces like

      [pcons m n (pcons m' n' (pret v))]

    ("I asked [m], got [n], asked [m'], got [n'], returned
    [v]"), using two kinds of choice:

    - [sup], angelic choice: the system picks;
    - [inf], demonic choice: the environment picks.

    The space with both is the _free completely distributive
    lattice_ over the poset of plays.  "Free" means: start from
    the plays, throw in every [sup] and every [inf], and identify
    only what the lattice laws force you to.

    The trouble is in the phrase "completely distributive". *)

(* ################################################################ *)
(** * Part I: Where Choice Came From *)

(* ================================================================ *)
(** ** The classical law *)

(** In a finite distributive lattice, [&&] distributes over [||].
    The infinitary version, which is what "completely
    distributive" means in the textbooks, reads

      inf i, sup j, x i j  =  sup f, inf i, x i (f i)

    where [f] ranges over all _choice functions_, that is, over
    all [f : forall i, J i].

    Read it as a game.  On the left, the demon picks a row [i],
    and then the angel picks a column [j] in that row.  On the
    right the angel must commit first, to a whole strategy [f]
    saying which column to take in every row; then the demon picks
    a row.  The law says the angel loses nothing by committing.

    Let us write this law down. *)

Definition classical_cd (L : ccdlattice) :=
  forall (I : Type) (J : I -> Type) (x : forall i, J i -> L),
    (inf i, sup j, x i j) =
    sup (f : forall i, J i), inf i, x i (f i).

(** And the axiom of choice, in its type-theoretic form: a
    relation that is total on the left contains a function. *)

Definition AC :=
  forall (I : Type) (J : I -> Type) (R : forall i, J i -> Prop),
    (forall i, exists j, R i j) ->
    exists f : forall i, J i, forall i, R i (f i).

(** It is easy to believe these two are related.  To pass from the
    left side of [classical_cd] to the right, you know that for
    each [i] there is some good [j], and you need a single [f]
    that picks one for every [i].  That is exactly what [AC] gives
    you.

    It is worse than related.  Take the smallest interesting
    lattice there is: the lattice of propositions. *)

(* ================================================================ *)
(** ** The lattice of propositions *)

(** [IntSpec.v] builds every lattice it needs out of one
    construction, [Downset.F C]: the down-closed subsets of a
    poset [C], ordered by inclusion, with [sup] as union and [inf]
    as intersection.

    Over the one-point poset, a down-closed subset is just a
    proposition, namely "is the point in it?".  So [Downset.F] of
    the one-point poset is [Prop] in disguise. *)

Definition unit_poset : poset :=
  {|
    poset_carrier := unit;
    ref _ _ := True;
    ref_refl _ := I;
    ref_trans _ _ _ _ _ := I;
    ref_antisym x y _ _ :=
      match x, y return x = y with tt, tt => eq_refl end;
  |}.

Definition Omega : ccdlattice := Downset.F unit_poset.

Definition prop_ds (Q : Prop) : Omega :=
  {| Downset.has _ := Q; Downset.has_closed _ _ _ H := H |}.

Lemma has_prop_ds Q c : Downset.has (prop_ds Q) c <-> Q.
Proof. reflexivity. Qed.

(** In [Omega], [sup] is [exists] and [inf] is [forall].  The
    classical law becomes

      (forall i, exists j, R i j) <-> exists f, forall i, R i (f i)

    which is [AC] on the nose. *)

Theorem classical_cd_AC : classical_cd Omega -> AC.
Proof.
  intros H I J R HR.
  specialize (H I J (fun i j => prop_ds (R i j))).
  assert (Hin : Downset.has
                  (inf i, sup j, prop_ds (R i j) : Omega) tt).
  { apply Downset.has_linf. intros i.
    apply Downset.has_lsup. destruct (HR i) as [j Hj].
    exists j. exact Hj. }
  rewrite H in Hin.
  apply Downset.has_lsup in Hin as [f Hf].
  exists f. intros i.
  exact (proj1 (Downset.has_linf _ _) Hf i).
Qed.

(** So if your definition of "completely distributive lattice"
    is [classical_cd], then the moment you build even one example
    of the thing, you have assumed the axiom of choice.  This is
    Theorem 6 of Fawcett and Wood, _Constructive complete
    distributivity I_ (1990).  The classical development of
    interaction specifications used exactly this definition, and
    paid for it. *)

(* ================================================================ *)
(** ** The constructive law *)

(** Fawcett and Wood's way out is to notice that the angel's
    strategy [f] does not have to vary with [i] if the columns are
    arranged well.

    Suppose each row is not an arbitrary family [x i : J i -> L]
    but a _down-closed set_ [P i] of elements of [L].  Down-closed
    means: if [y] is in [P i] and [z [= y], then [z] is in [P i]
    too.  Now look at an element [y] that lies in every [P i].
    The angel has a strategy that works against every row, and it
    is the constant one: "always play [y]".

    So, for down-closed rows, the law needs only constant choice
    functions, and a constant function is not chosen.  It is just
    an element.  That gives the equation [IntSpec.v] takes as an
    axiom of its lattices (the field [ccd] of [ccdlattice]):

      inf i, (sup {x | P i x}, x) = sup {x | forall i, P i x}, x
        (when every P i is down-closed)

    Look at the right side.  The [sup] ranges over elements, not
    over functions.  The "for every [i]" stays inside a
    proposition, [forall i, P i x], where no one has to produce a
    function from it. *)

Check inf_sup_dcl.
(* ===> forall (L : ccdlattice) (I : Type) (P : I -> L -> Prop),
          (forall i, dcl (P i)) ->
          inf i, (sup {x | P i x}, x)
          = sup {x | forall i, P i x}, x *)

(** Any family can be made down-closed by closing it downward,
    and that changes no [sup].  So the constructive law still
    tells us how an [inf] of [sup]s behaves for arbitrary
    families: *)

Check inf_sup.
(* ===> inf i, sup j, x i j
        = sup {y | forall i, exists j, y [= x i j}, y *)

(** Compare this with [classical_cd].  The right side of
    [classical_cd] wants an [f].  The right side of [inf_sup]
    wants a [y] with [forall i, exists j, ...].  The [exists] is
    left where it is, under the [forall].  We never pull it out.

    In the presence of [AC] you _could_ pull it out, and then you
    get the classical law back.  The next exercise asks you to do
    that.  It shows the constructive law is not weaker in any
    way you would notice classically; it just refuses to make the
    one move that costs choice. *)

(** **** Exercise: 3 stars, standard (AC_classical_cd)

    Show that every [ccdlattice] satisfies the classical law if we
    are allowed to use [AC].  Use [inf_sup] for one direction.  The
    other direction needs no axioms. *)

Theorem AC_classical_cd : AC -> forall L, classical_cd L.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================ *)
(** ** Why the downset lattice satisfies it *)

(** An axiom is only worth stating if something satisfies it.
    [IntSpec.v] proves that every [Downset.F C] is a
    [ccdlattice], with no axioms but extensionality.  This is
    Fawcett and Wood's Theorem 3, and the proof is short enough to
    read in full.  Here is the interesting half of [Downset.dccd]:

      intros H.
      assert (forall i, P i (emb c)) as Hc.
      { ... }
      exists (exist _ (emb c) Hc).

    We are given a point [c] lying in [sup {S | P i S}, S] for
    every [i]: for each row there is some downset [S] in [P i]
    containing [c].  Classically, one would choose such an [S] for
    each [i].  Instead, the proof takes the smallest downset that
    contains [c] at all, [emb c] ("everything below [c]").  It is
    below each of those [S]s, so by down-closure it is in each
    [P i].  One element, built from [c], serves every row.

    That is Lemma 1 of Fawcett and Wood made concrete: the witness
    is _manufactured_ from data at hand, not _chosen_ from a
    family of candidates. *)

(* ================================================================ *)
(** ** The same trick, twice more *)

(** Choice used to enter the development in two more places.
    Both are fixed by the same move.

    _The normal form._ Every element of a free completely
    distributive lattice is a [sup] of [inf]s of generators.
    Classically one builds the free lattice as [upset (downset
    C)], where the obvious normal form is the other way round, an
    [inf] of [sup]s, and flips it with the classical law.  That
    flip is a use of choice.

    [IntSpec.v] builds it as [downset (upset C)] instead.  An
    upset [A] of plays names the meet [inf {c | c in A}, c], and
    an element of the lattice is _literally_ a down-closed set of
    such meets.  So the [sup]-of-[inf]s normal form holds by
    construction: *)

Check FCD.join_meet_dense.
(* ===> x = sup {A | Downset.has x A},
              gen (fun c => FCD.emb c) A *)

(** _Extension preserves [inf]._ The universal property of a free
    lattice says a monotone map [f] from plays into any
    [ccdlattice] [L] extends to a map [FCD.ext f] that preserves
    all [sup]s and all [inf]s.  The hard half is [inf].  In the
    proof of [FCD.ext_inf] we arrive, for some [y], at

      forall i, exists A, A in x i  /\  y [= gen f A

    and need a single upset that lies in every [x i].  Classically
    you choose an [A] for each [i].  The proof instead takes

      wit f y  :=  {c | y [= f c}

    which depends only on [y].  Each chosen [A] would have been
    contained in [wit f y], and since the order on upsets is
    reverse inclusion, down-closure of [x i] puts [wit f y] in
    every [x i].  Again one element, computed, not chosen.

    ([PProd.poke] does the same job for products of lattices:
    "be [y] at index [a], [bot] elsewhere" is a single witness that
    works for every member of a family.)

    That is the whole story of choice.  It entered through one
    law, and every use of that law has been replaced by a uniform
    witness. *)

(* ################################################################ *)
(** * Part II: Where Excluded Middle Stays *)

(* ================================================================ *)
(** ** The dual law *)

(** Classically, complete distributivity is self-dual: if [inf]
    distributes over [sup], then [sup] distributes over [inf].  We
    only need the smallest piece of the dual, a binary join going
    past an infinite meet: *)

Print codistributive.
(* ===> fun L => forall I (a : L) (x : I -> L),
          inf i, (a || x i) [= a || inf i, x i *)

(** The other inclusion always holds ([join_inf_le]).  The finite
    case also holds: [codist_meet] proves it for a binary meet.

    In a downset lattice, being in [a || b] means being in [a] or
    being in [b], and being in [inf i, x i] means being in every
    [x i].  So the codistributive inclusion, at a point [c], says

      (forall i, c in a  \/  c in x i)
        ->  c in a  \/  (forall i, c in x i)

    You can move a [forall] past an [\/] whose left side does not
    mention [i].  Classically this is trivial: either [c in a] or
    not, and if not, every [c in x i] holds.  Constructively that
    "either or not" is the whole content.

    In [Omega] this is plain to see.  Take the index set to be a
    proposition [P] itself, [a] to be [P], and every [x i] to be
    [False]: the hypothesis is [P -> P \/ False], which is free,
    and the conclusion is [P \/ (P -> False)]. *)

(** **** Exercise: 2 stars, standard (codist_Omega_lem)

    Prove that codistributivity of [Omega] gives excluded middle.
    Do it directly, without [codist_lem].  The lemmas
    [Downset.has_linf], [has_join] and [has_bot] are useful. *)

Theorem codist_Omega_lem : codistributive Omega -> lem.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [IntSpec.v] proves the same for every downset lattice over an
    inhabited poset ([codist_lem]), and the converse
    ([lem_codist]).  For interaction specifications: *)

Check codist_t_iff.
(* ===> codistributive (ISpec.t E V) <-> lem *)

(** Note what the trick of Part I cannot do here.  It replaced a
    _function_ that had to be chosen with an _element_ that could
    be built.  Codistributivity does not ask for a function.  It
    asks for a _decision_, whether [c in a], and no witness,
    however cleverly built, decides a proposition. *)

(* ================================================================ *)
(** ** Where [bind] meets the dual law *)

(** Here is [bind], defined on a single play and then extended to
    all specifications by [ext]: *)

Print ISpec.pbind.
(* ===> fix pbind f p :=
          match p with
          | pret a => f a
          | pmove m => emb (pmove m)
          | pcons m n q => emb (pmove m) || pcext m n (pbind f q)
          end *)

(** The last clause is the one to watch.  When the play asked
    [m] and got [n], the result is "the computation may stop right
    after asking [m]" joined with "after [m] and [n], continue as
    [pbind f q]".  The first disjunct, [emb (pmove m)], keeps the
    record that [m] was asked, whatever the continuation does.

    Now associate two binds to the left.  On a [pcons] play the
    left bracketing produces, writing [e] for [emb (pmove m)] and
    [z] for the specification [pbind f q],

      e  ||  ext (fun s => e || pcext m n (pbind g s)) z

    while the right bracketing produces

      e  ||  ext (fun s =>      pcext m n (pbind g s)) z

    They differ by one copy of [e], sitting inside [ext] on the
    left.  To get rid of it we need to pull it outside.  But [ext]
    is a [sup] of [inf]s, and pulling [e] out of the [inf]s is
    the codistributive inclusion, with [a := e].  That is the
    proof of [ISpec.join_ext_absorb], and the reason [bind_bind]
    has a [codistributive] hypothesis.

    Only one direction is stuck.  [bind_bind_le] proves the other
    with no hypothesis at all. *)

Check ISpec.bind_bind.
(* ===> codistributive (t E C) ->
        bind g (bind f x) = bind (fun a => bind g (f a)) x *)

Check bind_bind_lem.
(* ===> lem -> bind g (bind f x) = ... *)

(* ================================================================ *)
(** ** Is the hypothesis really needed? *)

(** So far we know that _this proof_ of [bind_bind] needs excluded
    middle.  A cleverer proof might not.  The rest of the chapter
    shows that no proof can do without it: associativity of
    [bind] for interaction specifications implies excluded middle.

    The idea is to make the copy of [e] that gets stuck depend on
    an arbitrary proposition [P].  Fix a move [m] with an answer
    [n], and take

    - [x], the single play "ask [m], get [n], return [a]";

    - [f _ := inf _ : P, ret b], a demonic choice indexed by
      proofs of [P].  If [P] holds this is [ret b].  If [P] is
      false the demon has no options, and an empty [inf] is
      [top];

    - [g _ := bot], the continuation that does nothing.

    Work out both bracketings by hand.

    _Left_.  [bind f x] is [e || pcext m n (inf _ : P, ret b)].
    Binding [g] onto it pushes [g] under the [inf].  For each
    proof of [P] we get [pbind g (pcons m n (pret b))], which is
    [e || pcext m n bot], which is [e].  So the left side is

      inf _ : P, e            "if P, then the trace m"

    (plus an outer [e], which is below this and changes nothing).

    _Right_.  [bind g (f a)] is [inf _ : P, bot], since [g] wipes
    out [ret b].  Prefixing it with [m, n] and adding the record
    of [m] gives

      e || inf _ : P, bot     "the trace m, or else not P"

    Classically both sides mean "if [P] then [e] else [top]".
    Constructively the left side is weaker: it says [e] is
    available given a proof of [P], while the right side asks for
    [e] outright _or_ a refutation of [P].  Equating them decides
    [P].

    Here is the right side as a lemma. *)

Import ISpec.

(** **** Exercise: 3 stars, standard (rhs_compute)

    Compute the right bracketing.  You will want [bind_emb],
    [Inf.mor] (both [bind _] and [pcext m n] preserve [inf]s),
    [bind_ret_r] and [Sup.mor_bot]. *)

Lemma rhs_compute {E X A B C} (m : E X) (n : X) (a : A) (b : B)
      (P : Prop) :
  bind (fun a => bind (fun _ => bot : t E C)
                      (inf _ : P, ret b))
       (emb (pcons m n (pret a))) =
  emb (pmove m) || (inf _ : P, bot).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** To turn "equating them decides [P]" into a proof, we need an
    element of the lattice that lies below the left side, and
    lies below the right side only if [P \/ ~ P].  [IntSpec.v]
    already has one.  The upset

      pguard (pmove m) P  :=  {d | P /\ pmove m [= d}

    names a meet of plays that is guarded by [P].  It lies below
    [e] exactly when [P] holds ([has_emb_pguard]).  So it lies
    below [inf _ : P, e], trivially; and it lies below
    [e || inf _ : P, bot] exactly when [P \/ ~ P]. *)

Theorem bind_bind_implies_lem {E X A B C}
        (m : E X) (n : X) (a : A) (b : B) :
  (forall (g : B -> t E C) (f : A -> t E B) (x : t E A),
      bind g (bind f x) = bind (fun a => bind g (f a)) x) ->
  lem.
Proof.
  intros H P.
  set (e := emb (pmove m) : t E C).
  set (U := pguard (pmove m : play_poset E C) P).
  specialize (H (fun _ => bot) (fun _ => inf _ : P, ret b)
                (emb (pcons m n (pret a)))).
  rewrite !bind_emb in H. cbn [pbind] in H.
  (* The left side lies above [inf _ : P, e]. *)
  assert (HL : (inf _ : P, e) [= bind (fun _ => bot)
                 (emb (pmove m) || pcext m n (inf _ : P, ret b))).
  { rewrite (Sup.mor_join (bind _)).
    apply join_r.
    rewrite (Inf.mor (f := pcext m n)), (Inf.mor (f := bind _)).
    apply inf_glb. intros HP. apply (inf_at HP).
    unfold ret. rewrite pcext_emb, bind_emb. cbn [pbind].
    apply join_ub_l. }
  (* [U] is in [inf _ : P, e], hence in the left side, hence in
     the right side. *)
  assert (HU : Downset.has (inf _ : P, e) U).
  { apply Downset.has_linf. intros HP.
    apply has_emb_pguard. exact HP. }
  apply HL in HU. rewrite H in HU.
  (* Being in a join is a disjunction: here it is [P \/ ~ P]. *)
  apply has_join in HU as [HU | HU].
  - left. exact (proj1 (has_emb_pguard _ P) HU).
  - right. intros HP.
    assert (Hb : pcext m n (bind (fun _ => bot : t E C)
                                 (inf _ : P, ret b)) [= bot).
    { etransitivity.
      - apply pmor. apply pmor. apply (inf_lb HP).
      - rewrite bind_ret_r, (Sup.mor_bot (pcext m n)).
        reflexivity. }
    apply Hb in HU. exact (proj1 (has_bot _) HU).
Qed.

(** Putting the two directions together: for any signature with
    at least one answered move, associativity of [bind] is
    equivalent to excluded middle. *)

Corollary bind_bind_iff_lem {E X A B C}
          (m : E X) (n : X) (a : A) (b : B) :
  (forall (g : B -> t E C) (f : A -> t E B) (x : t E A),
      bind g (bind f x) = bind (fun a => bind g (f a)) x) <->
  lem.
Proof.
  split.
  - exact (bind_bind_implies_lem m n a b).
  - intros Hlem g f x. apply bind_bind_lem. exact Hlem.
Qed.

Print Assumptions bind_bind_iff_lem.
(* ===> propositional_extensionality,
        functional_extensionality_dep *)

(* ================================================================ *)
(** ** What the counterexample is made of *)

(** Look again at what went into it.  Two ingredients, and both
    are essential.

    _A demonic choice indexed by a proposition._ [inf _ : P, ...]
    is a perfectly good element of [t E B]: [inf] is allowed over
    any index type, propositions included.  It means "if [P]".
    This is the copy of [Omega] that lives inside every
    interaction specification lattice, and the reason
    [fcd_unique] in [IntSpec.v] matters: [ISpec.t] is _the_ free
    completely distributive lattice, so any other presentation
    contains the same copy of [Omega] and fails the same way.  You
    cannot fix [bind_bind] by building the lattice differently.

    _A record that survives [bot]._ The clause
    [emb (pmove m) || ...] in [pbind] keeps the trace [m] even
    when everything after it is [bot].  That is what produced two
    copies of [e], one inside the "if [P]" and one outside it.
    Thesis section 5.3.3 identifies silent divergence with a
    global [bot]; this record is the shadow of that choice.

    Take away either ingredient and the obstruction goes away.
    The [IRun] module at the end of [IntSpec.v] drops the demonic
    side, so there is no [inf] to index by a proposition, and
    there composition of layers is associative with no axioms at
    all ([IRun.rcompose_assoc]).

    So the honest summary is this.  Choice was never needed; it
    was an artifact of how complete distributivity was written
    down.  Excluded middle is needed; it is part of what
    [bind_bind] says, once demonic choice can range over
    propositions. *)

(* ################################################################ *)
(** * Summary *)

(** - [classical_cd] for [Omega] is [AC] ([classical_cd_AC]).

    - Restricted to down-closed rows, the law needs only constant
      choice functions, i.e. elements.  [IntSpec.v] takes this as
      its axiom ([ccd]), and every downset lattice satisfies it
      ([Downset.dccd]) with the witness [emb c].

    - The other two uses of choice, the normal form and
      [FCD.ext_inf], fall to the same move: [downset (upset C)]
      and the witness [FCD.wit].

    - The dual law, [codistributive], is excluded middle
      ([codist_t_iff]).  It asks for a decision, and a witness
      cannot supply one.

    - [bind_bind] needs the dual law because [pbind] joins
      [emb (pmove m)] onto its recursive call, and that join must
      cross the [inf]s of [ext].

    - And it really needs it: [bind_bind_iff_lem]. *)

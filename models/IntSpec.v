(** * Constructive interaction specifications

  This develops the interaction specification monad without
  classical reasoning.  The only axioms used are functional and
  propositional extensionality; in particular there is no appeal to
  excluded middle, to any form of the axiom of choice, or to
  Markov's principle.  Every result below can be checked with
  [Print Assumptions].

  Because the lattice layer this file used to rest on is classical
  throughout -- [lattices.Downset] requires [Classical] and
  [ClassicalChoice], and the [cdlattice] record of
  [structures.Lattice] builds in the choice-equivalent
  distributivity law discussed next -- the development here is
  self-contained.  It rebuilds posets, completely distributive
  lattices and the free such lattice from scratch, and depends only
  on the two extensionality axioms of the standard library.

  A handful of laws are proved relative to one named lattice
  principle, [codistributive], rather than outright.  That principle
  is pinned down exactly: for these lattices it is equivalent to
  excluded middle ([lem_codist], [codist_lem], [codist_t_iff]).  So
  the residual classical content is excluded middle alone - the
  choice that the original development needed is gone.

  The classical development is organized around the notion of a
  completely distributive lattice, formulated as the equation

    [sup i, inf j, x i j  =  inf f, sup i, x i (f i)]

  quantifying over all choice functions [f].  As Fawcett and Wood
  observe (/Constructive complete distributivity I/, Math. Proc.
  Camb. Phil. Soc. 107 (1990) 81-89), that equation is not merely
  unprovable without the axiom of choice: for powersets it is
  *equivalent* to it (their Theorem 6).  Accordingly the classical
  file inherits [Classical_Prop.classic] and the admitted
  [Lattice.inf_sup] through its lattice foundation.

  Fawcett and Wood propose instead to take as the definition of
  complete distributivity the existence of a left adjoint to
  [sup : D L -> L], where [D L] is the lattice of down-closed
  subsets of [L] (their Theorem 2).  They call this *constructive*
  complete distributivity, (CCD).  Their Lemma 1 is the key
  computational fact: when the inner families are down-closed, the
  right-hand side of the distributivity equation only needs the
  *constant* choice functions, so no choice is required.  We use the
  resulting equation

    [inf i, sup {x | P i x}, x  =  sup {x | forall i, P i x}, x]
      (each [P i] down-closed)

  as our primitive, and we recover the usual sup-of-infs normal form
  from it.

  Their Theorem 3 - [D X] is (CCD) for every ordered set [X], with
  no choice - is what makes the whole file go through.  It also
  dictates one concrete change of representation: the classical file
  builds the free completely distributive lattice over a poset [C]
  as [upset (downset C)], and both [upset] and the derived
  sup-of-infs normal form [join_meet_dense] then need choice.  Here
  we build it as [downset (upset C)] instead.  Classically the two
  agree; constructively only the outer [downset] is known to be
  (CCD) - the dual statement is Fawcett and Wood's Theorem 18, which
  they flag with an obelisk as requiring the ambient topos to be
  Boolean.  With this orientation the sup-of-infs normal form holds
  by construction, and the lemmas that previously destructed
  [FCD.join_meet_dense] become choice-free.

  Three laws about applying a substitution ([ISpec.apply_int_r],
  [ISpec.apply_bind], [ISpec.apply_assoc]) are still admitted, as
  they were classically; what has changed is that we can now say
  precisely what blocks them.  [ISpec.apply] is a *nested* pair of
  [FCD.ext]s, and exchanging them has to move an [inf] past a [join]
  -- codistributivity, hence excluded middle.  The [IRun] module at
  the end of the file shows the obstruction is this nesting and not
  interaction itself: dropping the demonic side, so that the lattice
  is a plain [Downset.F] and substitution is a *single*
  sup-extension over an inductively generated relation on
  interaction sequences, makes layer composition a category outright
  -- [IRun.rcompose_assoc], [IRun.rcompose_rid_l] and
  [IRun.rcompose_rid_r], each depending on nothing but the two
  extensionality axioms.

  [IRun] also settles why that does not simply lift back to the
  demonic side.  Its interaction relation [IRun.runs] is indexed by
  a family of predicates rather than by a substitution, which lets
  the two halves of associativity be weighed separately: the easy
  inclusion [IRun.runs_scompose_fwd] assumes nothing at all about
  the families, while the other, [IRun.runs_scompose_bwd], needs
  them downward closed -- and [IRun.scompose_bwd_needs_dcl] exhibits
  up-closed families, the shape a demonic bundle has, for which it
  is false.  So the missing ingredient is not the flattening law
  [inf_sup], which holds constructively and is never needed; it is
  the global [bot] of thesis section 5.3.3, the same thing that
  blocks [ISpec.bind_bind]. *)
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Morphisms.
From Stdlib Require Import Setoid.


(** * Preliminaries *)

(** ** Uniqueness of identity proofs

  Propositional extensionality gives us proof irrelevance, hence
  UIP, hence injectivity of [existT] on its second component.  We
  need the latter to reason about plays, whose moves are indexed by
  their arity. *)

Definition proof_irrel := PropExtensionality.proof_irrelevance.

Definition projT1_eq {U} {P : U -> Type} {s t : sigT P} (H : s = t) :
  projT1 s = projT1 t :=
  f_equal (@projT1 U P) H.

Definition projT2_eq {U} {P : U -> Type} {s t : sigT P} (H : s = t) :
  eq_rect (projT1 s) P (projT2 s) (projT1 t) (projT1_eq H) = projT2 t.
Proof.
  destruct H. reflexivity.
Defined.

Lemma inj_pair2 {U} {P : U -> Type} {p : U} {x y : P p} :
  existT P p x = existT P p y -> x = y.
Proof.
  intros H.
  pose proof (projT2_eq H) as E. cbn in E.
  rewrite (proof_irrel _ (projT1_eq H) (eq_refl p)) in E.
  exact E.
Qed.

(** ** Rewriting under binders

  The following instance enables rewriting under the binders of
  infinitary operations like [sup] and [inf]. *)

Global Instance bigop_eq {I A B} (f : (I -> A) -> B) :
  Proper (pointwise_relation I eq ==> eq) f.
Proof.
  intros x y Hxy.
  apply functional_extensionality in Hxy.
  congruence.
Qed.


(** * Posets *)

Record poset :=
  {
    poset_carrier :> Type;
    ref : poset_carrier -> poset_carrier -> Prop;
    ref_refl x : ref x x;
    ref_trans x y z : ref x y -> ref y z -> ref x z;
    ref_antisym x y : ref x y -> ref y x -> x = y;
  }.

Arguments ref {_}.
Infix "[=" := ref (at level 70).

Global Instance ref_preo (C : poset) : PreOrder (@ref C).
Proof.
  split.
  - intros x. apply ref_refl.
  - intros x y z. apply ref_trans.
Qed.

Global Instance ref_antisym_inst (C : poset) : Antisymmetric C eq (@ref C).
Proof.
  intros x y. apply ref_antisym.
Qed.

Class PosetMorphism {C D : poset} (f : C -> D) :=
  pmor : forall x y, x [= y -> f x [= f y.

Global Instance pmor_proper {C D : poset} (f : C -> D) `{!PosetMorphism f} :
  Proper (ref ++> ref) f.
Proof.
  intros x y. apply pmor.
Qed.

(** Down-closed and up-closed predicates on a poset.  These are the
  subsets Fawcett and Wood write [D X] and [U X]. *)

Definition dcl {C : poset} (P : C -> Prop) :=
  forall x y, x [= y -> P y -> P x.

Definition ucl {C : poset} (P : C -> Prop) :=
  forall x y, x [= y -> P x -> P y.


(** * Constructively completely distributive lattices *)

(** A complete lattice which is (CCD) in the sense of Fawcett and
  Wood.  The field [ccd] is their distributivity equation as
  simplified by their Lemma 1: an [inf] of [sup]s of down-closed
  families is the [sup] of the intersection of those families.  Only
  constant choice functions occur, so the equation is choice-free,
  and by their Theorem 2 it is equivalent to the existence of the
  left adjoint [way_below] below. *)

Record ccdlattice :=
  {
    ccdl_poset :> poset;

    lsup : forall {I}, (I -> ccdl_poset) -> ccdl_poset;
    linf : forall {I}, (I -> ccdl_poset) -> ccdl_poset;

    sup_ub {I} (i : I) (x : I -> ccdl_poset) :
      x i [= lsup x;
    sup_lub {I} (x : I -> ccdl_poset) (y : ccdl_poset) :
      (forall i, x i [= y) -> lsup x [= y;

    inf_lb {I} (i : I) (x : I -> ccdl_poset) :
      linf x [= x i;
    inf_glb {I} (x : ccdl_poset) (y : I -> ccdl_poset) :
      (forall i, x [= y i) -> x [= linf y;

    ccd {I} (P : I -> ccdl_poset -> Prop) :
      (forall i, dcl (P i)) ->
      linf (fun i => lsup (fun z : sig (P i) => proj1_sig z)) =
      lsup (fun z : sig (fun y => forall i, P i y) => proj1_sig z);
  }.

Arguments lsup {_ _}.
Arguments linf {_ _}.
Arguments sup_ub {_ _}.
Arguments sup_lub {_ _}.
Arguments inf_lb {_ _}.
Arguments inf_glb {_ _}.

Notation "'sup' i .. j , M" := (lsup (fun i => .. (lsup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

Notation "'inf' i .. j , M" := (linf (fun i => .. (linf (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

(** ** Extrema over a predicate *)

Definition fsup {L : ccdlattice} {I} (P : I -> Prop) (f : I -> L) :=
  lsup (I := sig P) (fun z => f (proj1_sig z)).

Definition finf {L : ccdlattice} {I} (P : I -> Prop) (f : I -> L) :=
  linf (I := sig P) (fun z => f (proj1_sig z)).

Notation "'sup' { x | P } , M" :=
  (fsup (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'sup' { x : A | P } , M" :=
  (fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).

Notation "'inf' { x | P } , M" :=
  (finf (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'inf' { x : A | P } , M" :=
  (finf (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).

Section PROPERTIES.
  Context {L : ccdlattice}.

  Lemma sup_at {I} (i : I) (x : L) (y : I -> L) :
    x [= y i -> x [= sup i, y i.
  Proof.
    intros H. etransitivity; eauto. apply sup_ub.
  Qed.

  Lemma inf_at {I} (i : I) (x : I -> L) (y : L) :
    x i [= y -> inf i, x i [= y.
  Proof.
    intros H. etransitivity; eauto. apply inf_lb.
  Qed.

  Lemma sup_iff {I} (x : I -> L) (y : L) :
    lsup x [= y <-> forall i, x i [= y.
  Proof.
    split.
    - intros H i. etransitivity; eauto. apply sup_ub.
    - apply sup_lub.
  Qed.

  Lemma inf_iff {I} (x : L) (y : I -> L) :
    x [= linf y <-> forall i, x [= y i.
  Proof.
    split.
    - intros H i. etransitivity; eauto. apply inf_lb.
    - apply inf_glb.
  Qed.

  Lemma fsup_ub {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> x i [= fsup P x.
  Proof.
    intros Hi. apply (sup_ub (exist P i Hi) (fun z => x (proj1_sig z))).
  Qed.

  Lemma fsup_at {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    P i -> x [= y i -> x [= fsup P y.
  Proof.
    intros Hi Hx. etransitivity; eauto using fsup_ub.
  Qed.

  Lemma fsup_lub {I} (P : I -> Prop) (x : I -> L) (y : L) :
    (forall i, P i -> x i [= y) -> fsup P x [= y.
  Proof.
    intros Hy. apply sup_lub. intros [i Hi]. auto.
  Qed.

  Lemma finf_lb {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> finf P x [= x i.
  Proof.
    intros Hi. apply (inf_lb (exist P i Hi) (fun z => x (proj1_sig z))).
  Qed.

  Lemma finf_at {I} (i : I) (P : I -> Prop) (x : I -> L) (y : L) :
    P i -> x i [= y -> finf P x [= y.
  Proof.
    intros Hi Hy. etransitivity; eauto using finf_lb.
  Qed.

  Lemma finf_glb {I} (P : I -> Prop) (x : L) (y : I -> L) :
    (forall i, P i -> x [= y i) -> x [= finf P y.
  Proof.
    intros Hy. apply inf_glb. intros [i Hi]. auto.
  Qed.
End PROPERTIES.

(** ** Constructive distributivity *)

Section DISTRIBUTIVITY.
  Context {L : ccdlattice}.

  (** The lattice axiom, restated with our notations.  This is
    Fawcett and Wood's (CCD) equation after the simplification of
    their Lemma 1. *)

  Lemma inf_sup_dcl {I} (P : I -> L -> Prop) :
    (forall i, dcl (P i)) ->
    inf i, (sup {x | P i x}, x) = sup {x | forall i, P i x}, x.
  Proof.
    intros H. exact (ccd L P H).
  Qed.

  (** Every [sup] is the [sup] of a down-closed family, namely of the
    down-closure of its own image.  This lets us apply the axiom
    above to arbitrary families. *)

  Lemma sup_dcl {I} (x : I -> L) :
    sup {y | exists i, y [= x i}, y = sup i, x i.
  Proof.
    apply antisymmetry.
    - apply fsup_lub. intros y [i Hi]. apply (sup_at i). assumption.
    - apply sup_lub. intros i. apply (fsup_at (x i)).
      + exists i. reflexivity.
      + reflexivity.
  Qed.

  (** The constructive replacement for the classical law

      [inf i, sup j, x i j = sup f, inf i, x i (f i)],

    which quantifies over all choice functions [f] and which, for
    powersets, is equivalent to the axiom of choice (Fawcett and
    Wood, Theorem 6).  Here the right-hand side instead ranges over
    the elements [y] which lie below some [x i j] for every [i]:
    by their Lemma 1 only the constant choice functions are needed,
    and the equation becomes choice-free.

    The classical law follows from this one in the presence of
    choice, by turning a family [fun i => exists j, y [= x i j] into
    a function; we never do that. *)

  Lemma inf_sup {I} {J : I -> Type} (x : forall i, J i -> L) :
    inf i, sup j, x i j = sup {y | forall i, exists j, y [= x i j}, y.
  Proof.
    transitivity (inf i, (sup {y | exists j, y [= x i j}, y)).
    - f_equal. apply functional_extensionality. intros i.
      symmetry. apply sup_dcl.
    - apply inf_sup_dcl.
      intros i y z Hyz [j Hj]. exists j. etransitivity; eauto.
  Qed.
End DISTRIBUTIVITY.

(** ** Derived operations

  Unlike in the classical development, all of the properties below
  are proved; none of them needs distributivity. *)

Section OPS.
  Context {L : ccdlattice}.

  Definition bot : L :=
    sup i : Empty_set, match i with end.

  Lemma bot_lb (x : L) :
    bot [= x.
  Proof.
    apply sup_lub. intros [ ].
  Qed.

  Definition top : L :=
    inf i : Empty_set, match i with end.

  Lemma top_ub (x : L) :
    x [= top.
  Proof.
    apply inf_glb. intros [ ].
  Qed.

  Definition join (x y : L) : L :=
    sup b : bool, if b then x else y.

  Lemma join_ub_l (x y : L) : x [= join x y.
  Proof. apply (sup_ub true (fun b : bool => if b then x else y)). Qed.

  Lemma join_ub_r (x y : L) : y [= join x y.
  Proof. apply (sup_ub false (fun b : bool => if b then x else y)). Qed.

  Lemma join_lub (x y z : L) : x [= z -> y [= z -> join x y [= z.
  Proof. intros. apply sup_lub. intros [|]; auto. Qed.

  Lemma join_l (x y z : L) : x [= y -> x [= join y z.
  Proof. intro. etransitivity; eauto using join_ub_l. Qed.

  Lemma join_r (x y z : L) : x [= z -> x [= join y z.
  Proof. intro. etransitivity; eauto using join_ub_r. Qed.

  Lemma ref_join (x y : L) : x [= y <-> join x y = y.
  Proof.
    split; intro H.
    - apply antisymmetry.
      + apply join_lub; auto. reflexivity.
      + apply join_ub_r.
    - rewrite <- H. apply join_ub_l.
  Qed.

  Definition meet (x y : L) : L :=
    inf b : bool, if b then x else y.

  Lemma meet_lb_l (x y : L) : meet x y [= x.
  Proof. apply (inf_lb true (fun b : bool => if b then x else y)). Qed.

  Lemma meet_lb_r (x y : L) : meet x y [= y.
  Proof. apply (inf_lb false (fun b : bool => if b then x else y)). Qed.

  Lemma meet_glb (x y z : L) : x [= y -> x [= z -> x [= meet y z.
  Proof. intros. apply inf_glb. intros [|]; auto. Qed.

  Lemma join_bot_l (x : L) : join bot x = x.
  Proof.
    apply antisymmetry.
    - apply join_lub. apply bot_lb. reflexivity.
    - apply join_ub_r.
  Qed.
End OPS.

Infix "||" := join (at level 50, left associativity).
Infix "&&" := meet (at level 40, left associativity).

(** * Least fixed points

  An interaction specification lattice is a complete lattice, so
  Knaster-Tarski applies and every monotonic endo-map has a least
  fixed point, computed as the [inf] of its pre-fixed points.  This
  needs no choice, no excluded middle, and no continuity: in
  particular recursion and non-termination are available, and a
  divergent computation is not [bot] -- see [ISpec.repeat]. *)

Section FIXPOINTS.
  Context {L : ccdlattice}.

  Definition lfp (F : L -> L) : L :=
    inf {x | F x [= x}, x.

  Lemma lfp_least (F : L -> L) (x : L) :
    F x [= x -> lfp F [= x.
  Proof.
    intros H. apply (finf_lb x). assumption.
  Qed.

  Lemma lfp_pre (F : L -> L) `{HF : !PosetMorphism F} :
    F (lfp F) [= lfp F.
  Proof.
    apply finf_glb. intros x Hx. etransitivity.
    - apply (HF (lfp F) x). apply (lfp_least F x Hx).
    - assumption.
  Qed.

  Lemma lfp_fixed (F : L -> L) `{HF : !PosetMorphism F} :
    F (lfp F) = lfp F.
  Proof.
    apply antisymmetry.
    - exact (lfp_pre F).
    - apply lfp_least. apply (HF (F (lfp F)) (lfp F)). exact (lfp_pre F).
  Qed.
End FIXPOINTS.


(** * Lattice morphisms *)

Module Sup.
  Class Morphism {L M : ccdlattice} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (lsup x) = sup i, f (x i).

  Lemma mor_join {L M : ccdlattice} (f : L -> M) `{!Morphism f} x y :
    f (x || y) = f x || f y.
  Proof.
    unfold join. rewrite (mor (f := f)). f_equal.
    apply functional_extensionality. intros [|]; reflexivity.
  Qed.

  Lemma mor_bot {L M : ccdlattice} (f : L -> M) `{!Morphism f} :
    f bot = bot.
  Proof.
    unfold bot. rewrite (mor (f := f)).
    apply antisymmetry; apply sup_lub; intros [ ].
  Qed.

  Lemma mor_fsup {L M : ccdlattice} (f : L -> M) `{!Morphism f}
        {I} (P : I -> Prop) (x : I -> L) :
    f (fsup P x) = fsup P (fun i => f (x i)).
  Proof.
    unfold fsup. rewrite (mor (f := f)). reflexivity.
  Qed.

  Lemma mor_ref {L M : ccdlattice} (f : L -> M) :
    Morphism f -> PosetMorphism f.
  Proof.
    intros Hf x y Hxy.
    apply ref_join in Hxy. rewrite <- Hxy.
    rewrite (@mor_join L M f Hf x y).
    apply join_ub_l.
  Qed.
End Sup.

Module Inf.
  Class Morphism {L M : ccdlattice} (f : L -> M) :=
    mor : forall {I} (x : I -> L), f (linf x) = inf i, f (x i).

  Lemma mor_finf {L M : ccdlattice} (f : L -> M) `{!Morphism f}
        {I} (P : I -> Prop) (x : I -> L) :
    f (finf P x) = finf P (fun i => f (x i)).
  Proof.
    unfold finf. rewrite (mor (f := f)). reflexivity.
  Qed.
End Inf.

Module CDL.
  Class Morphism {L M : ccdlattice} (f : L -> M) :=
    {
      cmor_sup : Sup.Morphism f;
      cmor_inf : Inf.Morphism f;
    }.

  Global Existing Instance cmor_sup.
  Global Existing Instance cmor_inf.

  Lemma id_mor (L : ccdlattice) : Morphism (fun x : L => x).
  Proof.
    split; red; reflexivity.
  Qed.

  Lemma compose_mor {A B C : ccdlattice} (g : B -> C) (f : A -> B) :
    Morphism f -> Morphism g -> Morphism (fun a => g (f a)).
  Proof.
    intros Hf Hg. split.
    - red. intros I x.
      rewrite (Sup.mor (f := f)), (Sup.mor (f := g)). reflexivity.
    - red. intros I x.
      rewrite (Inf.mor (f := f)), (Inf.mor (f := g)). reflexivity.
  Qed.

  Global Instance mor_ref {L M : ccdlattice} (f : L -> M) :
    Morphism f -> PosetMorphism f.
  Proof.
    intros [Hs _]. apply Sup.mor_ref. exact Hs.
  Qed.
End CDL.


(** * Downsets

  The lattice of down-closed subsets of a poset.  By Fawcett and
  Wood's Theorem 3 it is (CCD) for every poset, with no appeal to
  choice; this is the only lattice we construct, and everything else
  is built from it. *)

Module Downset.

  Record downset (C : poset) :=
    {
      has : C -> Prop;
      has_closed : dcl has;
    }.

  Arguments has {C}.
  Arguments has_closed {C}.

  Lemma has_eq {C} (x y : downset C) :
    (forall c, has x c <-> has y c) -> x = y.
  Proof.
    intros H. destruct x as [p Hp], y as [q Hq]. cbn in H.
    assert (p = q) as Hpq.
    {
      apply functional_extensionality. intros c.
      apply propositional_extensionality. apply H.
    }
    destruct Hpq. f_equal. apply proof_irrel.
  Qed.

  (** ** Partial order *)

  Definition dref {C} (x y : downset C) :=
    forall c, has x c -> has y c.

  Lemma dref_refl {C} (x : downset C) : dref x x.
  Proof. firstorder. Qed.

  Lemma dref_trans {C} (x y z : downset C) :
    dref x y -> dref y z -> dref x z.
  Proof. firstorder. Qed.

  Lemma dref_antisym {C} (x y : downset C) :
    dref x y -> dref y x -> x = y.
  Proof. intros Hxy Hyx. apply has_eq. firstorder. Qed.

  Definition Fpos (C : poset) : poset :=
    {|
      poset_carrier := downset C;
      ref := @dref C;
      ref_refl := @dref_refl C;
      ref_trans := @dref_trans C;
      ref_antisym := @dref_antisym C;
    |}.

  (** ** Extrema *)

  Lemma dsup_closed {C I} (x : I -> downset C) :
    dcl (fun c => exists i, has (x i) c).
  Proof.
    intros a b Hab [i Hi]. exists i. eapply has_closed; eauto.
  Qed.

  Definition dsup {C I} (x : I -> downset C) : downset C :=
    {| has c := exists i, has (x i) c; has_closed := dsup_closed x |}.

  Lemma dinf_closed {C I} (x : I -> downset C) :
    dcl (fun c => forall i, has (x i) c).
  Proof.
    intros a b Hab Hb i. eapply has_closed; eauto.
  Qed.

  Definition dinf {C I} (x : I -> downset C) : downset C :=
    {| has c := forall i, has (x i) c; has_closed := dinf_closed x |}.

  Lemma dsup_ub {C I} (i : I) (x : I -> downset C) : dref (x i) (dsup x).
  Proof. intros c Hc. exists i. assumption. Qed.

  Lemma dsup_lub {C I} (x : I -> downset C) (y : downset C) :
    (forall i, dref (x i) y) -> dref (dsup x) y.
  Proof. intros H c [i Hi]. eapply H; eauto. Qed.

  Lemma dinf_lb {C I} (i : I) (x : I -> downset C) : dref (dinf x) (x i).
  Proof. intros c Hc. apply Hc. Qed.

  Lemma dinf_glb {C I} (x : downset C) (y : I -> downset C) :
    (forall i, dref x (y i)) -> dref x (dinf y).
  Proof. intros H c Hc i. eapply H; eauto. Qed.

  (** ** The embedding *)

  Lemma emb_closed {C : poset} (c : C) : dcl (fun d : C => d [= c).
  Proof. intros a b Hab Hb. etransitivity; eauto. Qed.

  Definition emb {C : poset} (c : C) : downset C :=
    {| has d := d [= c; has_closed := emb_closed c |}.

  (** ** Constructive complete distributivity

    This is Fawcett and Wood's Theorem 3.  Their Lemma 1 is the
    observation that the element witnessing the inclusion can be
    taken to be the same for every member of the family - i.e. that
    only *constant* choice functions are needed.  Here that witness
    is the principal downset [emb c], which is manufactured from the
    element [c] at hand rather than chosen. *)

  Lemma dccd {C I} (P : I -> Fpos C -> Prop) :
    (forall i, dcl (P i)) ->
    dinf (fun i => dsup (fun z : sig (P i) => proj1_sig z)) =
    dsup (fun z : sig (fun y => forall i, P i y) => proj1_sig z).
  Proof.
    intros HP. apply has_eq. intros c. cbn. split.
    - intros H.
      assert (forall i, P i (emb c)) as Hc.
      {
        intros i. destruct (H i) as [[S HS] Hi]. cbn in Hi.
        refine (HP i (emb c) S _ HS).
        intros d Hd. cbn in Hd. exact (has_closed S d c Hd Hi).
      }
      exists (exist _ (emb c) Hc). cbn. reflexivity.
    - intros [[S HS] Hc] i. cbn in *.
      exists (exist _ S (HS i)). cbn. assumption.
  Qed.

  Definition F (C : poset) : ccdlattice :=
    {|
      ccdl_poset := Fpos C;
      lsup := @dsup C;
      linf := @dinf C;
      sup_ub := @dsup_ub C;
      sup_lub := @dsup_lub C;
      inf_lb := @dinf_lb C;
      inf_glb := @dinf_glb C;
      ccd := @dccd C;
    |}.

  (** ** Computing with extrema *)

  Lemma has_lsup {C I} (x : I -> F C) (c : C) :
    has (lsup x) c <-> exists i, has (x i) c.
  Proof. reflexivity. Qed.

  Lemma has_linf {C I} (x : I -> F C) (c : C) :
    has (linf x) c <-> forall i, has (x i) c.
  Proof. reflexivity. Qed.

  Lemma has_fsup {C I} (P : I -> Prop) (f : I -> F C) (c : C) :
    has (fsup P f) c <-> exists i, P i /\ has (f i) c.
  Proof.
    split.
    - intros [[i Hi] Hc]. eauto.
    - intros (i & Hi & Hc). exists (exist P i Hi). assumption.
  Qed.

  Lemma has_finf {C I} (P : I -> Prop) (f : I -> F C) (c : C) :
    has (finf P f) c <-> forall i, P i -> has (f i) c.
  Proof.
    split.
    - intros H i Hi. apply (H (exist P i Hi)).
    - intros H [i Hi]. apply H. assumption.
  Qed.

  (** ** Properties of the embedding *)

  Lemma emb_has {C} (x : downset C) (c : C) :
    dref (emb c) x <-> has x c.
  Proof.
    split.
    - intros H. apply H. cbn. reflexivity.
    - intros H d Hd. cbn in Hd. eapply has_closed; eauto.
  Qed.

  Lemma emb_mor {C : poset} (c1 c2 : C) :
    dref (emb c1) (emb c2) <-> c1 [= c2.
  Proof.
    rewrite emb_has. cbn. reflexivity.
  Qed.

  Global Instance emb_pmor {C : poset} : PosetMorphism (@emb C : C -> F C).
  Proof.
    intros c1 c2. apply emb_mor.
  Qed.

  (** Every downset is the join of the principal downsets it
    contains.  Constructively valid, and the basis for the
    sup-of-infs normal form in [FCD] below. *)

  Lemma emb_join_dense {C : poset} (x : F C) :
    x = sup {c | has x c}, (emb c : F C).
  Proof.
    apply has_eq. intros c. rewrite has_fsup. split.
    - intros H. exists c. split; auto. cbn. reflexivity.
    - intros (d & Hd & Hc). cbn in Hc. eapply has_closed; eauto.
  Qed.

  (** ** The sup-extension, and why interaction sequences want it

    A downset lattice is the free *sup*-lattice, and its extension is
    a plain [sup] over the elements of [x] -- no interposed [inf].
    Consequently two such extensions commute outright
    ([dext2_comm]): consuming [x] then [y] is the same as consuming
    [y] then [x], because both are a single [sup] over pairs.  That
    is exactly the "angel picks a global interaction sequence"
    reading, and it is why a purely angelic model gets interaction
    sequences for free.

    [FCD.ext] is [sup {A | has x A}, inf {c | uhas A c}, f c]: an
    [inf] sits between the two [sup]s, and swapping them is
    codistributivity.  See the discussion at [ISpec.papplies_bind]. *)

  Definition dext {C : poset} {L : ccdlattice} (f : C -> L) (x : F C) : L :=
    sup {c | has x c}, f c.

  Global Instance dext_sup {C : poset} {L : ccdlattice} (f : C -> L) :
    Sup.Morphism (dext f).
  Proof.
    red. intros I x. unfold dext. apply antisymmetry.
    - apply fsup_lub. intros c Hc. destruct Hc as [i Hi].
      apply (sup_at i). apply (fsup_at c); auto. reflexivity.
    - apply sup_lub. intros i. apply fsup_lub. intros c Hc.
      apply (fsup_at c).
      + exists i. assumption.
      + reflexivity.
  Qed.

  Lemma dext_ana {C : poset} {L : ccdlattice} (f : C -> L)
        `{Hf : !PosetMorphism f} (c : C) :
    dext f (emb c) = f c.
  Proof.
    unfold dext. apply antisymmetry.
    - apply fsup_lub. intros d Hd. apply pmor. exact Hd.
    - apply (fsup_at c).
      + cbn. reflexivity.
      + reflexivity.
  Qed.

  (** Two sup-extensions commute.  Constructively, with nothing
    assumed: both sides are the single [sup] over matching pairs. *)

  Lemma dext2_comm {C D : poset} {L : ccdlattice}
        (g : C -> D -> L) (x : F C) (y : F D) :
    dext (fun c => dext (fun d => g c d) y) x =
    dext (fun d => dext (fun c => g c d) x) y.
  Proof.
    apply antisymmetry.
    - apply fsup_lub. intros c Hc. apply fsup_lub. intros d Hd.
      apply (fsup_at d); auto. apply (fsup_at c); auto. reflexivity.
    - apply fsup_lub. intros d Hd. apply fsup_lub. intros c Hc.
      apply (fsup_at c); auto. apply (fsup_at d); auto. reflexivity.
  Qed.

End Downset.


(** * Upsets

  We only need upsets as a poset: they index the [inf]s appearing in
  the normal forms of the free lattice below.  The order is reverse
  inclusion, so that [up] is monotone and so that a larger upset
  denotes a smaller [inf]. *)

Module Upset.

  Record upset (C : poset) :=
    {
      uhas : C -> Prop;
      uhas_closed : ucl uhas;
    }.

  Arguments uhas {C}.
  Arguments uhas_closed {C}.

  Lemma uhas_eq {C} (x y : upset C) :
    (forall c, uhas x c <-> uhas y c) -> x = y.
  Proof.
    intros H. destruct x as [p Hp], y as [q Hq]. cbn in H.
    assert (p = q) as Hpq.
    {
      apply functional_extensionality. intros c.
      apply propositional_extensionality. apply H.
    }
    destruct Hpq. f_equal. apply proof_irrel.
  Qed.

  Definition uref {C} (x y : upset C) :=
    forall c, uhas y c -> uhas x c.

  Lemma uref_refl {C} (x : upset C) : uref x x.
  Proof. firstorder. Qed.

  Lemma uref_trans {C} (x y z : upset C) : uref x y -> uref y z -> uref x z.
  Proof. firstorder. Qed.

  Lemma uref_antisym {C} (x y : upset C) : uref x y -> uref y x -> x = y.
  Proof. intros Hxy Hyx. apply uhas_eq. firstorder. Qed.

  Definition Fpos (C : poset) : poset :=
    {|
      poset_carrier := upset C;
      ref := @uref C;
      ref_refl := @uref_refl C;
      ref_trans := @uref_trans C;
      ref_antisym := @uref_antisym C;
    |}.

  Lemma up_closed {C : poset} (c : C) : ucl (fun d : C => c [= d).
  Proof. intros a b Hab Ha. etransitivity; eauto. Qed.

  Definition up {C : poset} (c : C) : upset C :=
    {| uhas d := c [= d; uhas_closed := up_closed c |}.

  Lemma uhas_up {C} (A : upset C) (c : C) :
    uref A (up c) <-> uhas A c.
  Proof.
    split.
    - intros H. apply H. cbn. reflexivity.
    - intros H d Hd. cbn in Hd. eapply uhas_closed; eauto.
  Qed.

  Lemma up_mor {C : poset} (c1 c2 : C) :
    uref (up c1) (up c2) <-> c1 [= c2.
  Proof.
    rewrite uhas_up. cbn. reflexivity.
  Qed.

End Upset.


(** * The free completely distributive lattice over a poset

  The classical development takes [upset (downset C)].  Both halves
  of that construction are problematic without choice: [upset] is
  (CCD) only under Fawcett and Wood's Theorem 18, which needs the
  ambient topos to be Boolean, and the sup-of-infs normal form
  [join_meet_dense] is then derived from the meet-of-sups one using
  the choice-equivalent law [inf_sup].

  Taking [downset (upset C)] instead fixes both problems at once.
  The lattice is (CCD) by Theorem 3, and since an element *is* a
  down-closed family of upsets, the sup-of-infs normal form holds by
  construction: see [join_meet_dense] below, which needs no
  distributivity at all. *)

Module FCD.

  Definition F (C : poset) : ccdlattice :=
    Downset.F (Upset.Fpos C).

  Definition emb {C : poset} (c : C) : F C :=
    @Downset.emb (Upset.Fpos C) (Upset.up c).

  (** The [inf] of the generators named by an upset [A].  These are
    the "meets" of the sup-of-infs normal form. *)

  Definition gen {C : poset} {L : ccdlattice} (f : C -> L)
             (A : Upset.upset C) : L :=
    inf {c | Upset.uhas A c}, f c.

  Definition ext {C : poset} {L : ccdlattice} (f : C -> L) (x : F C) : L :=
    sup {A | Downset.has x A}, gen f A.

  (** ** The embedding *)

  Lemma emb_has {C : poset} (x : F C) (c : C) :
    Downset.dref (emb c) x <-> Downset.has x (Upset.up c).
  Proof.
    apply Downset.emb_has.
  Qed.

  Lemma emb_mor {C : poset} (c1 c2 : C) :
    Downset.dref (emb c1) (emb c2) <-> c1 [= c2.
  Proof.
    unfold emb. rewrite Downset.emb_mor. apply Upset.up_mor.
  Qed.

  Global Instance emb_pmor {C : poset} : PosetMorphism (@emb C).
  Proof.
    intros c1 c2. apply emb_mor.
  Qed.

  (** ** The sup-of-infs normal form

    [gen emb A] is the principal downset of [A], so an element of
    [F C] is literally the family of the "meets" below it. *)

  Lemma gen_emb {C : poset} (A : Upset.upset C) :
    gen (fun c => (emb c : F C)) A = @Downset.emb (Upset.Fpos C) A.
  Proof.
    unfold gen. apply Downset.has_eq. intros B.
    rewrite Downset.has_finf. split.
    - intros H c Hc. exact (proj1 (Upset.uhas_up B c) (H c Hc)).
    - intros H c Hc. exact (proj2 (Upset.uhas_up B c) (H c Hc)).
  Qed.

  (** Compare [FCD.join_meet_dense] in the classical development,
    which is obtained from the meet-of-joins normal form by an
    appeal to [inf_sup] and hence to choice. *)

  Lemma join_meet_dense {C : poset} (x : F C) :
    x = sup {A | Downset.has x A}, gen (fun c => (emb c : F C)) A.
  Proof.
    etransitivity. { apply (Downset.emb_join_dense x). }
    unfold fsup. f_equal. apply functional_extensionality.
    intros [A HA]. cbn. symmetry. apply gen_emb.
  Qed.

  Lemma ext_emb {C : poset} (x : F C) :
    ext (fun c => (emb c : F C)) x = x.
  Proof.
    symmetry. apply join_meet_dense.
  Qed.

  (** ** The universal property *)

  Lemma ext_ana {C : poset} {L : ccdlattice} (f : C -> L)
        `{Hf : !PosetMorphism f} (c : C) :
    ext f (emb c) = f c.
  Proof.
    unfold ext. apply antisymmetry.
    - apply fsup_lub. intros A HA.
      pose proof (proj1 (Upset.uhas_up A c) HA) as HAc.
      unfold gen. apply (finf_lb c). assumption.
    - apply (fsup_at (Upset.up c)).
      + apply Upset.uref_refl.
      + unfold gen. apply finf_glb. intros d Hd.
        apply pmor. exact Hd.
  Qed.

  Global Instance ext_sup {C : poset} {L : ccdlattice} (f : C -> L) :
    Sup.Morphism (ext f).
  Proof.
    red. intros I x. unfold ext. apply antisymmetry.
    - apply fsup_lub. intros A HA. destruct HA as [i Hi].
      apply (sup_at i). apply (fsup_at A); auto. reflexivity.
    - apply sup_lub. intros i. apply fsup_lub. intros A HA.
      apply (fsup_at A).
      + exists i. assumption.
      + reflexivity.
  Qed.

  (** The uniform witness used in [ext_inf] below: given [y], the
    upset of all generators [c] with [y [= f c].  This is where
    Fawcett and Wood's Lemma 1 does its work.  The classical proof
    would, from [forall i, exists A, ...], *choose* a family of
    upsets and take its union; here the witness is computed from [y]
    alone, uniformly in [i], so no choice is needed. *)

  Lemma wit_closed {C : poset} {L : ccdlattice} (f : C -> L)
        `{Hf : !PosetMorphism f} (y : L) :
    ucl (fun c : C => y [= f c).
  Proof.
    intros a b Hab Ha. etransitivity. exact Ha. apply pmor. assumption.
  Qed.

  Definition wit {C : poset} {L : ccdlattice} (f : C -> L)
             `{Hf : !PosetMorphism f} (y : L) : Upset.upset C :=
    {| Upset.uhas c := y [= f c; Upset.uhas_closed := wit_closed f y |}.

  Global Instance ext_inf {C : poset} {L : ccdlattice} (f : C -> L)
           `{Hf : !PosetMorphism f} :
    Inf.Morphism (ext f).
  Proof.
    red. intros I x. apply antisymmetry.
    - apply inf_glb. intros i. unfold ext.
      apply fsup_lub. intros A HA.
      apply (fsup_at A).
      + apply (HA i).
      + reflexivity.
    - set (P := fun (i : I) (y : L) =>
                  exists A, Downset.has (x i) A /\ y [= gen f A).
      assert (HPdcl : forall i, dcl (P i)).
      {
        intros i y z Hyz (A & HA & Hz). exists A. split; auto.
        etransitivity; eauto.
      }
      assert (HPsup : forall i, (sup {y | P i y}, y) = ext f (x i)).
      {
        intros i. apply antisymmetry.
        - apply fsup_lub. intros y (A & HA & Hy).
          etransitivity. exact Hy.
          unfold ext. apply (fsup_at A); auto. reflexivity.
        - unfold ext. apply fsup_lub. intros A HA.
          apply (fsup_at (gen f A)).
          + exists A. split; auto. reflexivity.
          + reflexivity.
      }
      assert (Heq : (inf i, (sup {y | P i y}, y)) = inf i, ext f (x i)).
      {
        f_equal. apply functional_extensionality. intros i. apply HPsup.
      }
      rewrite <- Heq, inf_sup_dcl by assumption.
      apply fsup_lub. intros y Hy.
      unfold ext. apply (fsup_at (wit f y)).
      + intros i. destruct (Hy i) as (A & HA & HyA).
        refine (Downset.has_closed (x i) (wit f y) A _ HA).
        intros c Hc. cbn.
        etransitivity. exact HyA. apply (finf_lb c). assumption.
      + unfold gen. apply finf_glb. intros c Hc. exact Hc.
  Qed.

  Global Instance ext_mor {C : poset} {L : ccdlattice} (f : C -> L)
           `{Hf : !PosetMorphism f} :
    CDL.Morphism (ext f).
  Proof.
    split.
    - apply ext_sup.
    - apply ext_inf; auto.
  Qed.

  Lemma gen_mono {C : poset} {L : ccdlattice} (f g : C -> L)
        (A : Upset.upset C) :
    (forall c, f c [= g c) -> gen f A [= gen g A.
  Proof.
    intros H. unfold gen. apply finf_glb. intros c Hc.
    etransitivity. apply (finf_lb c); eauto. apply H.
  Qed.

  (** Monotonicity of [ext] in its function argument.  In the
    classical file this kind of reasoning was done by destructing
    [join_meet_dense]; here it is immediate. *)

  Lemma ext_mono {C : poset} {L : ccdlattice} (f g : C -> L) (x : F C) :
    (forall c, f c [= g c) -> ext f x [= ext g x.
  Proof.
    intros H. unfold ext. apply fsup_lub. intros A HA.
    apply (fsup_at A); auto. apply gen_mono. assumption.
  Qed.

  Lemma ext_unique {C : poset} {L : ccdlattice} (f : C -> L)
        (g : F C -> L) `{Hg : !CDL.Morphism g} :
    (forall c, g (emb c) = f c) -> forall x, g x = ext f x.
  Proof.
    intros Hgf x.
    transitivity (g (sup {A | Downset.has x A},
                     gen (fun c => (emb c : F C)) A)).
    { f_equal. apply join_meet_dense. }
    rewrite (Sup.mor_fsup g). unfold ext. f_equal.
    apply functional_extensionality. intros A.
    unfold gen. rewrite (Inf.mor_finf g). f_equal.
    apply functional_extensionality. intros c. apply Hgf.
  Qed.

  Lemma ext_ext {C : poset} {L M : ccdlattice} (g : L -> M)
        `{Hg : !CDL.Morphism g} (f : C -> L) (x : F C) :
    g (ext f x) = ext (fun c => g (f c)) x.
  Proof.
    unfold ext, gen. rewrite (Sup.mor_fsup g). f_equal.
    apply functional_extensionality. intros A.
    rewrite (Inf.mor_finf g). reflexivity.
  Qed.

End FCD.

(** * There is no better free lattice

  [FCD.F C] is the free constructively completely distributive
  lattice over [C]: [FCD.ext_ana], [FCD.ext_mor] and
  [FCD.ext_unique] are the universal property, and all three are
  proved above with no axioms beyond extensionality.  Freeness pins
  the object down, so the theorem below says that *any* other
  construction with the same universal property is isomorphic to
  this one by a map preserving all sups and all infs.

  That is worth recording because it rules out a whole class of
  repairs.  The laws that fail here -- [codistributive], and with it
  [ISpec.bind_bind] and the exchange law at
  [ISpec.papplies_bind] -- do not fail because [downset (upset C)]
  is a clumsy presentation.  They fail because they are not
  consequences of (CCD), and [codist_lem] below locates the gap
  exactly: it is excluded middle.  Indeed [Downset.F] of the
  one-point poset is [Prop] itself, where codistributivity reads

    [(P \/ ~P) = True],

  so no presentation of a lattice containing a copy of [Prop] can
  satisfy it.  A better construction has to give up freeness, not
  change the presentation -- see [IRun] at the end of this file. *)

Theorem fcd_unique {C : poset} (L : ccdlattice) (e : C -> L)
        `{He : !PosetMorphism e}
        (lext : forall M : ccdlattice, (C -> M) -> L -> M)
        (lext_mor : forall (M : ccdlattice) (f : C -> M),
                      PosetMorphism f -> CDL.Morphism (lext M f))
        (lext_ana : forall (M : ccdlattice) (f : C -> M),
                      PosetMorphism f -> forall c, lext M f (e c) = f c)
        (lext_uniq : forall (M : ccdlattice) (f : C -> M) (g : L -> M),
                       CDL.Morphism g ->
                       (forall c, g (e c) = f c) ->
                       forall y, g y = lext M f y) :
  CDL.Morphism (FCD.ext e) /\
  CDL.Morphism (lext (FCD.F C) FCD.emb) /\
  (forall x : FCD.F C, lext (FCD.F C) FCD.emb (FCD.ext e x) = x) /\
  (forall y : L, FCD.ext e (lext (FCD.F C) FCD.emb y) = y).
Proof.
  assert (CDL.Morphism (FCD.ext e)) as Hi by (apply FCD.ext_mor; assumption).
  assert (CDL.Morphism (lext (FCD.F C) FCD.emb)) as Hj
    by (apply lext_mor; apply FCD.emb_pmor).
  split; [assumption | split; [assumption | split]].
  - (* [j . i] agrees with [emb] on generators, so it is the identity. *)
    intros x.
    transitivity (FCD.ext (fun c => (FCD.emb c : FCD.F C)) x).
    + apply (@FCD.ext_unique C (FCD.F C)
               (fun c => (FCD.emb c : FCD.F C))
               (fun y => lext (FCD.F C) FCD.emb (FCD.ext e y))
               (CDL.compose_mor (lext (FCD.F C) FCD.emb) (FCD.ext e) Hi Hj)).
      intros c. rewrite (FCD.ext_ana e c).
      apply lext_ana. apply FCD.emb_pmor.
    + apply FCD.ext_emb.
  - (* [i . j] agrees with [e] on generators, so it is the identity. *)
    intros y.
    transitivity (lext L e y).
    + apply (lext_uniq L e (fun z => FCD.ext e (lext (FCD.F C) FCD.emb z))).
      * apply (CDL.compose_mor _ _ Hj Hi).
      * intros c. rewrite (lext_ana (FCD.F C) FCD.emb (FCD.emb_pmor) c).
        apply (FCD.ext_ana e c).
    + symmetry.
      apply (lext_uniq L e (fun z : L => z)).
      * apply CDL.id_mor.
      * intros c. reflexivity.
Qed.




(** * Dependent products

  Products of (CCD) lattices are (CCD), constructively.  The
  classical file gets the pointwise lattice structure on
  substitutions from [lattices.LatticeProduct]; we rebuild it here,
  since Def. 6.8 of the thesis asks the hom-sets of the resulting
  category of games to be completely distributive lattices.

  The work is done by [poke a y], the element which is [y] at [a]
  and [bot] everywhere else.  This is Fawcett and Wood's Lemma 1
  once more: a single element, computed from the data at hand,
  serves as the witness for every member of the family.  Note it
  needs no decidable equality on the index type, because the [sup]
  is taken over the *proposition* [b = a]. *)

Module PProd.

Section PROD.
  Context {A : Type} (M : A -> ccdlattice).

  Definition pcar := forall a, M a.
  Definition pref (x y : pcar) := forall a, x a [= y a.

  Lemma pref_refl x : pref x x.
  Proof. intros a. reflexivity. Qed.

  Lemma pref_trans x y z : pref x y -> pref y z -> pref x z.
  Proof. intros H1 H2 a. etransitivity; eauto. Qed.

  Lemma pref_antisym x y : pref x y -> pref y x -> x = y.
  Proof.
    intros H1 H2. apply functional_extensionality_dep. intros a.
    apply antisymmetry; auto.
  Qed.

  Definition Ppos : poset :=
    {|
      poset_carrier := pcar;
      ref := pref;
      ref_refl := pref_refl;
      ref_trans := pref_trans;
      ref_antisym := pref_antisym;
    |}.

  Lemma eq_ext (x y : pcar) : (forall a, x a = y a) -> x = y.
  Proof.
    intros H. apply functional_extensionality_dep. exact H.
  Qed.

  Definition psup {I} (x : I -> pcar) : pcar := fun a => sup i, x i a.
  Definition pinf {I} (x : I -> pcar) : pcar := fun a => inf i, x i a.

  Lemma psup_ub {I} (i : I) (x : I -> pcar) : pref (x i) (psup x).
  Proof. intros a. apply (sup_ub i (fun j => x j a)). Qed.

  Lemma psup_lub {I} (x : I -> pcar) y : (forall i, pref (x i) y) -> pref (psup x) y.
  Proof. intros H a. apply (sup_lub (fun j => x j a)). intros i. apply H. Qed.

  Lemma pinf_lb {I} (i : I) (x : I -> pcar) : pref (pinf x) (x i).
  Proof. intros a. apply (inf_lb i (fun j => x j a)). Qed.

  Lemma pinf_glb {I} (x : pcar) (y : I -> pcar) :
    (forall i, pref x (y i)) -> pref x (pinf y).
  Proof. intros H a. apply (inf_glb (x a) (fun j => y j a)). intros i. apply H. Qed.

  (** The uniform witness: the element which is [y] at [a] and [bot]
    everywhere else.  Note this needs no decidable equality on [A]:
    the [sup] is taken over the *proposition* [b = a]. *)

  Definition poke (a : A) (y : M a) : pcar :=
    fun b => sup e : b = a, eq_rect a (fun a0 => M a0) y b (eq_sym e).

  Lemma poke_at (a : A) (y : M a) : y [= poke a y a.
  Proof.
    apply (sup_at (@eq_refl A a)). cbn. reflexivity.
  Qed.

  Lemma poke_lb (a : A) (y : M a) (x : pcar) : y [= x a -> pref (poke a y) x.
  Proof.
    intros Hy b. apply sup_lub. intros e. destruct e. cbn. assumption.
  Qed.

  Lemma pccd {I} (P : I -> Ppos -> Prop) :
    (forall i, dcl (P i)) ->
    pinf (fun i => psup (fun z : sig (P i) => proj1_sig z)) =
    psup (fun z : sig (fun y => forall i, P i y) => proj1_sig z).
  Proof.
    intros HP. apply pref_antisym.
    - intros a.
      set (Q := fun (i : I) (y : M a) => exists x, P i x /\ y [= x a).
      assert (HQ : forall i, dcl (Q i)).
      { intros i y z Hyz (x & Hx & Hz). exists x. split; auto.
        etransitivity; eauto. }
      assert (HQs : forall i, (sup {y | Q i y}, y) = lsup (fun z : sig (P i) => proj1_sig z a)).
      { intros i. apply antisymmetry.
        - apply fsup_lub. intros y (x & Hx & Hy).
          etransitivity. exact Hy. apply (sup_ub (exist (P i) x Hx) (fun z : sig (P i) => proj1_sig z a)).
        - apply (sup_lub (fun z : sig (P i) => proj1_sig z a)). intros [x Hx]. cbn.
          apply (fsup_at (x a)). exists x. split; auto. reflexivity. reflexivity. }
      assert (Heq : (inf i, (sup {y | Q i y}, y)) =
                    inf i, lsup (fun z : sig (P i) => proj1_sig z a)).
      { f_equal. apply functional_extensionality. intros i. apply HQs. }
      unfold pinf, psup. rewrite <- Heq, inf_sup_dcl by assumption.
      apply fsup_lub. intros y Hy.
      assert (Hp : forall i, P i (poke a y)).
      { intros i. destruct (Hy i) as (x & Hx & Hyx).
        eapply HP; eauto. apply poke_lb. assumption. }
      etransitivity. apply (poke_at a y).
      apply (sup_ub (exist (fun y0 : Ppos => forall i, P i y0) (poke a y) Hp)
                    (fun z : sig (fun y0 : Ppos => forall i, P i y0) => proj1_sig z a)).
    - apply psup_lub. intros [x Hx]. cbn. apply pinf_glb. intros i.
      apply (psup_ub (exist (P i) x (Hx i)) (fun z : sig (P i) => proj1_sig z)).
  Qed.

  Definition Pccd : ccdlattice :=
    {|
      ccdl_poset := Ppos;
      lsup := @psup;
      linf := @pinf;
      sup_ub := @psup_ub;
      sup_lub := @psup_lub;
      inf_lb := @pinf_lb;
      inf_glb := @pinf_glb;
      ccd := @pccd;
    |}.

End PROD.
End PProd.

(** * Codistributivity

  The [inf]-over-[sup] law [inf_sup] is the whole of (CCD).  Its
  dual - a finite [join] distributing over an infinitary [inf] -
  does *not* follow.  In [Downset.F C] the inclusion

    [inf i, (a || x i)  [=  a || inf i, x i]

  says that

    [(forall i, has a c \/ has (x i) c) ->
     has a c \/ (forall i, has (x i) c)],

  i.e. that disjunction distributes over universal quantification.

  We name the principle, and below we pin down its strength exactly:
  for a downset lattice over an inhabited poset it is *equivalent to
  excluded middle* ([lem_codist] and [codist_lem]).  So the handful
  of interaction specification laws that need it are classical, and
  precisely as classical as excluded middle - no more (it needs no
  choice) and no less.

  This agrees with Fawcett and Wood's bookkeeping.  Their Theorem
  18, that (CCD) is self-dual, is one of the two results they mark
  with an obelisk rather than an asterisk: it needs the ambient topos
  to be Boolean, not the axiom of choice.

  The converse inclusion holds unconditionally. *)

Definition codistributive (L : ccdlattice) :=
  forall I (a : L) (x : I -> L), (inf i, (a || x i)) [= (a || (inf i, x i)).

Lemma join_inf_le {L : ccdlattice} {I} (a : L) (x : I -> L) :
  (a || (inf i, x i)) [= (inf i, (a || x i)).
Proof.
  apply inf_glb. intros i. apply join_lub.
  - apply join_ub_l.
  - apply join_r. apply inf_lb.
Qed.

(** ** Exact strength *)

Definition lem := forall P : Prop, P \/ ~ P.

Lemma has_join {C : poset} (x y : Downset.F C) (c : C) :
  Downset.has (x || y) c <-> Downset.has x c \/ Downset.has y c.
Proof.
  unfold join. rewrite Downset.has_lsup. split.
  - intros [[|] H]; auto.
  - intros [H | H]; [exists true | exists false]; assumption.
Qed.

Lemma has_bot {C : poset} (c : C) :
  Downset.has (bot : Downset.F C) c <-> False.
Proof.
  unfold bot. rewrite Downset.has_lsup. split.
  - intros [[ ] _].
  - intros [ ].
Qed.

Lemma has_meet {C : poset} (x y : Downset.F C) (c : C) :
  Downset.has (x && y) c <-> Downset.has x c /\ Downset.has y c.
Proof.
  unfold meet. rewrite Downset.has_linf. split.
  - intros H. split; [apply (H true) | apply (H false)].
  - intros [Hx Hy] [|]; assumption.
Qed.

(** Finite demonic choice is not affected.  The binary case of
  codistributivity is constructively valid -- it is just the
  distributive law, and disjunction does distribute over a *finite*
  conjunction -- and the general finite case follows by induction.
  Only infinitary [inf] needs excluded middle. *)

Lemma codist_meet {C : poset} (a x y : Downset.F C) :
  ((a || x) && (a || y)) [= (a || (x && y)).
Proof.
  intros c Hc.
  apply has_meet in Hc as [Hx Hy].
  apply has_join in Hx. apply has_join in Hy. apply has_join.
  destruct Hx as [Ha | Hx]; [left; assumption | ].
  destruct Hy as [Ha | Hy]; [left; assumption | ].
  right. apply has_meet. split; assumption.
Qed.

Lemma guard_closed {C : poset} (c0 : C) (P : Prop) :
  dcl (fun d : C => d [= c0 /\ P).
Proof.
  intros d e Hde [He HP]. split; auto. etransitivity; eauto.
Qed.

Definition guard {C : poset} (c0 : C) (P : Prop) : Downset.F C :=
  {| Downset.has d := d [= c0 /\ P; Downset.has_closed := guard_closed c0 P |}.

Lemma lem_codist (C : poset) :
  lem -> codistributive (Downset.F C).
Proof.
  intros Hlem I a x c Hc.
  rewrite Downset.has_linf in Hc.
  apply has_join.
  destruct (Hlem (Downset.has a c)) as [H | H].
  - left. assumption.
  - right. rewrite Downset.has_linf. intros i.
    destruct (proj1 (has_join a (x i) c) (Hc i)) as [Ha | Hx].
    + contradiction.
    + assumption.
Qed.

(** Conversely, codistributivity of a single downset lattice over an
  inhabited poset already yields excluded middle: take the index type
  of the [inf] to be the proposition [P] itself. *)

Lemma codist_lem (C : poset) (c0 : C) :
  codistributive (Downset.F C) -> lem.
Proof.
  intros Hcd P.
  specialize (Hcd P (guard c0 P) (fun _ => bot) c0).
  destruct (proj1 (has_join _ _ c0) (Hcd ltac:(
    rewrite Downset.has_linf; intros HP; apply has_join;
    left; split; [reflexivity | assumption]))) as [[_ HP] | Hb].
  - left. assumption.
  - right. intros HP.
    rewrite Downset.has_linf in Hb.
    apply (has_bot c0). apply (Hb HP).
Qed.

(** ** Could decidability help?

  The disjunct that has to be decided is [Downset.has a c].  Where
  that is decidable the inclusion goes through with nothing further
  assumed. *)

Lemma codist_dec {C : poset} (a : Downset.F C) :
  (forall c, Downset.has a c \/ ~ Downset.has a c) ->
  forall I (x : I -> Downset.F C), (inf i, (a || x i)) [= (a || (inf i, x i)).
Proof.
  intros Hdec I x c Hc.
  rewrite Downset.has_linf in Hc. apply has_join.
  destruct (Hdec c) as [H | H].
  - left. assumption.
  - right. rewrite Downset.has_linf. intros i.
    destruct (proj1 (has_join a (x i) c) (Hc i)) as [Ha | Hx].
    + contradiction.
    + assumption.
Qed.

(** That is of no help here, though, and no decidability hypothesis
  on the data of the problem can be.  In the instance that
  [join_ext_absorb] needs, [a] is a *single generator* - [emb
  (pmove m)] - and [c] ranges over all of [Upset.Fpos C].  So the
  proposition to decide is "does this upset contain [c0]", asked of
  an arbitrary up-closed predicate.  It is not a question about
  plays, operations, answer types or values: it lives one level up,
  in [Prop], inside the carrier of the lattice itself.  And the
  single-generator instance is already equivalent to excluded
  middle. *)

Lemma pguard_closed {C : poset} (c0 : C) (P : Prop) :
  ucl (fun d : C => P /\ c0 [= d).
Proof.
  intros d e Hde [HP Hd]. split; auto. etransitivity; eauto.
Qed.

Definition pguard {C : poset} (c0 : C) (P : Prop) : Upset.upset C :=
  {| Upset.uhas d := P /\ c0 [= d; Upset.uhas_closed := pguard_closed c0 P |}.

Lemma has_emb_pguard {C : poset} (c0 : C) (P : Prop) :
  Downset.has (FCD.emb c0) (pguard c0 P) <-> P.
Proof.
  unfold FCD.emb. split.
  - intros H. apply (proj1 (Upset.uhas_up (pguard c0 P) c0)) in H. apply H.
  - intros HP. apply (Upset.uhas_up (pguard c0 P) c0).
    split; auto. reflexivity.
Qed.

Lemma codist_emb_lem {C : poset} (c0 : C) :
  (forall I (x : I -> FCD.F C),
     (inf i, (FCD.emb c0 || x i)) [= (FCD.emb c0 || (inf i, x i))) -> lem.
Proof.
  intros H P.
  specialize (H P (fun _ => bot) (pguard c0 P)).
  destruct (proj1 (has_join _ _ _) (H ltac:(
    rewrite Downset.has_linf; intros HP; apply has_join; left;
    exact (proj2 (has_emb_pguard c0 P) HP)))) as [He | Hb].
  - left. exact (proj1 (has_emb_pguard c0 P) He).
  - right. intros HP. rewrite Downset.has_linf in Hb.
    exact (proj1 (has_bot (C := Upset.Fpos C) (pguard c0 P)) (Hb HP)).
Qed.

(** One could instead cut the lattice down so that the question
  becomes decidable by construction, replacing [Upset.upset] by
  up-closed *decidable* subsets.  That does fix this instance, but
  it costs the universal property: the witness [FCD.wit] driving
  [FCD.ext_inf] - and hence the freeness of [downset (upset C)] - is
  the upset [fun c => y [= f c], built from an order comparison in
  the *target* lattice, which is not decidable.  Without
  [FCD.ext_inf] the extension is no longer a complete homomorphism
  and the object is no longer FCD. *)

(** ** Why adjoining a bottom does not help

  [lattices/AdjoinBot.v] introduces [Lazy] morphisms - preserving
  all infs and all *non-empty* sups - and adjoins a bottom so that
  such a map becomes a complete homomorphism.  The recursive clause
  of [pbind] has the shape [fun z => a || k z], which is indeed not
  bot-preserving, so one might hope that working over an adjoined
  bottom removes the need for codistributivity.

  It does not.  Constructively, bot-preservation is not the obstacle:
  the non-empty sup half of [Lazy] holds outright ([join_sup_ne]),
  while the *inf* half is exactly codistributivity
  ([join_inf_codist]), hence exactly excluded middle.  The [Lazy]
  condition is not a way around the gap; it is the gap. *)

Lemma join_sup_ne {L : ccdlattice} {I} (a : L) (x : I -> L) :
  inhabited I -> a || (sup i, x i) = sup i, (a || x i).
Proof.
  intros [i0]. apply antisymmetry.
  - apply join_lub.
    + apply (sup_at i0). apply join_ub_l.
    + apply sup_lub. intros i. apply (sup_at i). apply join_ub_r.
  - apply sup_lub. intros i. apply join_lub.
    + apply join_ub_l.
    + apply join_r. apply (sup_at i). reflexivity.
Qed.

Lemma join_inf_codist (L : ccdlattice) :
  (forall a : L, Inf.Morphism (fun z => a || z)) <-> codistributive L.
Proof.
  split.
  - intros H I a x. specialize (H a I x). cbn in H.
    rewrite <- H. reflexivity.
  - intros Hcd a. red. intros I x. cbn. apply antisymmetry.
    + apply join_inf_le.
    + apply Hcd.
Qed.

Lemma uempty_closed (C : poset) : ucl (fun _ : C => False).
Proof. intros x y Hxy H. exact H. Qed.

Definition uempty (C : poset) : Upset.upset C :=
  {| Upset.uhas _ := False; Upset.uhas_closed := uempty_closed C |}.

(** * Effect signatures *)

(** The classical file gets [esig] from [structures.Effects], which
  in turn depends on the classical lattice library.  Since only the
  definition is needed, we repeat it here. *)

Definition esig := Type -> Type.


(** * Interaction specifications *)

Module ISpec.

  Ltac depsubst :=
    subst;
    lazymatch goal with
      | H : existT _ ?x _ = existT _ ?x _ |- _ =>
        apply inj_pair2 in H; depsubst
      | _ =>
        idtac
    end.

  (** ** Plays *)

  Inductive play {E : esig} {V} :=
    | pret (v : V)
    | pmove {X} (m : E X)
    | pcons {X} (m : E X) (n : X) (s : play).

  Arguments play : clear implicits.

  Inductive pref {E : esig} {V} : relation (play E V) :=
    | pret_ref (v : V) :
        pref (pret v) (pret v)
    | pmove_ref {N} (m : E N) :
        pref (pmove m) (pmove m)
    | pmove_cons_ref {N} (m : E N) (n : N) (s : play E V) :
        pref (pmove m) (pcons m n s)
    | pcons_ref {N} (m : E N) (n : N) (s t : play E V) :
        pref s t -> pref (pcons m n s) (pcons m n t).

  Lemma pref_refl {E V} (p : play E V) :
    pref p p.
  Proof.
    induction p; constructor; auto.
  Qed.

  Lemma pref_trans {E V} (p q r : play E V) :
    pref p q -> pref q r -> pref p r.
  Proof.
    intros Hpq. revert r.
    induction Hpq; inversion 1; depsubst; constructor; auto.
  Qed.

  Lemma pref_antisym {E V} (p q : play E V) :
    pref p q -> pref q p -> p = q.
  Proof.
    intros Hpq Hqp.
    induction Hpq; inversion Hqp; depsubst; try congruence.
    assert (s = t) as Hst by (apply IHHpq; assumption).
    congruence.
  Qed.

  Definition play_poset (E : esig) (V : Type) : poset :=
    {|
      poset_carrier := play E V;
      ref := @pref E V;
      ref_refl := @pref_refl E V;
      ref_trans := @pref_trans E V;
      ref_antisym := @pref_antisym E V;
    |}.

  (** ** The underlying lattice

    As in the classical development, an interaction specification is
    an element of the free completely distributive lattice over the
    poset of plays.  The only change is that this is now the
    constructive lattice built above. *)

  Definition t (E : esig) (V : Type) : ccdlattice :=
    FCD.F (play_poset E V).

  Definition emb {E V} (p : play E V) : t E V :=
    @FCD.emb (play_poset E V) p.

  Definition ext {E V} {L : ccdlattice} (f : play_poset E V -> L) : t E V -> L :=
    @FCD.ext (play_poset E V) L f.

  Global Instance emb_pmor {E V} :
    PosetMorphism (@emb E V : play_poset E V -> t E V).
  Proof.
    apply (@FCD.emb_pmor (play_poset E V)).
  Qed.

  Lemma emb_mor {E V} (p q : play E V) :
    emb p [= emb q <-> pref p q.
  Proof.
    apply (@FCD.emb_mor (play_poset E V)).
  Qed.

  Global Instance ext_sup {E V} {L : ccdlattice} (f : play_poset E V -> L) :
    Sup.Morphism (ext f).
  Proof.
    apply FCD.ext_sup.
  Qed.

  Global Instance ext_mor {E V} {L : ccdlattice} (f : play_poset E V -> L)
           `{Hf : !PosetMorphism f} :
    CDL.Morphism (ext f).
  Proof.
    apply FCD.ext_mor. assumption.
  Qed.

  Lemma ext_ana {E V} {L : ccdlattice} (f : play_poset E V -> L)
        `{Hf : !PosetMorphism f} (p : play E V) :
    ext f (emb p) = f p.
  Proof.
    apply (FCD.ext_ana f).
  Qed.

  Lemma ext_mono {E V} {L : ccdlattice} (f g : play_poset E V -> L) (x : t E V) :
    (forall p, f p [= g p) -> ext f x [= ext g x.
  Proof.
    apply FCD.ext_mono.
  Qed.

  Lemma ext_emb {E V} (x : t E V) :
    ext emb x = x.
  Proof.
    apply (@FCD.ext_emb (play_poset E V)).
  Qed.

  Lemma ext_ext {E V} {L M : ccdlattice} (g : L -> M) `{Hg : !CDL.Morphism g}
        (f : play_poset E V -> L) (x : t E V) :
    g (ext f x) = ext (fun p => g (f p)) x.
  Proof.
    apply (FCD.ext_ext g f).
  Qed.

  (** Mapping a monotonic function on plays over a specification.
    This is [FCD.map] of the classical [Completion] interface. *)

  Definition map {E V W} (f : play_poset E V -> play_poset E W) :
    t E V -> t E W :=
    ext (fun p => emb (f p)).

  Global Instance emb_comp_pmor {E V W} (f : play_poset E V -> play_poset E W)
         `{Hf : !PosetMorphism f} :
    PosetMorphism (fun p => emb (f p) : t E W).
  Proof.
    intros p q Hpq. apply emb_mor. exact (Hf p q Hpq).
  Qed.

  Global Instance map_mor {E V W} (f : play_poset E V -> play_poset E W)
         `{Hf : !PosetMorphism f} :
    CDL.Morphism (map f).
  Proof.
    unfold map. typeclasses eauto.
  Qed.

  Lemma map_emb {E V W} (f : play_poset E V -> play_poset E W)
        `{Hf : !PosetMorphism f} (p : play E V) :
    map f (emb p) = emb (f p).
  Proof.
    unfold map. apply (ext_ana (fun q => emb (f q))).
  Qed.

  (** ** Extending a play by an answered move *)

  Definition pcons_emb {E V X} (m : E X) (n : X) (s : play E V) : t E V :=
    emb (pcons m n s).

  Global Instance pcons_pmor {E V X} (m : E X) (n : X) :
    PosetMorphism (pcons m n : play_poset E V -> play_poset E V).
  Proof.
    intros s1 s2 Hs. constructor. assumption.
  Qed.

  Global Instance pcons_emb_pmor {E V X} (m : E X) (n : X) :
    PosetMorphism (pcons_emb m n : play_poset E V -> t E V).
  Proof.
    intros s1 s2 Hs. apply emb_mor. constructor. assumption.
  Qed.

  Definition pcext {E V X} (m : E X) (n : X) : t E V -> t E V :=
    ext (pcons_emb m n).

  Global Instance pcext_mor {E V X} (m : E X) (n : X) :
    CDL.Morphism (@pcext E V X m n).
  Proof.
    unfold pcext. typeclasses eauto.
  Qed.

  Lemma pcext_emb {E V X} (m : E X) (n : X) (s : play E V) :
    pcext m n (emb s) = emb (pcons m n s).
  Proof.
    unfold pcext. apply (ext_ana (pcons_emb m n)).
  Qed.

  (** ** Monad structure *)

  Definition ret {E A} (a : A) : t E A :=
    emb (pret a).

  Fixpoint pbind {E A B} (f : A -> t E B) (p : play E A) : t E B :=
    match p with
      | pret a => f a
      | pmove m => emb (pmove m)
      | pcons m n q => emb (pmove m) || pcext m n (pbind f q)
    end.

  Global Instance pbind_pmor {E A B} (f : A -> t E B) :
    PosetMorphism (pbind f : play_poset E A -> t E B).
  Proof.
    intros p q Hpq. induction Hpq; cbn [pbind].
    - reflexivity.
    - reflexivity.
    - apply join_ub_l.
    - apply join_lub.
      + apply join_ub_l.
      + apply join_r. apply pmor. assumption.
  Qed.

  Definition bind {E A B} (f : A -> t E B) : t E A -> t E B :=
    ext (pbind f).

  Global Instance bind_mor {E A B} (f : A -> t E B) :
    CDL.Morphism (bind f).
  Proof.
    unfold bind. typeclasses eauto.
  Qed.

  Lemma bind_emb {E A B} (f : A -> t E B) (p : play E A) :
    bind f (emb p) = pbind f p.
  Proof.
    unfold bind. apply (ext_ana (pbind f)).
  Qed.

  (** Monotonicity in the continuation.  The classical proof of
    [papply_mor] worked by destructing [FCD.join_meet_dense]; with
    the constructive normal form, monotonicity of [ext] in its
    function argument is immediate and does all the work. *)

  Lemma pbind_mono {E A B} (f g : A -> t E B) (p : play E A) :
    (forall a, f a [= g a) -> pbind f p [= pbind g p.
  Proof.
    intros H. induction p; cbn [pbind].
    - apply H.
    - reflexivity.
    - apply join_lub.
      + apply join_ub_l.
      + apply join_r. apply pmor. assumption.
  Qed.

  Lemma bind_mono {E A B} (f g : A -> t E B) (x : t E A) :
    (forall a, f a [= g a) -> bind f x [= bind g x.
  Proof.
    intros H. unfold bind. apply ext_mono. intros p.
    apply pbind_mono. assumption.
  Qed.

  Lemma bind_ret_r {E A B} (a : A) (f : A -> t E B) :
    bind f (ret a) = f a.
  Proof.
    unfold ret. rewrite bind_emb. reflexivity.
  Qed.

  Lemma pbind_ret_l {E A} :
    pbind (@ret E A) = emb.
  Proof.
    apply functional_extensionality. intros s.
    induction s; cbn [pbind]; try reflexivity.
    rewrite IHs, pcext_emb.
    apply antisymmetry.
    - apply join_lub.
      + apply emb_mor. constructor.
      + reflexivity.
    - apply join_ub_r.
  Qed.

  Lemma bind_ret_l {E A} (x : t E A) :
    bind ret x = x.
  Proof.
    unfold bind. rewrite pbind_ret_l. apply ext_emb.
  Qed.

  (** ** Recursion and non-termination

    [t E A] is a complete lattice, so a tail-recursive loop is just a
    least fixed point; no continuity or dcpo structure is needed to
    define it.  [repeat body] runs [body] over and over, and
    [repeat_unfold] is its loop law.

    Non-termination is therefore representable, and the resulting
    element is *not* [bot]: [pbind] keeps [emb (pmove m)] for every
    move already issued, so the divergent loop is the (prefix-closed)
    set of all its finite interactions, with no [pret] among them.
    That is exactly the trace-set reading of divergence.  It is only
    *silent* divergence -- a loop issuing no moves at all -- that the
    thesis chooses to identify with [bot] (§5.3.3). *)

  Global Instance repeat_body_mor {E A} (body : t E A) :
    PosetMorphism (fun x : t E A => bind (fun _ => x) body).
  Proof.
    intros x y Hxy. apply bind_mono. intros _. assumption.
  Qed.

  Definition repeat {E A} (body : t E A) : t E A :=
    lfp (fun x => bind (fun _ => x) body).

  Lemma repeat_unfold {E A} (body : t E A) :
    bind (fun _ => repeat body) body = repeat body.
  Proof.
    apply (lfp_fixed (fun x : t E A => bind (fun _ => x) body)).
  Qed.

  Lemma repeat_least {E A} (body x : t E A) :
    bind (fun _ => x) body [= x -> repeat body [= x.
  Proof.
    intros H.
    apply (lfp_least (fun y : t E A => bind (fun _ => y) body) x H).
  Qed.

  Lemma bind_le_id {E A} (f : A -> t E A) (x : t E A) :
    (forall a, f a [= ret a) -> bind f x [= x.
  Proof.
    intros H. etransitivity.
    - apply bind_mono. exact H.
    - rewrite bind_ret_l. reflexivity.
  Qed.

  (** ** Interaction *)

  (** The interaction primitive triggers one of the actions from the
    signature and returns the environment's response. *)

  Definition int {E ar} (m : E ar) : t E ar :=
    sup k : option ar,
      match k with
        | Some n => emb (pcons m n (pret n))
        | None   => emb (pmove m)
      end.

  Lemma bind_int {E A X} (f : X -> t E A) (m : E X) :
    bind f (int m) =
    sup k : option X,
      match k with
        | Some n => emb (pmove m) || pcext m n (f n)
        | None   => emb (pmove m)
      end.
  Proof.
    unfold int. rewrite (Sup.mor (f := bind f)).
    f_equal. apply functional_extensionality.
    intros [n | ]; rewrite bind_emb; cbn [pbind]; reflexivity.
  Qed.

  (** ** Substitutions *)

  (** Morphisms between two effect signatures are substitutions,
    which give an interaction specification in [E] for each possible
    operation in [F].  As in the classical file, and as Def. 6.8 of
    the thesis requires of the hom-sets of the resulting category of
    games, these carry a pointwise completely distributive lattice
    structure; here it comes from [PProd]. *)

  Definition subst (E F : esig) : ccdlattice :=
    PProd.Pccd (fun ar : Type => PProd.Pccd (fun m : F ar => t E ar)).

  (** To apply a substitution [f : E -> F] to an interaction
    specification in [F], we replace each move [m] by the
    corresponding interaction as given by [f m]. *)

  Fixpoint papply {E F A} (f : subst E F) (s : play F A) : t E A :=
    match s with
      | pret a => emb (pret a)
      | pmove m => bind (fun _ => bot) (f _ m)
      | pcons m n q => bind (fun n' => sup H : n' = n, papply f q) (f _ m)
    end.

  (** Compare the classical proof, which destructed
    [FCD.join_meet_dense] twice and so depended on choice. *)

  Global Instance papply_pmor {E F A} (f : subst E F) :
    PosetMorphism (papply f : play_poset F A -> t E A).
  Proof.
    intros p q Hpq. induction Hpq; cbn [papply].
    - reflexivity.
    - reflexivity.
    - apply bind_mono. intros n'. apply bot_lb.
    - apply bind_mono. intros n'. apply sup_lub. intros Hn'.
      apply (sup_at Hn'). assumption.
  Qed.

  Definition apply {E F A} (f : subst E F) : t F A -> t E A :=
    ext (papply f).

  Global Instance apply_mor {E F A} (f : subst E F) :
    CDL.Morphism (@apply E F A f).
  Proof.
    unfold apply. typeclasses eauto.
  Qed.

  Definition compose {E F G} (g : subst F G) (f : subst E F) : subst E G :=
    fun ar m => apply f (g ar m).

  Lemma apply_emb {E F A} (f : subst E F) (p : play F A) :
    apply f (emb p) = papply f p.
  Proof.
    unfold apply. apply (ext_ana (papply f)).
  Qed.

  Lemma apply_ret {E F A} (f : subst E F) (a : A) :
    apply f (ret a) = ret a.
  Proof.
    unfold ret. rewrite apply_emb. reflexivity.
  Qed.

  (** ** Applying the identity substitution

    This was left admitted in the classical development.  It goes
    through here because [bind] only has to be pushed through the
    [sup] defining [int], which is choice-free. *)

  Lemma papply_int {E A} (p : play E A) :
    papply (@int E) p = emb p.
  Proof.
    induction p as [v | X m | X m n q IHq]; cbn [papply].
    - reflexivity.
    - rewrite bind_int. cbv beta. apply antisymmetry.
      + apply sup_lub. intros [n | ].
        * apply join_lub.
          -- reflexivity.
          -- rewrite (Sup.mor_bot (pcext m n)). apply bot_lb.
        * reflexivity.
      + apply (sup_at None). reflexivity.
    - rewrite bind_int. cbv beta. apply antisymmetry.
      + apply sup_lub. intros [n0 | ].
        * apply join_lub.
          -- apply emb_mor. constructor.
          -- rewrite (Sup.mor (f := pcext m n0)).
             apply sup_lub. intros Hn0. subst n0.
             rewrite IHq, pcext_emb. reflexivity.
        * apply emb_mor. constructor.
      + apply (sup_at (Some n)). apply join_r.
        rewrite (Sup.mor (f := pcext m n)).
        apply (sup_at (@eq_refl X n)).
        rewrite IHq, pcext_emb. reflexivity.
  Qed.

  Lemma apply_int_l {E A} (x : t E A) :
    apply (@int E) x = x.
  Proof.
    unfold apply. transitivity (ext emb x).
    - f_equal. apply functional_extensionality. intros p.
      apply papply_int.
    - apply ext_emb.
  Qed.

  Lemma compose_int_r {E F} (f : subst E F) :
    compose f (@int E) = f.
  Proof.
    apply PProd.eq_ext. intros ar. apply PProd.eq_ext. intros m.
    apply apply_int_l.
  Qed.

  (** ** Associativity of [bind]

    Left admitted in the classical development.  Here it is reduced
    to the single lattice-theoretic principle [codistributive]: the
    recursive clause of [pbind] joins [emb (pmove m)] onto an [ext],
    and pushing that [join] back out through the [inf]s of the
    normal form is exactly the codistributivity discussed above. *)

  Lemma join_ext_absorb {E A B} (a : t E B) (k : play_poset E A -> t E B)
        (z : t E A) :
    codistributive (t E B) ->
    ext (fun s => a || k s) z [= a || ext k z.
  Proof.
    intros Hcd. unfold ext, FCD.ext, FCD.gen.
    apply fsup_lub. intros U HU.
    etransitivity.
    - apply (Hcd _ a (fun i : sig (Upset.uhas U) => k (proj1_sig i))).
    - apply join_lub.
      + apply join_ub_l.
      + apply join_r. apply (fsup_at U). assumption. reflexivity.
  Qed.

  Lemma join_ext_join {E A B} (a : t E B) (k : play_poset E A -> t E B)
        (z : t E A) :
    codistributive (t E B) ->
    a || ext (fun s => a || k s) z = a || ext k z.
  Proof.
    intros Hcd. apply antisymmetry.
    - apply join_lub.
      + apply join_ub_l.
      + apply join_ext_absorb. assumption.
    - apply join_lub.
      + apply join_ub_l.
      + apply join_r. apply ext_mono. intros s. apply join_ub_r.
  Qed.

  Lemma bind_pcext {E B C} (g : B -> t E C) {X} (m : E X) (n : X) (z : t E B) :
    bind g (pcext m n z) = ext (fun s => pbind g (pcons m n s)) z.
  Proof.
    unfold pcext. rewrite (ext_ext (bind g) (pcons_emb m n)).
    f_equal. apply functional_extensionality. intros s.
    unfold pcons_emb. apply bind_emb.
  Qed.

  Lemma pcext_bind {E B C} (g : B -> t E C) {X} (m : E X) (n : X) (z : t E B) :
    pcext m n (bind g z) = ext (fun s => pcext m n (pbind g s)) z.
  Proof.
    unfold bind. rewrite (ext_ext (pcext m n) (pbind g)). reflexivity.
  Qed.

  Lemma pbind_bind {E A B C} (g : B -> t E C) (f : A -> t E B) (p : play E A) :
    codistributive (t E C) ->
    bind g (pbind f p) = pbind (fun a => bind g (f a)) p.
  Proof.
    intros Hcd. induction p as [a | X m | X m n q IHq]; cbn [pbind].
    - reflexivity.
    - rewrite bind_emb. reflexivity.
    - rewrite (Sup.mor_join (bind g)), bind_emb, bind_pcext.
      rewrite <- IHq, pcext_bind. cbn [pbind].
      apply join_ext_join. assumption.
  Qed.

  Lemma bind_bind {E A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    codistributive (t E C) ->
    bind g (bind f x) = bind (fun a => bind g (f a)) x.
  Proof.
    intros Hcd. unfold bind.
    rewrite (ext_ext (ext (pbind g)) (pbind f)).
    f_equal. apply functional_extensionality. intros p.
    apply (pbind_bind g f p Hcd).
  Qed.

  (** ** The half of associativity that is free

    One inclusion of [bind_bind] needs nothing at all: the step that
    fails is [join_ext_absorb], and its converse ([join_ub_r] under
    [ext_mono]) is unconditional.  Re-associating a sequence towards
    the right always gives a *refinement* of re-associating it to
    the left. *)
  Lemma pbind_bind_le {E A B C} (g : B -> t E C) (f : A -> t E B)
        (p : play E A) :
    pbind (fun a => bind g (f a)) p [= bind g (pbind f p).
  Proof.
    induction p as [a | X m | X m n q IHq]; cbn [pbind].
    - reflexivity.
    - rewrite bind_emb. reflexivity.
    - rewrite (Sup.mor_join (bind g)), bind_emb, bind_pcext.
      cbn [pbind]. apply join_lub.
      + apply join_ub_l.
      + apply join_r. etransitivity.
        * apply pmor. apply IHq.
        * rewrite pcext_bind. apply ext_mono. intros s. apply join_ub_r.
  Qed.

  Lemma bind_ext_ext {E A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    bind g (bind f x) = ext (fun p => bind g (pbind f p)) x.
  Proof.
    unfold bind. apply (ext_ext (ext (pbind g)) (pbind f)).
  Qed.

  Lemma bind_bind_le {E A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    bind (fun a => bind g (f a)) x [= bind g (bind f x).
  Proof.
    rewrite bind_ext_ext.
    change (bind (fun a => bind g (f a)) x)
      with (ext (pbind (fun a => bind g (f a))) x).
    apply ext_mono. intros p. apply pbind_bind_le.
  Qed.

  (** ** Applying a substitution to a single interaction

    One inclusion is choice-free: every play that [apply f (int m)]
    contributes already refines [f ar m], because the continuations
    involved all refine [ret]. *)

  Lemma apply_int_r_le {E F ar} (m : F ar) (f : subst E F) :
    apply f (int m) [= f ar m.
  Proof.
    unfold int. rewrite (Sup.mor (f := apply f)).
    apply sup_lub. intros [n | ]; rewrite apply_emb; cbn [papply].
    - apply bind_le_id. intros n'. apply sup_lub. intros Hn'.
      subst n'. reflexivity.
    - apply bind_le_id. intros n'. apply bot_lb.
  Qed.

  (** ** Composing layers: reducing associativity to one law

    Composition of layers is [compose], and what makes it a category
    is [apply_assoc].  The lattice-theoretic content of that can be
    discharged completely: both sides are complete homomorphisms in
    [x], so by [ext_unique] they agree as soon as they agree on
    generators, i.e. on single plays.  Carrying out that induction
    shows the only thing missing is [apply_bind] -- substitution
    commutes with sequencing -- used at two instances. *)

  Definition applies_bind {E F} (f : subst E F) :=
    forall A B (h : A -> t F B) (y : t F A),
      apply f (bind h y) = bind (fun a => apply f (h a)) (apply f y).

  Lemma papply_compose {E F G A} (f : subst E F) (g : subst F G)
        (p : play G A) :
    applies_bind f ->
    apply f (papply g p) = papply (compose g f) p.
  Proof.
    intros Hab. induction p as [a | X m | X m n q IHq]; cbn [papply].
    - rewrite apply_emb. reflexivity.
    - rewrite Hab. unfold compose. f_equal.
      apply functional_extensionality. intros _.
      apply (Sup.mor_bot (apply f)).
    - rewrite Hab. unfold compose. f_equal.
      apply functional_extensionality. intros n'.
      rewrite (Sup.mor (f := apply f)). f_equal.
      apply functional_extensionality. intros Hn'. apply IHq.
  Qed.

  Lemma apply_ext_ext {E F G A} (f : subst E F) (g : subst F G) (x : t G A) :
    apply f (apply g x) = ext (fun p => apply f (papply g p)) x.
  Proof.
    unfold apply. apply (ext_ext (ext (papply f)) (papply g)).
  Qed.

  Lemma apply_assoc_of_bind {E F G A} (f : subst E F) (g : subst F G)
        (x : t G A) :
    applies_bind f ->
    apply f (apply g x) = apply (compose g f) x.
  Proof.
    intros Hab. rewrite apply_ext_ext.
    change (apply (compose g f) x) with (ext (papply (compose g f)) x).
    f_equal. apply functional_extensionality. intros p.
    apply papply_compose. assumption.
  Qed.

  Lemma compose_assoc_of_bind {E F G H}
        (f : subst E F) (g : subst F G) (h : subst G H) :
    applies_bind f ->
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros Hab.
    apply PProd.eq_ext. intros ar. apply PProd.eq_ext. intros m.
    apply apply_assoc_of_bind. assumption.
  Qed.

  (** And [apply_bind] itself is again purely a statement about
    single plays: both sides are complete homomorphisms in [y]. *)

  Definition papplies_bind {E F} (f : subst E F) :=
    forall A B (h : A -> t F B) (p : play F A),
      apply f (pbind h p) = bind (fun a => apply f (h a)) (papply f p).

  Lemma apply_bind_ext {E F A B} (f : subst E F) (h : A -> t F B) (y : t F A) :
    apply f (bind h y) = ext (fun p => apply f (pbind h p)) y.
  Proof.
    unfold apply, bind. apply (ext_ext (ext (papply f)) (pbind h)).
  Qed.

  Lemma bind_apply_ext {E F A B} (f : subst E F) (k : A -> t E B) (y : t F A) :
    bind k (apply f y) = ext (fun p => bind k (papply f p)) y.
  Proof.
    unfold bind, apply. apply (ext_ext (ext (pbind k)) (papply f)).
  Qed.

  Lemma applies_bind_pointwise {E F} (f : subst E F) :
    papplies_bind f -> applies_bind f.
  Proof.
    intros H A B h y.
    rewrite apply_bind_ext, bind_apply_ext.
    f_equal. apply functional_extensionality. intros p. apply H.
  Qed.

  (** The first two cases of that induction, for the record. *)

  Lemma papplies_bind_pret {E F A B} (f : subst E F) (h : A -> t F B) (a : A) :
    apply f (pbind h (pret a)) =
    bind (fun a => apply f (h a)) (papply f (pret a)).
  Proof.
    cbn [pbind papply]. rewrite bind_emb. reflexivity.
  Qed.

  Lemma papplies_bind_pmove_le {E F A B X}
        (f : subst E F) (h : A -> t F B) (m : F X) :
    apply f (pbind h (pmove m)) [=
    bind (fun a => apply f (h a)) (papply f (pmove m)).
  Proof.
    cbn [pbind papply]. rewrite apply_emb. cbn [papply].
    transitivity
      (bind (fun _ : X => bind (fun a => apply f (h a)) (bot : t E A)) (f X m)).
    - apply bind_mono. intros n'.
      rewrite (Sup.mor_bot (bind (fun a => apply f (h a)))). reflexivity.
    - apply (bind_bind_le (fun a => apply f (h a)) (fun _ : X => bot : t E A)).
  Qed.

  (** So layer composition is associative as soon as [papplies_bind]
    holds, and that is an induction on a single play with exactly
    three cases.  Spelling them out:

    - [pret a] is an identity, and goes through.

    - [pmove m] asks for
        [bind (fun _ => bot) z = bind k (bind (fun _ => bot) z)],
      i.e. that a computation which discards its value absorbs any
      later continuation.  [bind_bind_le] gives [[=]; the converse is
      the missing half of [bind_bind].

    - [pcons m n q] asks for an *exchange*: writing [z] for
      [pbind h q] and [y] for [f _ m],
        [ext (fun s => bind (c s) y) z
           = bind (fun n' => ext (fun s => c s n') z) y]
      which swaps an extension over the plays of the continuation
      with a bind into the plays of the substituted call.  Neither
      inclusion is available: pushing the [inf]s of one normal form
      past the [join] of the other is codistributivity again, in
      both directions.

    Both obligations are the same phenomenon: [pbind] joins
    [emb (pmove m)] onto its recursive call because [bot] is global,
    and that join then has to cross an [inf].  Note the exchange is
    not a commutation of independent effects -- in [apply f (bind h y)]
    the substituted call [f _ m] runs first and the continuation
    resumes after it, so the two sides enumerate the *same*
    interactions, just bracketed differently.  That is the shape of
    an argument about interaction sequences rather than about
    distributivity, which suggests defining [apply] by a single
    extension over an inductively generated set of interaction
    sequences -- the design of Chapter 7 of the thesis -- instead of
    by nested extensions as here. *)

  (** ** Laws that remain open

    The three laws below were admitted in the classical development
    too, and we do not improve on that here; what has changed is
    that nothing else in this file depends on choice, so the gap is
    now isolated.

    For [apply_int_r] the missing inclusion is
    [f ar m [= apply f (int m)].  Pointwise on plays one does have
    [emb p [= (sup n, pbind (k n) p) || pbind (fun _ => bot) p], but
    turning that into a statement about [f ar m] requires moving a
    [sup] and a [join] out through the [inf]s of the normal form -
    again codistributivity, as for [bind_bind].  [apply_bind] and
    [apply_assoc] additionally require commuting an [ext] over the
    plays of the argument with a [bind] over [f ar m], which does
    not reduce to [codistributive] in any way we have found.

    Note that assuming [codistributive] - equivalently, by
    [codist_lem] below, excluded middle - would not by itself close
    these three: the thesis proves them (Lemma 6.7) by induction on
    plays using properties of FCD, and that argument has simply not
    been carried out here.

    The [IRun] module at the end of this file shows that all three
    *are* available constructively once the demonic side is dropped:
    there [rcompose_rid_l] is [apply_int_r], [rcompose_assoc] is
    [apply_assoc], and no [applies_bind] hypothesis is needed,
    because substitution is a single [sup]-extension over an
    inductively generated relation rather than two nested
    [FCD.ext]s.  So the obstruction is not interaction; it is the
    [inf] that [FCD] interposes. *)

  Lemma apply_int_r {E F ar} (m : F ar) (f : subst E F) :
    apply f (int m) = f ar m.
  Admitted.

  Lemma apply_bind {E F A B} (f : subst E F) (g : A -> t F B) (x : t F A) :
    apply f (bind g x) = bind (fun a => apply f (g a)) (apply f x).
  Admitted.

  Lemma apply_assoc {E F G A} (f : subst E F) (g : subst F G) (x : t G A) :
    apply f (apply g x) = apply (compose g f) x.
  Admitted.

  (** ** Properties of [compose] *)

  Lemma compose_int_l {E F} (f : subst E F) :
    compose (@int F) f = f.
  Proof.
    apply PProd.eq_ext. intros ar. apply PProd.eq_ext. intros m.
    apply apply_int_r.
  Qed.

  Lemma compose_assoc {E F G H} (f : subst E F) (g : subst F G) (h : subst G H) :
    compose (compose h g) f = compose h (compose g f).
  Proof.
    apply PProd.eq_ext. intros ar. apply PProd.eq_ext. intros m.
    apply apply_assoc.
  Qed.

End ISpec.

Abbreviation ispec := ISpec.t.

(** * The strength of the [bind_bind] hypothesis

  Putting the pieces together: the hypothesis under which [bind_bind]
  was proved is, for the interaction specification lattice, neither
  more nor less than excluded middle.  It needs no choice, which is
  what the classical development's [Lattice.inf_sup] required. *)

Lemma codist_t_iff (E : esig) (V : Type) :
  codistributive (ISpec.t E V) <-> lem.
Proof.
  split.
  - apply (codist_lem (Upset.Fpos (ISpec.play_poset E V))
                      (uempty (ISpec.play_poset E V))).
  - apply lem_codist.
Qed.

Corollary bind_bind_lem {E A B C} (g : B -> ISpec.t E C) (f : A -> ISpec.t E B)
          (x : ISpec.t E A) :
  lem -> ISpec.bind g (ISpec.bind f x) = ISpec.bind (fun a => ISpec.bind g (f a)) x.
Proof.
  intros Hlem. apply ISpec.bind_bind. apply codist_t_iff. assumption.
Qed.




(** * Substitution as a single extension over interaction sequences

  [ISpec.papply] consumes the substituted call [f _ m] with an [ext]
  nested inside the recursion on the outer play, so a play with [k]
  moves costs [k] nested extensions; re-bracketing them is the
  exchange law that [ISpec.papplies_bind] got stuck on.

  The alternative is to generate the interactions inductively and
  take *one* extension over them: the angel picks a global
  interaction sequence, and the result is its external projection.
  [Downset.dext2_comm] is what makes this legitimate -- in a
  downset lattice two extensions commute outright, so there is no
  preferred bracketing to begin with.

  We carry that out here for the angelic model [s E A], which is the
  shape of the Chapter 7 model of the thesis: strategies as
  prefix-closed sets of plays, with the polarity in the game rather
  than in the lattice. *)

Module IRun.

  Import ISpec.

  Definition s (E : esig) (A : Type) : ccdlattice :=
    Downset.F (play_poset E A).

  Definition rsubst (E F : esig) := forall ar, F ar -> s E ar.

  (** [pend r u]: the call observed as [r] never returned, and [u]
    is that same sequence of moves and answers read as a play of the
    ambient type. *)

  Inductive pend {E : esig} {X A} : play E X -> play E A -> Prop :=
    | pend_move {Y} (m : E Y) :
        pend (pmove m) (pmove m)
    | pend_cons {Y} (m : E Y) (n : Y) (r : play E X) (u : play E A) :
        pend r u -> pend (pcons m n r) (pcons m n u).

  (** [graft r n v u]: the call observed as [r] returned [n], and [u]
    is [r] with that return replaced by the continuation [v]. *)

  Inductive graft {E : esig} {X A} : play E X -> X -> play E A -> play E A -> Prop :=
    | graft_ret (n : X) (v : play E A) :
        graft (pret n) n v v
    | graft_cons {Y} (m : E Y) (k : Y) (r : play E X)
                 (n : X) (v u : play E A) :
        graft r n v u -> graft (pcons m k r) n v (pcons m k u).

  (** The interaction sequences themselves, generated inductively.
    They are indexed by a *family of predicates* rather than by a
    substitution: that way we can see later exactly which closure
    property of the family each half of associativity uses, which is
    what tells us whether the construction lifts to the dual
    (demonic) setting.  [runs P p u] says the outer play [p], each of
    whose moves is answered by a play admitted by [P], is observed
    externally as [u]. *)

  Definition rspec (E F : esig) := forall ar, F ar -> play E ar -> Prop.

  Inductive runs {E F : esig} (P : rspec E F) {A}
    : play F A -> play E A -> Prop :=
    | runs_ret (a : A) :
        runs P (pret a) (pret a)
    | runs_pend {X} (m : F X) (r : play E X) (u : play E A) :
        P X m r -> pend r u ->
        runs P (pmove m) u
    | runs_cons {X} (m : F X) (n : X) (q : play F A)
                (r : play E X) (v u : play E A) :
        P X m r -> runs P q v -> graft r n v u ->
        runs P (pcons m n q) u
    | runs_cons_pend {X} (m : F X) (n : X) (q : play F A)
                     (r : play E X) (u : play E A) :
        P X m r -> pend r u ->
        runs P (pcons m n q) u.

  (** A substitution induces such a family, and it is downward closed
    because each [f ar m] is a downset. *)

  Definition rhas {E F} (f : rsubst E F) : rspec E F :=
    fun ar m r => Downset.has (f ar m) r.

  Lemma rhas_dcl {E F} (f : rsubst E F) ar (m : F ar) :
    dcl (C := play_poset E ar) (rhas f ar m).
  Proof.
    apply Downset.has_closed.
  Qed.

  (** The external projection of all interactions of a single outer
    play, and then substitution as a *single* extension. *)

  Definition prun {E F} (f : rsubst E F) {A} (p : play F A) : s E A :=
    sup {u | runs (rhas f) p u}, (@Downset.emb (play_poset E A) u : s E A).

  Definition rapply {E F A} (f : rsubst E F) : s F A -> s E A :=
    Downset.dext (prun f : play_poset F A -> s E A).

  Global Instance rapply_sup {E F A} (f : rsubst E F) :
    Sup.Morphism (@rapply E F A f).
  Proof.
    unfold rapply. apply Downset.dext_sup.
  Qed.


  (** ** Monotonicity

    [graft] is monotonic in the continuation it grafts in, and a
    longer outer play admits a longer interaction.  Together these
    make [prun f] a poset morphism, which is what ties [rapply] to
    its generators. *)

  Lemma graft_mono {E : esig} {X A} (r : play E X) (n : X) (v u : play E A) :
    graft r n v u ->
    forall v', pref v v' -> exists u', graft r n v' u' /\ pref u u'.
  Proof.
    intros Hg. induction Hg as [n0 v0 | Y m k r0 n0 v0 u0 Hg IH].
    - intros v' Hv. exists v'. split; [constructor | assumption].
    - intros v' Hv. destruct (IH v' Hv) as [u'' [Hu'' Huu'']].
      exists (pcons m k u''). split; constructor; assumption.
  Qed.

  Lemma runs_pref {E F : esig} (P : rspec E F) {A} (p q : play F A) :
    pref p q ->
    forall u, runs P p u -> exists u', runs P q u' /\ pref u u'.
  Proof.
    intros Hpq.
    induction Hpq as [v | N m | N m n s | N m n s t Hst IH]; intros u Hu.
    - exists u. split; [assumption | apply pref_refl].
    - exists u. split; [assumption | apply pref_refl].
    - inversion Hu; depsubst.
      exists u. split; [ | apply pref_refl].
      eapply runs_cons_pend; eassumption.
    - inversion Hu; depsubst.
      + destruct (IH _ H5) as [v' [Hv' Hvv']].
        destruct (graft_mono _ _ _ _ H6 _ Hvv') as [u' [Hg Huu']].
        exists u'. split; [ | assumption].
        eapply runs_cons; eassumption.
      + exists u. split; [ | apply pref_refl].
        eapply runs_cons_pend; eassumption.
  Qed.

  Global Instance prun_pmor {E F A} (f : rsubst E F) :
    PosetMorphism (prun f : play_poset F A -> s E A).
  Proof.
    intros p q Hpq. apply fsup_lub. intros u Hu.
    edestruct (runs_pref (rhas f) p q Hpq u Hu) as (u' & Hu' & Huu').
    apply (fsup_at u'); auto.
    apply Downset.emb_mor. assumption.
  Qed.

  Lemma rapply_emb {E F A} (f : rsubst E F) (p : play F A) :
    rapply f (@Downset.emb (play_poset F A) p) = prun f p.
  Proof.
    unfold rapply.
    apply (Downset.dext_ana (prun f : play_poset F A -> s E A)).
  Qed.
  (** ** Structural lemmas on [pend] and [graft]

    [pend] and [graft] are the two ways the interaction of a single
    outer move with its implementation can end: either the inner play
    never returns, and is simply re-read at the ambient result type,
    or it returns and its [pret] is replaced by the continuation.
    The lemmas below are the equations those two operations satisfy.
    Everything after this point is an induction on [runs] which uses
    nothing but these equations -- in particular no lattice identity,
    and so no distributivity. *)

  (** A play either returns a value or ends in an unanswered move,
    and which of the two is decided by structural recursion.  This is
    the only "case analysis on a disjunction" the development needs,
    and it is why layer composition does not run into the excluded
    middle the way [ISpec.apply_int_r] does. *)

  Fixpoint pval {E : esig} {X} (p : play E X) : option X :=
    match p with
      | pret v => Some v
      | pmove _ => None
      | pcons _ _ q => pval q
    end.

  Lemma pval_pend {E : esig} {X} (p : play E X) :
    pval p = None -> pend p p.
  Proof.
    induction p as [v | Y m | Y m n q IHq]; cbn.
    - discriminate.
    - constructor.
    - intro. constructor. auto.
  Qed.

  Lemma pval_graft {E : esig} {X} (p : play E X) (v : X) :
    pval p = Some v -> graft p v (pret v) p.
  Proof.
    induction p as [w | Y m | Y m n q IHq]; cbn.
    - intro H. injection H as H. subst. constructor.
    - discriminate.
    - intro. constructor. auto.
  Qed.

  (** [pend] is retyping, so it is functional up to the result type,
    transitive, and the identity when the two types agree. *)

  Lemma pend_retype {E : esig} {X A} B (r : play E X) (u : play E A) :
    pend r u -> exists u' : play E B, pend r u'.
  Proof.
    intros H. induction H as [Y m | Y m n r0 u0 H IH].
    - exists (pmove m). constructor.
    - destruct IH as [u' Hu']. exists (pcons m n u'). constructor. assumption.
  Qed.

  Lemma pend_trans {E : esig} {X Y A}
        (r : play E X) (t : play E Y) (w : play E A) :
    pend r t -> pend t w -> pend r w.
  Proof.
    intros H. revert w.
    induction H as [Z m | Z m n r0 t0 H IH]; intros w Hw;
      inversion Hw; depsubst; constructor; auto.
  Qed.

  Lemma pend_compose {E : esig} {X Y A}
        (r : play E X) (t : play E Y) (w : play E A) :
    pend r t -> pend r w -> pend t w.
  Proof.
    intros H. revert w.
    induction H as [Z m | Z m n r0 t0 H IH]; intros w Hw;
      inversion Hw; depsubst; constructor; auto.
  Qed.

  Lemma pend_same {E : esig} {X} (r u : play E X) :
    pend r u -> r = u.
  Proof.
    induction 1; congruence.
  Qed.

  (** A play in the image of [pend] never returns, so it cannot be
    grafted onto. *)

  Lemma pend_graft_absurd {E : esig} {X Y A}
        (r : play E X) (u : play E Y) (n : Y) (v w : play E A) :
    pend r u -> graft u n v w -> False.
  Proof.
    intros Hp. revert v w. induction Hp as [Z m | Z m k r0 u0 Hp IH];
      intros v w Hg; inversion Hg; depsubst.
    eapply IH; eassumption.
  Qed.

  (** [graft] is total in the play it grafts in, associative, and
    propagates both [pend] and prefixes. *)

  Lemma graft_total {E : esig} {X A B} (r : play E X) (n : X)
        (v u : play E A) (v' : play E B) :
    graft r n v u -> exists u' : play E B, graft r n v' u'.
  Proof.
    intros Hg. induction Hg as [k v0 | Y m k r0 n0 v0 u0 Hg IH].
    - exists v'. constructor.
    - destruct IH as [u' Hu']. exists (pcons m k u'). constructor. assumption.
  Qed.

  Lemma graft_assoc {E : esig} {Y Z A} (r : play E Y) (k : Y)
        (t0 : play E Z) (n : Z) (v' v1 w : play E A) :
    graft r k v1 w -> graft t0 n v' v1 ->
    exists t : play E Z, graft r k t0 t /\ graft t n v' w.
  Proof.
    intros Hg. revert t0 n v'.
    induction Hg as [k0 v0 | W m j r0 k0 v0 u0 Hg IH]; intros t0 n v' Ht.
    - exists t0. split; [constructor | assumption].
    - destruct (IH t0 n v' Ht) as (t & Ht1 & Ht2).
      exists (pcons m j t). split; constructor; assumption.
  Qed.

  Lemma graft_assoc_inv {E : esig} {Y X A} (r1 : play E Y) (k : Y)
        (v' r : play E X) (n : X) (v w : play E A) :
    graft r1 k v' r -> graft r n v w ->
    exists v'' : play E A, graft v' n v v'' /\ graft r1 k v'' w.
  Proof.
    intros Hg. revert n v w.
    induction Hg as [k0 v0 | W m j r0 k0 v0 u0 Hg IH]; intros n v w Hw.
    - exists w. split; [assumption | constructor].
    - inversion Hw; depsubst.
      match goal with Hx : graft u0 _ _ _ |- _ =>
        destruct (IH n v _ Hx) as (v'' & Hv1 & Hv2) end.
      exists v''. split; [assumption | constructor; assumption].
  Qed.

  Lemma graft_pend {E : esig} {Y Z A} (r : play E Y) (k : Y)
        (t0 t : play E Z) (v1 w : play E A) :
    graft r k t0 t -> graft r k v1 w -> pend t0 v1 -> pend t w.
  Proof.
    intros Hg. revert v1 w.
    induction Hg as [k0 v0 | W m j r0 k0 v0 u0 Hg IH]; intros v1 w Hw Hp.
    - inversion Hw; depsubst. assumption.
    - inversion Hw; depsubst. constructor. eapply IH; eassumption.
  Qed.

  Lemma graft_pret {E : esig} {X} (r w v : play E X) (n : X) :
    graft r n v w -> v = pret n -> w = r.
  Proof.
    induction 1 as [k0 v0 | Y m k r0 n0 v0 u0 Hg IH]; intros Hv; subst.
    - reflexivity.
    - f_equal. apply IH. reflexivity.
  Qed.

  Lemma graft_pend_inv {E : esig} {X B A} (r : play E X) (n : X)
        (v u : play E B) (w : play E A) :
    graft r n v u -> pend u w ->
    exists wv : play E A, pend v wv /\ graft r n wv w.
  Proof.
    intros Hg. revert w.
    induction Hg as [k0 v0 | W m j r0 k0 v0 u0 Hg IH]; intros w Hw.
    - exists w. split; [assumption | constructor].
    - inversion Hw; depsubst.
      match goal with Hx : pend u0 _ |- _ =>
        destruct (IH _ Hx) as (wv & Hv1 & Hv2) end.
      exists wv. split; [assumption | constructor; assumption].
  Qed.

  Lemma pend_pref {E : esig} {X A} (r : play E X) (u u' : play E A) :
    pend r u -> pref u' u ->
    exists r' : play E X, pref r' r /\ pend r' u'.
  Proof.
    intros Hp. revert u'.
    induction Hp as [Z m | Z m n r0 u0 Hp IH]; intros u' Hu.
    - inversion Hu; depsubst. exists (pmove m). split; constructor.
    - inversion Hu; depsubst.
      + exists (pmove m). split; constructor.
      + match goal with Hx : pref _ u0 |- _ =>
          destruct (IH _ Hx) as (r' & Hr1 & Hr2) end.
        exists (pcons m n r'). split; constructor; assumption.
  Qed.

  Lemma graft_pref {E : esig} {X A} (r : play E X) (n : X) (v u u' : play E A) :
    graft r n v u -> pref u' u ->
    (exists v' : play E A, pref v' v /\ graft r n v' u') \/
    (exists r' : play E X, pref r' r /\ pend r' u').
  Proof.
    intros Hg. revert u'.
    induction Hg as [k0 v0 | W m j r0 k0 v0 u0 Hg IH]; intros u' Hu.
    - left. exists u'. split; [assumption | constructor].
    - inversion Hu; depsubst.
      + right. exists (pmove m). split; constructor.
      + match goal with Hx : pref _ u0 |- _ =>
          destruct (IH _ Hx) as [(v' & Hv1 & Hv2) | (r' & Hr1 & Hr2)] end.
        * left. exists v'. split; [assumption | constructor; assumption].
        * right. exists (pcons m j r'). split; constructor; assumption.
  Qed.

  (** ** [runs] is downward closed in its observation

    This is what makes the whole approach work: because each [f _ m]
    is a downset, a prefix of an observed interaction is itself an
    observed interaction.  Consequently [prun] and [rapply] are
    *exactly* described by [runs] -- no prefix slack to carry around
    -- which is what lets associativity be stated as an equivalence
    between inductive relations. *)

  Lemma runs_down {E F} (P : rspec E F)
        (HP : forall ar (m : F ar), dcl (C := play_poset E ar) (P ar m))
        {A} (p : play F A) (u u' : play E A) :
    runs P p u -> pref u' u -> runs P p u'.
  Proof.
    intros Hr. revert u'.
    induction Hr as [ a
                    | X m r u Hr Hp
                    | X m n q r v u Hr Hv IH Hg
                    | X m n q r u Hr Hp ]; intros u' Hu'.
    - inversion Hu'; depsubst. constructor.
    - destruct (pend_pref _ _ _ Hp Hu') as (r' & Hr1 & Hr2).
      assert (P X m r') as Hr'0 by (eapply HP; eassumption).
      eapply runs_pend; eassumption.
    - destruct (graft_pref _ _ _ _ _ Hg Hu')
        as [(v' & Hv1 & Hv2) | (r' & Hr1 & Hr2)].
      + assert (runs P q v') as Hqv by (apply IH; assumption).
        eapply runs_cons; eassumption.
      + assert (P X m r') as Hr'0 by (eapply HP; eassumption).
        eapply runs_cons_pend; eassumption.
    - destruct (pend_pref _ _ _ Hp Hu') as (r' & Hr1 & Hr2).
      assert (P X m r') as Hr'0 by (eapply HP; eassumption).
      eapply runs_cons_pend; eassumption.
  Qed.

  Lemma prun_has {E F} (f : rsubst E F) {A} (p : play F A) (u : play E A) :
    Downset.has (prun f p) u <-> runs (rhas f) p u.
  Proof.
    unfold prun. rewrite Downset.has_fsup. split.
    - intros (w & Hw & Hu). cbn in Hu.
      eapply (runs_down (rhas f) (rhas_dcl f)); eassumption.
    - intros H. exists u. split; auto. cbn. apply pref_refl.
  Qed.

  Lemma rapply_has {E F A} (f : rsubst E F) (x : s F A) (w : play E A) :
    Downset.has (rapply f x) w <->
    exists p : play F A, Downset.has x p /\ runs (rhas f) p w.
  Proof.
    unfold rapply, Downset.dext. rewrite Downset.has_fsup.
    split; intros (p & Hp & Hw); exists p; split; auto; apply prun_has; auto.
  Qed.
  (** ** Composition of substitutions *)

  Definition rcompose {E F G} (g : rsubst F G) (f : rsubst E F) : rsubst E G :=
    fun ar m => rapply f (g ar m).

  (** ** Associativity, left to right

    Given an interaction of [p] with [g] observed as [u], and an
    interaction of [u] with [f] observed as [w], the composite
    [rcompose g f] observes [w] directly.  Everything is an induction
    on the inductive relations; the two auxiliary lemmas say how an
    interaction of the *inner* play travels through [pend] and
    [graft]. *)

  Lemma runs_pend_fwd {E F} (P : rspec E F) {X A}
        (r : play F X) (u : play F A) (w : play E A) :
    pend r u -> runs P u w ->
    exists t : play E X, runs P r t /\ pend t w.
  Proof.
    intros Hp. revert w.
    induction Hp as [Z m | Z m n r0 u0 Hp IH]; intros w Hw.
    - inversion Hw; depsubst.
      match goal with Hr : P Z m ?r1, Hq : pend ?r1 w |- _ =>
        destruct (pend_retype X _ _ Hq) as (t & Ht);
        exists t; split;
          [ eapply runs_pend; eassumption
          | eapply pend_compose; eassumption ]
      end.
    - inversion Hw; depsubst.
      + match goal with
          | Hr : P Z m ?r1, Hv : runs P u0 ?v,
            Hg : graft ?r1 n ?v w |- _ =>
            destruct (IH _ Hv) as (t0 & Ht0 & Hpt0);
            destruct (graft_total _ _ _ _ t0 Hg) as (t & Ht);
            exists t; split;
              [ eapply runs_cons; eassumption
              | eapply graft_pend; eassumption ]
        end.
      + match goal with Hr : P Z m ?r1, Hq : pend ?r1 w |- _ =>
          destruct (pend_retype X _ _ Hq) as (t & Ht);
          exists t; split;
            [ eapply runs_cons_pend; eassumption
            | eapply pend_compose; eassumption ]
        end.
  Qed.

  Lemma runs_graft_fwd {E F} (P : rspec E F) {X B}
        (r : play F X) (n : X) (v u : play F B) (w : play E B) :
    graft r n v u -> runs P u w ->
    (exists (t : play E X) (v' : play E B),
       runs P r t /\ runs P v v' /\ graft t n v' w) \/
    (exists t : play E X, runs P r t /\ pend t w).
  Proof.
    intros Hg. revert w.
    induction Hg as [k0 v0 | Z m j r0 k0 v0 u0 Hg IH]; intros w Hw.
    - left. exists (pret k0), w. split; [ | split ].
      + constructor.
      + assumption.
      + constructor.
    - inversion Hw; depsubst.
      + match goal with
          | Hr : P Z m ?r1, Hv : runs P u0 ?v1,
            Hgr : graft ?r1 j ?v1 w |- _ =>
            destruct (IH _ Hv) as
              [ (t0 & v' & Ht0 & Hv' & Hgt) | (t0 & Ht0 & Hpt) ]
        end.
        * match goal with
            | Hr : P Z m ?r1, Hgr : graft ?r1 j ?v1 w,
              Hgt : graft t0 k0 v' ?v1 |- _ =>
              destruct (graft_assoc _ _ t0 _ _ _ _ Hgr Hgt) as (t & Hg1 & Hg2);
              left; exists t, v'; split; [ | split ];
                [ eapply runs_cons; eassumption
                | assumption
                | assumption ]
          end.
        * match goal with
            | Hr : P Z m ?r1, Hgr : graft ?r1 j ?v1 w |- _ =>
              destruct (graft_total _ _ _ _ t0 Hgr) as (t & Ht);
              right; exists t; split;
                [ eapply runs_cons; eassumption
                | eapply graft_pend; eassumption ]
          end.
      + match goal with Hr : P Z m ?r1, Hq : pend ?r1 w |- _ =>
          destruct (pend_retype X _ _ Hq) as (t & Ht);
          right; exists t; split;
            [ eapply runs_cons_pend; eassumption
            | eapply pend_compose; eassumption ]
        end.
  Qed.

  (** Composition of generator families: [scompose Pg Pf] describes
    what one [G]-move does when its [F]-implementation is given by
    [Pg] and the resulting [F]-play is in turn run under [Pf]. *)

  Definition scompose {E F G} (Pg : rspec F G) (Pf : rspec E F) : rspec E G :=
    fun ar m w => exists p : play F ar, Pg ar m p /\ runs Pf p w.

  Lemma runs_scompose_fwd {E F G} (Pf : rspec E F) (Pg : rspec F G) {A}
        (p : play G A) (u : play F A) (w : play E A) :
    runs Pg p u -> runs Pf u w -> runs (scompose Pg Pf) p w.
  Proof.
    intros Hr. revert w.
    induction Hr as [ a
                    | X m r u Hr Hp
                    | X m n q r v u Hr Hv IH Hg
                    | X m n q r u Hr Hp ]; intros w Hw.
    - inversion Hw; depsubst. constructor.
    - destruct (runs_pend_fwd Pf _ _ _ Hp Hw) as (t & Ht & Hpt).
      assert (scompose Pg Pf X m t) as Hct by (eexists; split; eassumption).
      eapply runs_pend; eassumption.
    - destruct (runs_graft_fwd Pf _ _ _ _ _ Hg Hw)
        as [ (t & v' & Ht & Hv' & Hgt) | (t & Ht & Hpt) ].
      + assert (scompose Pg Pf X m t) as Hct by (eexists; split; eassumption).
        assert (runs (scompose Pg Pf) q v') as Hqv by (apply IH; assumption).
        eapply runs_cons; eassumption.
      + assert (scompose Pg Pf X m t) as Hct by (eexists; split; eassumption).
        eapply runs_cons_pend; eassumption.
    - destruct (runs_pend_fwd Pf _ _ _ Hp Hw) as (t & Ht & Hpt).
      assert (scompose Pg Pf X m t) as Hct by (eexists; split; eassumption).
      eapply runs_cons_pend; eassumption.
  Qed.

  (** ** Associativity, right to left

    Conversely, an interaction of [p] with the composite splits.  The
    two auxiliary lemmas are the inverses of the previous pair: if
    running [r0] under [f] produced something that ends pending, then
    some prefix of [r0] was already pending (and a prefix is still
    available, since each [g _ m] is a downset); and if it produced
    something that returns, then [r0] returned too and the graft can
    be performed one level up. *)

  Lemma runs_pend_bwd {E F} (P : rspec E F) {X A}
        (r0 : play F X) (r : play E X) (w : play E A) :
    runs P r0 r -> pend r w ->
    exists (r0' : play F X) (uu : play F A),
      pref r0' r0 /\ pend r0' uu /\ runs P uu w.
  Proof.
    intros Hr. revert w.
    induction Hr as [ a
                    | Z m r1 r Hr1 Hp
                    | Z m j q' r1 v r Hr1 Hv IH Hg
                    | Z m j q' r1 r Hr1 Hp ]; intros w Hw.
    - inversion Hw.
    - exists (pmove m), (pmove m). split; [ | split ].
      + apply pref_refl.
      + constructor.
      + eapply runs_pend; [ eassumption | eapply pend_trans; eassumption ].
    - destruct (graft_pend_inv _ _ _ _ _ Hg Hw) as (wv & Hpv & Hgw).
      destruct (IH _ Hpv) as (q'' & uuv & Hq1 & Hq2 & Hq3).
      exists (pcons m j q''), (pcons m j uuv). split; [ | split ].
      + constructor. assumption.
      + constructor. assumption.
      + eapply runs_cons; eassumption.
    - exists (pmove m), (pmove m). split; [ | split ].
      + constructor.
      + constructor.
      + eapply runs_pend; [ eassumption | eapply pend_trans; eassumption ].
  Qed.

  Lemma runs_graft_bwd {E F} (P : rspec E F) {X A}
        (r0 : play F X) (r : play E X) (n : X)
        (v w : play E A) (v0 : play F A) :
    runs P r0 r -> graft r n v w -> runs P v0 v ->
    exists uu : play F A, graft r0 n v0 uu /\ runs P uu w.
  Proof.
    intros Hr. revert n v w v0.
    induction Hr as [ a
                    | Z m r1 r Hr1 Hp
                    | Z m j q' r1 v' r Hr1 Hv IH Hg
                    | Z m j q' r1 r Hr1 Hp ]; intros n v w v0 Hgw Hv0.
    - inversion Hgw; depsubst.
      exists v0. split; [constructor | assumption].
    - exfalso. eapply pend_graft_absurd; eassumption.
    - destruct (graft_assoc_inv _ _ _ _ _ _ _ Hg Hgw) as (v'' & Hg1 & Hg2).
      destruct (IH _ _ _ _ Hg1 Hv0) as (uuq & Hu1 & Hu2).
      exists (pcons m j uuq). split.
      + constructor. assumption.
      + eapply runs_cons; eassumption.
    - exfalso. eapply pend_graft_absurd; eassumption.
  Qed.

  Lemma runs_scompose_bwd {E F G} (Pf : rspec E F) (Pg : rspec F G)
        (HPg : forall ar (m : G ar), dcl (C := play_poset F ar) (Pg ar m))
        {A} (p : play G A) (w : play E A) :
    runs (scompose Pg Pf) p w ->
    exists u : play F A, runs Pg p u /\ runs Pf u w.
  Proof.
    intros Hr.
    induction Hr as [ a
                    | X m r w Hr Hp
                    | X m n q r v w Hr Hv IH Hg
                    | X m n q r w Hr Hp ].
    - exists (pret a). split; constructor.
    - unfold scompose in Hr. destruct Hr as (r0 & Hr0 & Hrr).
      destruct (runs_pend_bwd Pf _ _ _ Hrr Hp) as (r0' & uu & H1 & H2 & H3).
      exists uu. split; [ | assumption ].
      eapply runs_pend; [ | eassumption ].
      eapply HPg; eassumption.
    - unfold scompose in Hr. destruct Hr as (r0 & Hr0 & Hrr).
      destruct IH as (uq & Hq1 & Hq2).
      destruct (runs_graft_bwd Pf _ _ _ _ _ _ Hrr Hg Hq2) as (uu & Hu1 & Hu2).
      exists uu. split; [ | assumption ].
      eapply runs_cons; eassumption.
    - unfold scompose in Hr. destruct Hr as (r0 & Hr0 & Hrr).
      destruct (runs_pend_bwd Pf _ _ _ Hrr Hp) as (r0' & uu & H1 & H2 & H3).
      exists uu. split; [ | assumption ].
      eapply runs_cons_pend; [ | eassumption ].
      eapply HPg; eassumption.
  Qed.

  (** ** Layer composition is associative, constructively

    The two directions above say that splitting an interaction at the
    [F] layer and splitting it at the [G] layer observe the same
    [E]-plays.  No choice, no excluded middle, no distributivity.

    Note what each half needed.  Left to right,
    [runs_scompose_fwd] assumes *nothing* about the generator
    families: it is bookkeeping on [pend] and [graft].  Right to
    left, [runs_scompose_bwd] needs the outer family to be downward
    closed, and genuinely so -- see [scompose_bwd_needs_dcl] below.
    For an [rsubst] that closure is free, since each [g ar m] is a
    downset, and this is the one place where being in the angelic
    model is doing work. *)

  Lemma rhas_rcompose {E F G} (g : rsubst F G) (f : rsubst E F) :
    rhas (rcompose g f) = scompose (rhas g) (rhas f).
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    apply functional_extensionality. intros w.
    apply propositional_extensionality.
    unfold rhas, rcompose, scompose. apply rapply_has.
  Qed.

  Theorem runs_rcompose {E F G} (f : rsubst E F) (g : rsubst F G) {A}
          (p : play G A) (w : play E A) :
    runs (rhas (rcompose g f)) p w <->
    exists u : play F A, runs (rhas g) p u /\ runs (rhas f) u w.
  Proof.
    rewrite rhas_rcompose. split.
    - apply (runs_scompose_bwd (rhas f) (rhas g) (rhas_dcl g)).
    - intros (u & Hu & Hw). eapply runs_scompose_fwd; eassumption.
  Qed.

  Theorem rapply_assoc {E F G A} (f : rsubst E F) (g : rsubst F G) (x : s G A) :
    rapply f (rapply g x) = rapply (rcompose g f) x.
  Proof.
    apply Downset.has_eq. intros w. split.
    - intros H. apply rapply_has in H as (u & Hu & Hw).
      apply rapply_has in Hu as (p & Hp & Hu).
      apply rapply_has. exists p. split; [assumption | ].
      apply runs_rcompose. eauto.
    - intros H. apply rapply_has in H as (p & Hp & Hw).
      apply runs_rcompose in Hw as (u & Hu & Hw).
      apply rapply_has. exists u. split; [ | assumption ].
      apply rapply_has. eauto.
  Qed.

  Theorem rcompose_assoc {E F G K}
          (f : rsubst E F) (g : rsubst F G) (h : rsubst G K) :
    rcompose (rcompose h g) f = rcompose h (rcompose g f).
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    apply (rapply_assoc f g (h ar m)).
  Qed.

  (** ** The identity substitution

    [rid] is the angelic reading of [ISpec.int]: the implementation
    of a move is to play that very move and hand back whatever answer
    comes, or to stop before the answer arrives. *)

  Definition rid (E : esig) : rsubst E E :=
    fun ar m =>
      sup k : option ar,
        (@Downset.emb (play_poset E ar)
           (match k with
              | Some n => pcons m n (pret n)
              | None   => pmove m
            end) : s E ar).

  Lemma pref_pret_inv {E : esig} {A} (v : A) (p : play E A) :
    pref p (pret v) -> p = pret v.
  Proof.
    inversion 1; reflexivity.
  Qed.

  Lemma pref_int_inv {E : esig} {X} (m : E X) (n : X) (r : play E X) :
    pref r (pcons m n (pret n)) ->
    r = pmove m \/ r = pcons m n (pret n).
  Proof.
    intros H. inversion H; depsubst.
    - left. reflexivity.
    - right.
      match goal with Hx : pref ?s (pret n) |- _ =>
        apply pref_pret_inv in Hx; subst; reflexivity end.
  Qed.

  Lemma rid_pmove {E : esig} {X} (m : E X) :
    Downset.has (rid E X m) (pmove m).
  Proof.
    unfold rid. rewrite Downset.has_lsup. exists None. cbn. apply pref_refl.
  Qed.

  Lemma rid_pcons {E : esig} {X} (m : E X) (n : X) :
    Downset.has (rid E X m) (pcons m n (pret n)).
  Proof.
    unfold rid. rewrite Downset.has_lsup. exists (Some n). cbn.
    apply pref_refl.
  Qed.

  Lemma rid_has_inv {E : esig} {X} (m : E X) (r : play E X) :
    Downset.has (rid E X m) r ->
    r = pmove m \/ exists n : X, r = pcons m n (pret n).
  Proof.
    unfold rid. rewrite Downset.has_lsup. intros [k Hk]. cbn in Hk.
    destruct k as [n | ].
    - destruct (pref_int_inv m n r Hk) as [Hr | Hr].
      + left. assumption.
      + right. exists n. assumption.
    - left. inversion Hk; depsubst. reflexivity.
  Qed.

  (** Running a play against [rid] observes exactly its prefixes. *)

  Lemma runs_rid {E : esig} {A} (p u : play E A) :
    runs (rhas (rid E)) p u <-> pref u p.
  Proof.
    split.
    - intros Hr.
      induction Hr as [ a
                      | X m r u Hr Hp
                      | X m n q r v u Hr Hv IH Hg
                      | X m n q r u Hr Hp ].
      + apply pref_refl.
      + apply rid_has_inv in Hr as [Hr | (n & Hr)]; subst.
        * inversion Hp; depsubst. apply pref_refl.
        * inversion Hp; depsubst.
          match goal with Hx : pend (pret n) _ |- _ => inversion Hx end.
      + apply rid_has_inv in Hr as [Hr | (n' & Hr)]; subst.
        * inversion Hg.
        * inversion Hg; depsubst.
          match goal with Hx : graft (pret n') n v _ |- _ =>
            inversion Hx; depsubst end.
          constructor. assumption.
      + apply rid_has_inv in Hr as [Hr | (n' & Hr)]; subst.
        * inversion Hp; depsubst. constructor.
        * inversion Hp; depsubst.
          match goal with Hx : pend (pret n') _ |- _ => inversion Hx end.
    - intros Hu.
      induction Hu as [ v | N m | N m n s | N m n s t Hst IH ].
      + constructor.
      + eapply runs_pend; [ apply rid_pmove | constructor ].
      + eapply runs_cons_pend; [ apply rid_pmove | constructor ].
      + eapply runs_cons; [ apply rid_pcons | eassumption | ].
        constructor. constructor.
  Qed.

  Theorem rapply_rid {E A} (x : s E A) :
    rapply (rid E) x = x.
  Proof.
    apply Downset.has_eq. intros w. split.
    - intros H. apply rapply_has in H as (p & Hp & Hw).
      apply runs_rid in Hw. eapply Downset.has_closed; eassumption.
    - intros H. apply rapply_has. exists w. split; [assumption | ].
      apply runs_rid. apply pref_refl.
  Qed.

  Theorem rcompose_rid_r {E F} (f : rsubst E F) :
    rcompose f (rid E) = f.
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    apply rapply_rid.
  Qed.

  (** The other unit law is the analogue of [ISpec.apply_int_r],
    which is one of the three laws the FCD model leaves admitted.
    Here it goes through: the case analysis it needs is whether the
    play [w] returns a value or ends in an unanswered move, and that
    is decided by [pval], not by excluded middle. *)

  Theorem rcompose_rid_l {E F} (f : rsubst E F) :
    rcompose (rid F) f = f.
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    apply Downset.has_eq. intros w.
    unfold rcompose. rewrite rapply_has. split.
    - intros (p & Hp & Hw).
      apply rid_has_inv in Hp as [Hp | (n & Hp)]; subst.
      + inversion Hw; depsubst.
        match goal with Hq : pend ?r1 w |- _ =>
          apply pend_same in Hq; subst; assumption end.
      + inversion Hw; depsubst.
        * match goal with Hv : runs (rhas f) (pret n) _ |- _ =>
            inversion Hv; depsubst end.
          match goal with Hg : graft ?r1 n (pret n) w |- _ =>
            assert (w = r1) as Hw0
              by (eapply graft_pret; [eassumption | reflexivity]);
            subst; assumption
          end.
        * match goal with Hq : pend ?r1 w |- _ =>
            apply pend_same in Hq; subst; assumption end.
    - intros H. destruct (pval w) as [v | ] eqn:Hv.
      + exists (pcons m v (pret v)). split.
        * apply rid_pcons.
        * eapply runs_cons; [eassumption | constructor | ].
          apply pval_graft. assumption.
      + exists (pmove m). split.
        * apply rid_pmove.
        * eapply runs_pend; [eassumption | ]. apply pval_pend. assumption.
  Qed.

  (** ** Downward closure is necessary

    [runs_scompose_bwd] is the only place in the whole module that
    uses a closure property of the generator family, and that use is
    not an artefact of the proof.  Take signatures with one operation
    each, and the implementations

      [gm : sg unit]  implemented in [sf] by [pcons fb tt (pret tt)],
      [fb : sf unit]  implemented in [se] by [pmove ea],

    both read up-closed, as demonic bundles are.  The
    [sf]-implementation of [gm] always returns; the
    [se]-implementation of [fb] never does.  So the composite
    implementation of [gm] admits the pending play [pmove ea], and an
    outer caller which issues [gm] and never gets an answer observes
    [pmove ea].  Split at [sf], though, and the first step asks for a
    *pending* play of [gm]'s [sf]-implementation: there is none,
    because an up-closed family containing [pcons fb tt (pret tt)]
    need not contain the prefix [pmove fb]. *)

  Inductive sg : esig := gm : sg unit.
  Inductive sf : esig := fb : sf unit.
  Inductive se : esig := ea : se unit.

  Definition Pg : rspec sf sg :=
    fun ar m =>
      match m in sg z return play sf z -> Prop with
        | gm => fun r => pref (pcons fb tt (pret tt)) r
      end.

  Definition Pf : rspec se sf :=
    fun ar m =>
      match m in sf z return play se z -> Prop with
        | fb => fun r => pref (pmove ea) r
      end.

  Lemma Pg_ucl ar (m : sg ar) : ucl (C := play_poset sf ar) (Pg ar m).
  Proof.
    destruct m. intros x y Hxy Hx. cbn in *. eapply pref_trans; eassumption.
  Qed.

  Lemma Pf_ucl ar (m : sf ar) : ucl (C := play_poset se ar) (Pf ar m).
  Proof.
    destruct m. intros x y Hxy Hx. cbn in *. eapply pref_trans; eassumption.
  Qed.

  (** A pending play never returns a value, and the single play that
    implements [gm] does; so no interaction of an unanswered [gm]
    with [Pg] exists at all. *)

  Lemma pend_pval {E : esig} {X A} (r : play E X) (u : play E A) :
    pend r u -> pval r = None.
  Proof.
    induction 1; cbn; auto.
  Qed.

  Lemma pref_cons_shape {E : esig} {X V} (m : E X) (n : X) (s t : play E V) :
    pref (pcons m n s) t -> exists t', t = pcons m n t' /\ pref s t'.
  Proof.
    inversion 1; depsubst; eauto.
  Qed.

  Lemma pref_pret_l {E : esig} {A} (v : A) (t : play E A) :
    pref (pret v) t -> t = pret v.
  Proof.
    inversion 1; reflexivity.
  Qed.

  Lemma Pg_shape (r : play sf unit) :
    Pg unit gm r -> r = pcons fb tt (pret tt).
  Proof.
    cbn. intros H.
    apply pref_cons_shape in H as (t & Ht & Hs).
    apply pref_pret_l in Hs. congruence.
  Qed.

  Lemma Pg_nonpend {X} (m : sg X) (r : play sf X) (u : play sf unit) :
    Pg X m r -> pend r u -> False.
  Proof.
    destruct m. intros Hr Hp.
    apply Pg_shape in Hr. subst r.
    apply pend_pval in Hp. cbn in Hp. discriminate.
  Qed.

  Theorem scompose_bwd_needs_dcl :
    runs (scompose Pg Pf) (pmove gm : play sg unit) (pmove ea) /\
    ~ (exists u : play sf unit,
         runs Pg (pmove gm : play sg unit) u /\ runs Pf u (pmove ea)).
  Proof.
    split.
    - eapply runs_pend; [ | constructor ].
      exists (pcons fb tt (pret tt)). split.
      + cbn. apply pref_refl.
      + eapply runs_cons_pend; [ | constructor ]. cbn. apply pref_refl.
    - intros (u & Hu & _). inversion Hu; depsubst.
      eapply Pg_nonpend; eassumption.
  Qed.

  (** So the obstruction to lifting [IRun] to dual nondeterminism is
    not the flattening law: [inf_sup] above is available, and
    [runs_scompose_fwd] needs no closure at all.  It is that the
    interaction-sequence *splitting* fails for up-closed families.

    Semantically the missing observation is a [bot].  When the demon
    picks an implementation play that returns and the caller recorded
    no answer, [ISpec.papply] yields [bot] -- that is the
    [bind (fun _ => bot)] in its [pmove] case.  In the angelic model
    [bot] is the empty downset, so there is nothing to record and
    down-closure of the generators is exactly what makes the two
    readings agree.  Demonically [bot] is not nothing, so recovering
    the splitting needs a generator poset with a bottom element: the
    global [bot] of thesis section 5.3.3.  That is the same
    obstruction as [ISpec.bind_bind], which is why assuming
    [codistributive] does not help here either -- the equation to be
    proved is missing a term, not a distributivity step. *)

  (** ** Summary: layers compose, constructively

    Collecting the above, [IRun] is a category:

      objects          effect signatures [E]
      morphisms        [rsubst E F = forall ar, F ar -> s E ar]
      identity         [rid]
      composition      [rcompose]
      action           [rapply], a complete join homomorphism

    with [rcompose_assoc], [rcompose_rid_l] and [rcompose_rid_r] all
    proved, and [Print Assumptions] on each reporting only functional
    and propositional extensionality.  In particular the unit law
    [rcompose_rid_l] is the analogue of [ISpec.apply_int_r], which the
    FCD model leaves admitted and which we showed there to run into
    codistributivity, i.e. excluded middle.

    Three things made the difference, and all three are properties of
    [Downset.F] that [FCD.F] does not have.

    - [rapply] is a *single* extension ([Downset.dext]), a plain [sup]
      over the elements of its argument.  Two such extensions commute
      outright ([Downset.dext2_comm]); for [FCD.ext] an [inf] sits
      between the two [sup]s and swapping them is codistributivity.
      The nesting [ISpec.papply] had is absorbed into the inductive
      definition of [runs], so associativity never has to exchange an
      [ext] with a [bind] -- the exchange law discussed at
      [ISpec.papplies_bind], for which neither inclusion is free.

    - [runs] is downward closed in its observation ([runs_down]),
      because each [f _ m] is a downset.  Hence [prun_has] and
      [rapply_has] describe [rapply] *exactly* by [runs], with no
      prefix slack, and the associativity statement becomes an
      equivalence between two inductive relations ([runs_rcompose])
      rather than a lattice identity.

    - The one disjunction the argument needs -- did this inner play
      return a value, or does it end in an unanswered move? -- is
      decided by structural recursion on the play ([pval]).  In the
      FCD model the corresponding step is a case analysis on an
      element of the lattice, where no such recursion is available
      and excluded middle is what is actually required.

    What is given up is demonic choice: [s E A] has all the [inf]s a
    complete lattice has, but [rapply] preserves only [sup]s, so an
    [inf] of specifications is not in general refined by the [inf] of
    their images.

    And the [runs] development says what stands in the way of getting
    it back.  Because [runs] is indexed by a family of predicates
    rather than by a substitution, the two halves of associativity
    can be inspected separately:

    - [runs_scompose_fwd] needs *no* hypothesis on the families.  So
      the easy inclusion survives any lift, demonic or not.

    - [runs_scompose_bwd] needs each family to be *downward* closed,
      and [scompose_bwd_needs_dcl] exhibits up-closed families for
      which it fails.  Demonic bundles -- the inner families of an
      element of [FCD.F] -- are up-closed, so the splitting is simply
      false for them.

    So the flattening law is not the obstacle: [inf_sup] is available
    constructively and we never needed it.  The obstacle is that a
    demonic bundle can omit the prefixes of the plays it contains,
    and the interaction that the composite admits is then not
    witnessed at the intermediate layer.  What is missing there is
    the [bot] that [ISpec.papply] produces at a [pmove] -- in the
    angelic model [bot] is the empty downset, so nothing is lost, and
    down-closure is precisely what makes that agree.  A dual lift
    therefore needs a generator poset with a bottom element, which is
    the global [bot] of thesis section 5.3.3 and the same obstruction
    as [ISpec.bind_bind].  Assuming [codistributive] does not supply
    it: the equation is missing a term, not a distributivity step. *)

End IRun.
(** * Opacity for clients

  The classical development kept the lattice behind sealed module
  interfaces, so [cbn] in a client file never tore the
  representation open.  This file is transparent throughout, which
  its own proofs rely on, so we restore the old behaviour here --
  after everything above has been proved -- for the benefit of
  anything built on top.  [pbind] and [papply] stay reducible: they
  are the recursions client proofs do induct on. *)

Global Opaque bot top join meet.

Arguments lsup : simpl never.
Arguments linf : simpl never.
Arguments fsup : simpl never.
Arguments finf : simpl never.
Arguments Downset.has : simpl never.
Arguments Downset.dsup : simpl never.
Arguments Downset.dinf : simpl never.
Arguments Downset.emb : simpl never.
Arguments Upset.uhas : simpl never.
Arguments Upset.up : simpl never.
Arguments FCD.emb : simpl never.
Arguments FCD.ext : simpl never.
Arguments FCD.gen : simpl never.
Arguments ISpec.emb : simpl never.
Arguments ISpec.ext : simpl never.
Arguments ISpec.map : simpl never.
Arguments ISpec.pcext : simpl never.
Arguments ISpec.ret : simpl never.
Arguments ISpec.bind : simpl never.
Arguments ISpec.int : simpl never.
Arguments ISpec.apply : simpl never.
Arguments ISpec.compose : simpl never.
Arguments ref : simpl never.
Arguments Downset.dref : simpl never.
Arguments Downset.Fpos : simpl never.
Arguments Downset.F : simpl never.
Arguments Upset.uref : simpl never.
Arguments Upset.Fpos : simpl never.
Arguments FCD.F : simpl never.
Arguments PProd.Ppos : simpl never.
Arguments PProd.Pccd : simpl never.
Arguments ISpec.t : simpl never.
Arguments ISpec.play_poset : simpl never.

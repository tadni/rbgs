(** * Interaction specifications as free bicompletions of interaction trees

  This is a constructive alternative to the [FCD]-based model of
  [models/IntSpec.v].  The only axioms used are functional
  extensionality (for the equational monad laws) and nothing else;
  in particular no excluded middle and no distributivity law.

  The idea is the one behind Whitman's solution of the word problem
  for free lattices, Joyal's free bicompletion of a category, and
  Blass/Abramsky-Jagadeesan games: instead of building a complete
  lattice and then asking which equations it satisfies, we take the
  syntax of specifications -- interaction trees with angelic ([Sup])
  and demonic ([Inf]) choice nodes -- and define refinement as a
  game played on the two trees.  Refinement [x [= y] holds when:

    - every angelic choice of [x] can be matched (Sup on the left is a
      universal quantifier),
    - some demonic choice of [x] can be matched (Inf on the left is a
      witness),
    - some angelic choice of [y] can be matched (Sup on the right is a
      witness),
    - every demonic choice of [y] can be matched (Inf on the right is
      universal),
    - [Vis m k [= Vis m k'] when [k n [= k' n] for every answer [n].

  A refinement proof therefore consists of the witnesses one would
  need in order to actually calculate with the specification.  This
  makes the model branching-time: the point at which a choice is made
  is observable, and [Inf j, Vis m (k j)] is not equivalent to
  [Vis m (fun n => Inf j, k j n)].  The monad structure is
  substitution, so all monad laws and all laws of [apply] hold as
  equalities, with no side conditions. *)

From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Morphisms RelationClasses Setoid.
From Stdlib Require Import PropExtensionality.
Require Import structures.Effects.


(** * Specification trees *)

Module ISpec.

  Inductive t (E : esig) (A : Type) : Type :=
    | Ret (a : A)
    | Vis {ar} (m : E ar) (k : ar -> t E A)
    | Sup {I : Type} (k : I -> t E A)
    | Inf {I : Type} (k : I -> t E A).

  Arguments Ret {E A} a.
  Arguments Vis {E A ar} m k.
  Arguments Sup {E A I} k.
  Arguments Inf {E A I} k.

  Definition ret {E A} (a : A) : t E A := Ret a.

  Definition int {E ar} (m : E ar) : t E ar := Vis m Ret.

  Fixpoint bind {E A B} (f : A -> t E B) (x : t E A) : t E B :=
    match x with
      | Ret a => f a
      | Vis m k => Vis m (fun n => bind f (k n))
      | Sup k => Sup (fun i => bind f (k i))
      | Inf k => Inf (fun i => bind f (k i))
    end.

  (** ** Lattice vocabulary *)

  Definition bot {E A} : t E A := Sup (fun x : False => match x with end).
  Definition top {E A} : t E A := Inf (fun x : False => match x with end).
  Definition join {E A} (x y : t E A) : t E A := Sup (fun b : bool => if b then x else y).
  Definition meet {E A} (x y : t E A) : t E A := Inf (fun b : bool => if b then x else y).

  Definition fsup {E A I} (P : I -> Prop) (f : I -> t E A) : t E A :=
    Sup (I := sig P) (fun z => f (proj1_sig z)).
  Definition finf {E A I} (P : I -> Prop) (f : I -> t E A) : t E A :=
    Inf (I := sig P) (fun z => f (proj1_sig z)).

  (** ** Duality *)

  Fixpoint dual {E A} (x : t E A) : t E A :=
    match x with
      | Ret a => Ret a
      | Vis m k => Vis m (fun n => dual (k n))
      | Sup k => Inf (fun i => dual (k i))
      | Inf k => Sup (fun i => dual (k i))
    end.

End ISpec.

Import ISpec.

Notation "'sup' i .. j , M" := (Sup (fun i => .. (Sup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).
Notation "'inf' i .. j , M" := (Inf (fun i => .. (Inf (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

Notation "'sup' { x | P } , M" := (fsup (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'sup' { x : A | P } , M" := (fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).
Notation "'inf' { x | P } , M" := (finf (fun x => P) (fun x => M))
  (at level 65, x ident, right associativity).
Notation "'inf' { x : A | P } , M" := (finf (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x ident, right associativity).

Infix "||" := join (at level 50, left associativity).
Infix "&&" := meet (at level 40, left associativity).


(** * The refinement game *)

Module Ref.

  (** Equality of operations of possibly different arities.  Using an
    inductive family rather than an equation between dependent pairs
    avoids any need for UIP: [destruct] on an [opeq m m'] simply
    unifies the two operations. *)

  Inductive opeq {E : esig} {ar} (m : E ar) : forall ar', E ar' -> Prop :=
    | opeq_refl : opeq m ar m.

  Arguments opeq {E ar} m {ar'} m'.
  Arguments opeq_refl {E ar m}.

  Definition opeq_cast {E : esig} {ar ar'} {m : E ar} {m' : E ar'} (e : opeq m m') : ar -> ar' :=
    match e with opeq_refl => fun n => n end.

  (** Refinement, defined by recursion on both trees.  The invertible
    rules (Sup on the left, Inf on the right) are given priority; the
    only genuine case split is [Inf] against [Sup], which is Whitman's
    condition. *)

  Fixpoint ref {E A} (x : t E A) : t E A -> Prop :=
    match x with
      | Sup k => fun y => forall i, ref (k i) y
      | Inf k =>
        fix go (y : t E A) : Prop :=
          match y with
            | Inf k' => forall j, go (k' j)
            | Sup k' => (exists i, ref (k i) y) \/ (exists j, go (k' j))
            | _ => exists i, ref (k i) y
          end
      | Ret a =>
        fix go (y : t E A) : Prop :=
          match y with
            | Inf k' => forall j, go (k' j)
            | Sup k' => exists j, go (k' j)
            | Ret b => a = b
            | Vis _ _ => False
          end
      | Vis m k =>
        fix go (y : t E A) : Prop :=
          match y with
            | Inf k' => forall j, go (k' j)
            | Sup k' => exists j, go (k' j)
            | Ret _ => False
            | Vis m' k' => exists e : opeq m m', forall n, ref (k n) (k' (opeq_cast e n))
          end
    end.

  (** ** The four lattice rules *)

  Lemma sup_l {E A I} (k : I -> t E A) y :
    ref (Sup k) y <-> forall i, ref (k i) y.
  Proof.
    reflexivity.
  Qed.

  Lemma inf_r {E A I} x (k' : I -> t E A) :
    ref x (Inf k') <-> forall j, ref x (k' j).
  Proof.
    induction x as [a | ar m k IH | J k IH | J k IH]; cbn; try reflexivity.
    split.
    - intros H j i. apply IH. auto.
    - intros H i. apply IH. intros j. apply H.
  Qed.

  Lemma sup_r {E A I} x (k' : I -> t E A) j :
    ref x (k' j) -> ref x (Sup k').
  Proof.
    revert j. induction x; intros j Hj; cbn in *; eauto.
  Qed.

  Lemma inf_l {E A I} (k : I -> t E A) i y :
    ref (k i) y -> ref (Inf k) y.
  Proof.
    revert i. induction y; intros i Hi; cbn; eauto.
    - rewrite inf_r in Hi. intros j. apply (H j i). auto.
  Qed.

  (** ** Reflexivity and transitivity *)

  Lemma refl {E A} (x : t E A) :
    ref x x.
  Proof.
    induction x; cbn; eauto.
    - exists opeq_refl. auto.
    - intros i. eapply sup_r; eauto.
    - intros i. eapply inf_l; eauto.
  Qed.

  (** The cut: the middle tree is an [Inf], the outer trees are
    arbitrary.  This is the same for every shape of [x]. *)

  Ltac cut_inf IHy Hxy Hyz :=
    let Hxy' := fresh "Hxy'" in
    pose proof (proj1 (inf_r _ _) Hxy) as Hxy';
    match goal with
      | [ |- ref ?x ?z ] =>
        revert Hyz; induction z as [c | ar'' m'' k'' IHz | K k'' IHz | K k'' IHz]; intros Hyz;
        [ cbn in Hyz; destruct Hyz as [j Hj]; exact (IHy j (Hxy' j) _ Hj)
        | cbn in Hyz; destruct Hyz as [j Hj]; exact (IHy j (Hxy' j) _ Hj)
        | cbn in Hyz; destruct Hyz as [[j Hj] | [j Hj]];
          [ exact (IHy j (Hxy' j) _ Hj)
          | eapply sup_r; exact (IHz j Hj) ]
        | apply inf_r; intros j; apply (IHz j (proj1 (inf_r _ _) Hyz j)) ]
    end.

  Lemma trans {E A} (x y z : t E A) :
    ref x y -> ref y z -> ref x z.
  Proof.
    revert y z.
    induction x as [a | ar m k IHx | I k IHx | I k IHx]; intros y z Hxy Hyz.
    - (* Ret *)
      revert Hxy z Hyz.
      induction y as [b | ar' m' k' IHy | J k' IHy | J k' IHy]; intros Hxy z Hyz.
      + cbn in Hxy. subst. assumption.
      + cbn in Hxy. contradiction.
      + cbn in Hxy. destruct Hxy as [j Hj]. cbn in Hyz. exact (IHy j Hj z (Hyz j)).
      + cut_inf IHy Hxy Hyz.
    - (* Vis *)
      revert Hxy z Hyz.
      induction y as [b | ar' m' k' IHy | J k' IHy | J k' IHy]; intros Hxy z Hyz.
      + cbn in Hxy. contradiction.
      + pose proof Hxy as Hxy0. cbn in Hxy0. destruct Hxy0 as [e Hk']. destruct e.
        revert Hyz. induction z as [c | ar'' m'' k'' IHz | K k'' IHz | K k'' IHz]; intros Hyz.
        * cbn in Hyz. contradiction.
        * cbn in Hyz. destruct Hyz as [e Hk'']. destruct e. cbn. exists opeq_refl.
          intros n. exact (IHx n _ _ (Hk' n) (Hk'' n)).
        * cbn in Hyz. destruct Hyz as [j Hj]. eapply sup_r. exact (IHz j Hj).
        * apply inf_r. intros j. apply (IHz j (proj1 (inf_r _ _) Hyz j)).
      + cbn in Hxy. destruct Hxy as [j Hj]. cbn in Hyz. exact (IHy j Hj z (Hyz j)).
      + cut_inf IHy Hxy Hyz.
    - (* Sup *)
      cbn in Hxy |- *. intros i. exact (IHx i y z (Hxy i) Hyz).
    - (* Inf *)
      revert Hxy z Hyz.
      induction y as [b | ar' m' k' IHy | J k' IHy | J k' IHy]; intros Hxy z Hyz.
      + cbn in Hxy. destruct Hxy as [i Hi]. eapply inf_l. exact (IHx i _ _ Hi Hyz).
      + cbn in Hxy. destruct Hxy as [i Hi]. eapply inf_l. exact (IHx i _ _ Hi Hyz).
      + cbn in Hxy. destruct Hxy as [[i Hi] | [j Hj]].
        * eapply inf_l. exact (IHx i _ _ Hi Hyz).
        * cbn in Hyz. exact (IHy j Hj z (Hyz j)).
      + cut_inf IHy Hxy Hyz.
  Qed.

  Global Instance preorder E A : PreOrder (@ref E A).
  Proof.
    split.
    - exact refl.
    - exact trans.
  Qed.

End Ref.

Abbreviation ref := Ref.ref.
Infix "[=" := ref (at level 70).

Definition eqv {E A} (x y : t E A) : Prop := x [= y /\ y [= x.
Infix "[=]" := eqv (at level 70).

Global Instance eqv_equiv E A : Equivalence (@eqv E A).
Proof.
  split.
  - intros x. split; reflexivity.
  - intros x y [H1 H2]. split; assumption.
  - intros x y z [H1 H2] [H3 H4]. split; etransitivity; eauto.
Qed.

Global Instance eqv_ref_subrel E A : subrelation (@eqv E A) ref.
Proof.
  intros x y [H _]. exact H.
Qed.

Global Instance ref_eqv_proper E A :
  Proper (eqv ==> eqv ==> iff) (@ref E A).
Proof.
  intros x x' [Hx Hx'] y y' [Hy Hy']. split; intros H.
  - etransitivity; eauto. etransitivity; eauto.
  - etransitivity; eauto. etransitivity; eauto.
Qed.


(** * Lattice properties *)

Section LATTICE.
  Context {E : esig} {A : Type}.

  Lemma sup_ub {I} (k : I -> t E A) i : k i [= Sup k.
  Proof. eapply Ref.sup_r. reflexivity. Qed.

  Lemma sup_lub {I} (k : I -> t E A) y : (forall i, k i [= y) -> Sup k [= y.
  Proof. apply Ref.sup_l. Qed.

  Lemma sup_at {I} (i : I) x (k : I -> t E A) : x [= k i -> x [= Sup k.
  Proof. apply Ref.sup_r. Qed.

  Lemma inf_lb {I} (k : I -> t E A) i : Inf k [= k i.
  Proof. eapply Ref.inf_l. reflexivity. Qed.

  Lemma inf_glb {I} x (k : I -> t E A) : (forall i, x [= k i) -> x [= Inf k.
  Proof. apply Ref.inf_r. Qed.

  Lemma inf_at {I} (i : I) (k : I -> t E A) y : k i [= y -> Inf k [= y.
  Proof. apply Ref.inf_l. Qed.

  Lemma bot_lb (x : t E A) : bot [= x.
  Proof. apply sup_lub. intros []. Qed.

  Lemma top_ub (x : t E A) : x [= top.
  Proof. apply inf_glb. intros []. Qed.

  Lemma join_ub_l (x y : t E A) : x [= x || y.
  Proof. apply (sup_at true). reflexivity. Qed.

  Lemma join_ub_r (x y : t E A) : y [= x || y.
  Proof. apply (sup_at false). reflexivity. Qed.

  Lemma join_lub (x y z : t E A) : x [= z -> y [= z -> x || y [= z.
  Proof. intros. apply sup_lub. intros []; auto. Qed.

  Lemma meet_lb_l (x y : t E A) : x && y [= x.
  Proof. apply (inf_at true). reflexivity. Qed.

  Lemma meet_lb_r (x y : t E A) : x && y [= y.
  Proof. apply (inf_at false). reflexivity. Qed.

  Lemma meet_glb (x y z : t E A) : z [= x -> z [= y -> z [= x && y.
  Proof. intros. apply inf_glb. intros []; auto. Qed.

  Lemma sup_mono {I} (k k' : I -> t E A) :
    (forall i, k i [= k' i) -> Sup k [= Sup k'.
  Proof. intros H. apply sup_lub. intros i. apply (sup_at i). auto. Qed.

  Lemma inf_mono {I} (k k' : I -> t E A) :
    (forall i, k i [= k' i) -> Inf k [= Inf k'.
  Proof. intros H. apply inf_glb. intros i. apply (inf_at i). auto. Qed.

  Lemma vis_mono {ar} (m : E ar) (k k' : ar -> t E A) :
    (forall n, k n [= k' n) -> Vis m k [= Vis m k'.
  Proof. intros H. cbn. exists Ref.opeq_refl. auto. Qed.

  (** Answers that are only assumed (or asserted) to satisfy [P] are
    encoded in the continuation, the same way [assert] is encoded in
    [examples/CAL.v]. *)

  Lemma vis_assume {ar} (m : E ar) (P : ar -> Prop) (k : ar -> t E A) :
    Vis m k [= Vis m (fun n => inf _ : P n, k n).
  Proof. apply vis_mono. intros n. apply inf_glb. reflexivity. Qed.

  Lemma vis_assert {ar} (m : E ar) (P : ar -> Prop) (k : ar -> t E A) :
    Vis m (fun n => sup _ : P n, k n) [= Vis m k.
  Proof. apply vis_mono. intros n. apply sup_lub. reflexivity. Qed.

End LATTICE.

(** ** Duality *)

Lemma dual_dual {E A} (x : t E A) : dual (dual x) = x.
Proof.
  induction x; cbn; try reflexivity; f_equal; apply functional_extensionality; auto.
Qed.

Local Ltac fin H := first [ exact H | exact (H _) ].

Lemma ref_dual {E A} (x y : t E A) :
  dual x [= dual y <-> y [= x.
Proof.
  revert y. induction x as [a | ar m k IHx | I k IHx | I k IHx];
    intros y; induction y as [b | ar' m' k' IHy | J k' IHy | J k' IHy];
    cbn in *.
  - (* Ret Ret *) split; intros H; subst; reflexivity.
  - (* Ret Vis *) reflexivity.
  - (* Ret Sup *) split; intros H j; apply IHy; fin H.
  - (* Ret Inf *) split; intros [j H]; exists j; apply IHy; fin H.
  - (* Vis Ret *) reflexivity.
  - (* Vis Vis *)
    split; intros [e H]; destruct e; exists Ref.opeq_refl; intros n; cbn in *; apply (IHx n (k' n)); fin H.
  - (* Vis Sup *) split; intros H j; apply IHy; fin H.
  - (* Vis Inf *) split; intros [j H]; exists j; apply IHy; fin H.
  - (* Sup Ret *) split; intros [i H]; exists i; apply (IHx i (Ret b)); fin H.
  - (* Sup Vis *) split; intros [i H]; exists i; apply (IHx i (Vis m' k')); fin H.
  - (* Sup Sup *) split; intros H j; apply IHy; fin H.
  - (* Sup Inf *)
    split.
    + intros [[i H] | [j H]].
      * right. exists i. apply (IHx i (Inf k')). fin H.
      * left. exists j. apply IHy. fin H.
    + intros [[j H] | [i H]].
      * right. exists j. apply IHy. fin H.
      * left. exists i. apply (IHx i (Inf k')). fin H.
  - (* Inf Ret *) split; intros H i; apply (IHx i (Ret b)); fin H.
  - (* Inf Vis *) split; intros H i; apply (IHx i (Vis m' k')); fin H.
  - (* Inf Sup *)
    split.
    + intros H j. apply Ref.inf_r. intros i. apply (IHx i (k' j)).
      specialize (H i). rewrite Ref.inf_r in H. fin H.
    + intros H i. apply Ref.inf_r. intros j. apply (IHx i (k' j)).
      specialize (H j). rewrite Ref.inf_r in H. fin H.
  - (* Inf Inf *) split; intros H i; apply (IHx i (Inf k')); fin H.
Qed.

Lemma dual_bind {E A B} (f : A -> t E B) (x : t E A) :
  dual (bind f x) = bind (fun a => dual (f a)) (dual x).
Proof.
  induction x; cbn; try reflexivity; f_equal; apply functional_extensionality; auto.
Qed.


(** * Monad laws *)

Section MONAD.
  Context {E : esig}.

  Lemma bind_ret_r {A B} (a : A) (f : A -> t E B) :
    bind f (ret a) = f a.
  Proof. reflexivity. Qed.

  Lemma bind_ret_l {A} (x : t E A) :
    bind ret x = x.
  Proof.
    induction x; cbn; try reflexivity; f_equal; apply functional_extensionality; auto.
  Qed.

  Lemma bind_bind {A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    bind g (bind f x) = bind (fun a => bind g (f a)) x.
  Proof.
    induction x; cbn; try reflexivity; f_equal; apply functional_extensionality; auto.
  Qed.

  Lemma bind_int {A X} (f : X -> t E A) (m : E X) :
    bind f (int m) = Vis m f.
  Proof. reflexivity. Qed.

  Lemma bind_sup {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (Sup k) = Sup (fun i => bind f (k i)).
  Proof. reflexivity. Qed.

  Lemma bind_inf {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (Inf k) = Inf (fun i => bind f (k i)).
  Proof. reflexivity. Qed.

  (** [bind] is monotonic in both arguments. *)

  Lemma bind_mono {A B} (f f' : A -> t E B) (x x' : t E A) :
    (forall a, f a [= f' a) -> x [= x' -> bind f x [= bind f' x'.
  Proof.
    intros Hf. revert x'.
    induction x as [a | ar m k IHx | I k IHx | I k IHx];
      intros x'; induction x' as [b | ar' m' k' IHx' | J k' IHx' | J k' IHx'];
      intros H; cbn in H; cbn [bind]; try contradiction.
    - (* Ret Ret *) subst. apply Hf.
    - (* Ret Sup *) destruct H as [j Hj]. eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Ret Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
    - (* Vis Vis *) destruct H as [e Hk']. destruct e. exists Ref.opeq_refl.
      intros n. apply (IHx n (k' n) (Hk' n)).
    - (* Vis Sup *) destruct H as [j Hj]. eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Vis Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
    - (* Sup Ret *) intros i. apply (IHx i _ (H i)).
    - (* Sup Vis *) intros i. apply (IHx i _ (H i)).
    - (* Sup Sup *) intros i. apply (IHx i (Sup k') (H i)).
    - (* Sup Inf *) intros i. apply (IHx i (Inf k') (H i)).
    - (* Inf Ret *) destruct H as [i Hi]. eapply Ref.inf_l. apply (IHx i _ Hi).
    - (* Inf Vis *) destruct H as [i Hi]. eapply Ref.inf_l. apply (IHx i _ Hi).
    - (* Inf Sup *) destruct H as [[i Hi] | [j Hj]].
      + eapply Ref.inf_l. apply (IHx i (Sup k') Hi).
      + eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Inf Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
  Qed.

  Global Instance bind_ref_proper A B :
    Proper (pointwise_relation A ref ==> ref ==> ref) (@bind E A B).
  Proof.
    intros f f' Hf x x' Hx. apply bind_mono; auto.
  Qed.

  Global Instance bind_eqv_proper A B :
    Proper (pointwise_relation A eqv ==> eqv ==> eqv) (@bind E A B).
  Proof.
    intros f f' Hf x x' [Hx Hx']. split; apply bind_mono; auto.
    - intros a. apply Hf.
    - intros a. apply Hf.
  Qed.

End MONAD.


(** * Substitutions *)

Module Subst.

  Definition t (E F : esig) := forall ar, F ar -> ISpec.t E ar.

  Definition ref {E F} (f g : t E F) := forall ar m, f ar m [= g ar m.

  Global Instance ref_preorder E F : PreOrder (@ref E F).
  Proof.
    split.
    - intros f ar m. reflexivity.
    - intros f g h Hfg Hgh ar m. etransitivity; eauto.
  Qed.

  Definition id {E} : t E E := fun ar m => int m.

  Fixpoint apply {E F A} (f : t E F) (x : ISpec.t F A) : ISpec.t E A :=
    match x with
      | Ret a => Ret a
      | Vis m k => bind (fun n => apply f (k n)) (f _ m)
      | Sup k => Sup (fun i => apply f (k i))
      | Inf k => Inf (fun i => apply f (k i))
    end.

  Definition compose {E F G} (g : t F G) (f : t E F) : t E G :=
    fun ar m => apply f (g ar m).

End Subst.

Infix "~>" := Subst.t (at level 99).
Infix "[~=" := Subst.ref (at level 70).
Notation "x / f" := (Subst.apply f x).
Infix "@" := Subst.compose (at level 40, left associativity).

Section APPLY.
  Import Subst.

  Lemma apply_ret {E F A} (f : E ~> F) (a : A) :
    ret a / f = ret a.
  Proof. reflexivity. Qed.

  Lemma apply_int_r {E F ar} (m : F ar) (f : E ~> F) :
    int m / f = f ar m.
  Proof. cbn. apply bind_ret_l. Qed.

  Lemma apply_bind {E F A B} (f : E ~> F) (g : A -> ISpec.t F B) (x : ISpec.t F A) :
    bind g x / f = bind (fun a => g a / f) (x / f).
  Proof.
    induction x; cbn.
    - reflexivity.
    - rewrite bind_bind. f_equal. apply functional_extensionality. auto.
    - f_equal. apply functional_extensionality. auto.
    - f_equal. apply functional_extensionality. auto.
  Qed.

  Lemma apply_int_l {E A} (x : ISpec.t E A) :
    x / Subst.id = x.
  Proof.
    induction x; cbn; try reflexivity; f_equal; apply functional_extensionality; auto.
  Qed.

  Lemma apply_assoc {E F G A} (f : E ~> F) (g : F ~> G) (x : ISpec.t G A) :
    x / g / f = x / (g @ f).
  Proof.
    induction x; cbn.
    - reflexivity.
    - rewrite apply_bind. unfold compose. f_equal.
      apply functional_extensionality. auto.
    - f_equal. apply functional_extensionality. auto.
    - f_equal. apply functional_extensionality. auto.
  Qed.

  Lemma apply_sup {E F A I} (f : E ~> F) (k : I -> ISpec.t F A) :
    Sup k / f = Sup (fun i => k i / f).
  Proof. reflexivity. Qed.

  Lemma apply_inf {E F A I} (f : E ~> F) (k : I -> ISpec.t F A) :
    Inf k / f = Inf (fun i => k i / f).
  Proof. reflexivity. Qed.

  Lemma compose_id_l {E F} (f : E ~> F) : Subst.id @ f = f.
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    unfold compose, Subst.id. apply apply_int_r.
  Qed.

  Lemma compose_id_r {E F} (f : E ~> F) : f @ Subst.id = f.
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    unfold compose. apply apply_int_l.
  Qed.

  Lemma compose_assoc {E F G H} (h : G ~> H) (g : F ~> G) (f : E ~> F) :
    (h @ g) @ f = h @ (g @ f).
  Proof.
    apply functional_extensionality_dep. intros ar.
    apply functional_extensionality. intros m.
    unfold compose. apply apply_assoc.
  Qed.

  (** [apply] is monotonic in both arguments. *)

  Lemma apply_mono {E F A} (f f' : E ~> F) (x x' : ISpec.t F A) :
    f [~= f' -> x [= x' -> x / f [= x' / f'.
  Proof.
    intros Hf. revert x'.
    induction x as [a | ar m k IHx | I k IHx | I k IHx];
      intros x'; induction x' as [b | ar' m' k' IHx' | J k' IHx' | J k' IHx'];
      intros H; cbn in H; cbn [Subst.apply]; try contradiction.
    - (* Ret Ret *) subst. reflexivity.
    - (* Ret Sup *) destruct H as [j Hj]. eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Ret Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
    - (* Vis Vis *) destruct H as [e Hk']. destruct e.
      apply bind_mono; [ intros n; apply (IHx n (k' n) (Hk' n)) | apply Hf ].
    - (* Vis Sup *) destruct H as [j Hj]. eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Vis Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
    - (* Sup Ret *) intros i. apply (IHx i _ (H i)).
    - (* Sup Vis *) intros i. apply (IHx i _ (H i)).
    - (* Sup Sup *) intros i. apply (IHx i (Sup k') (H i)).
    - (* Sup Inf *) intros i. apply (IHx i (Inf k') (H i)).
    - (* Inf Ret *) destruct H as [i Hi]. eapply Ref.inf_l. apply (IHx i _ Hi).
    - (* Inf Vis *) destruct H as [i Hi]. eapply Ref.inf_l. apply (IHx i _ Hi).
    - (* Inf Sup *) destruct H as [[i Hi] | [j Hj]].
      + eapply Ref.inf_l. apply (IHx i (Sup k') Hi).
      + eapply Ref.sup_r. apply (IHx' j Hj).
    - (* Inf Inf *) apply Ref.inf_r. intros j. apply (IHx' j (H j)).
  Qed.

  Global Instance apply_ref_proper E F A :
    Proper (Subst.ref ==> Ref.ref ==> Ref.ref) (@apply E F A).
  Proof.
    intros f f' Hf x x' Hx. apply apply_mono; auto.
  Qed.

  Global Instance compose_ref_proper E F G :
    Proper (Subst.ref ==> Subst.ref ==> Subst.ref) (@compose E F G).
  Proof.
    intros g g' Hg f f' Hf ar m. apply apply_mono; auto.
  Qed.

End APPLY.




(** * Questions of either polarity *)

(** The game fixes who chooses the answer at a bare [Vis] node: the
  environment.  Who chooses the question is not fixed by the model
  but by the choice node above the [Vis]. *)

Section QUESTIONS.
  Context {E : esig} {A : Type}.

  (** An angelic question: the specification picks which question to
    ask, so a single question refines it. *)

  Lemma angelic_question {I} (ar : I -> Type) (m : forall i, E (ar i))
        (k : forall i, ar i -> t E A) (i : I) :
    Vis (m i) (k i) [= sup j, Vis (m j) (k j).
  Proof. apply (sup_at i). reflexivity. Qed.

  (** A demonic question: the environment picks which question gets
    asked, so the specification must be prepared for all of them. *)

  Lemma demonic_question {I} (ar : I -> Type) (m : forall i, E (ar i))
        (k : forall i, ar i -> t E A) (i : I) :
    inf j, Vis (m j) (k j) [= Vis (m i) (k i).
  Proof. apply (inf_at i). reflexivity. Qed.

  (** When a demonic question is substituted into a lower layer, it
    becomes a demonic choice between the implementations of the
    questions, as expected. *)

  Lemma apply_demonic_question {F I} (f : F ~> E) (ar : I -> Type)
        (m : forall i, E (ar i)) (k : forall i, ar i -> t E A) :
    (inf j, Vis (m j) (k j)) / f = inf j, bind (fun n => k j n / f) (f _ (m j)).
  Proof. reflexivity. Qed.

  (** Choices are not postponed past interaction: the game is
    branching-time.  The direction that holds is the one where the
    choice is made later. *)

  Lemma vis_inf_late {ar} (m : E ar) {J} (k : J -> ar -> t E A) :
    Vis m (fun n => inf j, k j n) [= inf j, Vis m (k j).
  Proof.
    apply inf_glb. intros j. apply vis_mono. intros n. apply (inf_at j). reflexivity.
  Qed.

  Lemma vis_sup_early {ar} (m : E ar) {J} (k : J -> ar -> t E A) :
    sup j, Vis m (k j) [= Vis m (fun n => sup j, k j n).
  Proof.
    apply sup_lub. intros j. apply vis_mono. intros n. apply (sup_at j). reflexivity.
  Qed.

End QUESTIONS.

(** * Where locatedness lives in this model *)

(** The classical model needs codistributivity, [inf i, (a || x i) [=
  a || inf i, x i], as an axiom of the lattice, and constructively that
  is excluded middle.  In the game model the inequality is not an
  axiom but a lemma with a side condition, and the side condition is
  exactly the locatedness of the family relative to [a]: either some
  member is already below [a], or [a] is below every member.  This is
  the information one needs in order to calculate the witness, and
  it is supplied per instance by whoever knows it. *)

Section LOCATED.
  Context {E : esig} {A : Type}.

  Lemma join_inf_le {I} (a : t E A) (x : I -> t E A) :
    a || (inf i, x i) [= inf i, (a || x i).
  Proof.
    apply inf_glb. intros i. apply join_lub.
    - apply join_ub_l.
    - etransitivity; [ apply (inf_lb x i) | apply join_ub_r ].
  Qed.

  Lemma codist_located {I} (a : t E A) (x : I -> t E A) :
    (exists i, x i [= a) \/ (forall i, a [= x i) ->
    inf i, (a || x i) [= a || (inf i, x i).
  Proof.
    intros [[i Hi] | Ha].
    - apply (sup_at true). apply (inf_at i). apply join_lub; [ reflexivity | exact Hi ].
    - apply (sup_at false). apply inf_glb. intros i. apply (inf_at i).
      apply join_lub; [ apply Ha | reflexivity ].
  Qed.

End LOCATED.

(** * Dedekind cuts: Leibniz equality for specifications *)

(** Trees are representatives, like Cauchy sequences: [eqv] is a
  setoid equality.  The Dedekind-style move is to replace a tree by
  the set of trees below it.  With functional and propositional
  extensionality that set has Leibniz equality, and two trees have
  the same cut exactly when they are [eqv].  Because the trees already
  form a complete lattice, nothing new appears: every cut is
  principal, and the cuts are exactly the Sup-closed downsets. *)

Module Cut.

  Definition down {E A} (x : t E A) : t E A -> Prop := fun y => y [= x.

  Record cut (E : esig) (A : Type) : Type := mk {
    has : t E A -> Prop;
    principal : exists x, forall y, has y <-> down x y;
  }.

  Arguments has {E A}.
  Arguments principal {E A}.

  Lemma cut_eq {E A} (C D : cut E A) :
    (forall y, has C y <-> has D y) -> C = D.
  Proof.
    intros H. destruct C as [C HC], D as [D HD]. cbn in H.
    assert (C = D) as <-.
    { apply functional_extensionality. intros y.
      apply propositional_extensionality. apply H. }
    f_equal. apply proof_irrelevance.
  Qed.

  Definition emb {E A} (x : t E A) : cut E A :=
    mk E A (down x) (ex_intro _ x (fun y => iff_refl _)).

  Lemma emb_eq {E A} (x y : t E A) :
    emb x = emb y <-> x [=] y.
  Proof.
    split.
    - intros H.
      assert (Hx : has (emb x) x) by (cbn; unfold down; reflexivity).
      assert (Hy : has (emb y) y) by (cbn; unfold down; reflexivity).
      rewrite H in Hx. rewrite <- H in Hy. split; assumption.
    - intros [Hxy Hyx]. apply cut_eq. intros z. cbn. unfold down. split; intros H.
      + etransitivity; eauto.
      + etransitivity; eauto.
  Qed.

  (** What does not work, and why.  One would like to recover a tree
    from a cut as the sup of its members,
    [Sup (fun z : { y | has D y } => proj1_sig z)], and then lift
    [bind], [apply] and friends to cuts through this representative.
    But a family indexed by trees lives one universe above the index
    universe of [Sup], so this sup is not a tree of the same type.
    This is the usual size issue of Dedekind cuts: cuts of a type live
    one level up, and here it does not stabilize because trees have
    sups over arbitrary small index types.  Lifting the operations
    without a representative would need, for [bind f D], a choice of
    representatives for all the [f a] simultaneously, which is the
    axiom of choice.  So cuts give Leibniz equality for stating and
    transporting facts, while the computations stay on trees. *)

End Cut.

(** Clients of the model should reason with the lattice lemmas above
  rather than by unfolding the game, so we prevent [simpl] and [cbn]
  from unfolding [ref] from here on. *)

Global Arguments Ref.ref : simpl never.


Global Instance apply_eqv_proper E F A :
  Proper (eq ==> eqv ==> eqv) (@Subst.apply E F A).
Proof.
  intros f f' [] x x' [Hx Hx']. split; apply apply_mono; auto; reflexivity.
Qed.

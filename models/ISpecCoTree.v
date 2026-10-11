(** * Coinductive interaction specifications with dual nondeterminism

  This is the coinductive version of [models/ISpecTree.v].  Trees may
  be infinite, so that specifications of reactive systems such as
  servers can be written with [iter], as with interaction trees.

  The shape of the trees is that of choice trees: every child is
  coinductive, including the children of the choice nodes [Sup] and
  [Inf].  Refinement is the game of the inductive model, taken as a
  greatest fixed point, with one design decision that makes it work:

    - the rules that act on the *left* tree are coinductive steps
      ([Sup] on the left is universal, [Inf] on the left is a witness,
      and both continue through the fixed point),
    - the rules that act on the *right* tree are inductive ([Sup] on
      the right is a witness, [Inf] on the right is universal, and
      both must reach a leaf or a left rule in finitely many steps).

  Consequently any silent divergence is the bottom element, in the
  same way that a diverging tree is below everything for [sutt] in the
  interaction tree library.  A silent step [Tau] is just [Sup] over
  [unit].  With both universal rules coinductive the alternating
  silent chain would be both bottom and top and transitivity would
  fail; with the asymmetric assignment the cut goes through by a
  lexicographic induction.

  The fixed point is taken Knaster-Tarski style over [Prop]-valued
  relations, so no coinduction library is needed, and the only axioms
  are functional and propositional extensionality. *)

From Stdlib Require Import FunctionalExtensionality PropExtensionality EqdepFacts.
From Stdlib Require Import Morphisms RelationClasses Setoid.
Require Import structures.Effects.

(** Injectivity of dependent pairs follows from proof irrelevance,
  which follows from propositional extensionality. *)

Module PI_eq_rect_eq.
  Lemma eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h.
  Proof. intros. rewrite (proof_irrelevance _ h eq_refl). reflexivity. Qed.
End PI_eq_rect_eq.
Module PI_Eqdep := EqdepFacts.EqdepTheory PI_eq_rect_eq.

Ltac inj_pair :=
  repeat match goal with
    | H : existT _ _ _ = existT _ _ _ |- _ => apply PI_Eqdep.inj_pair2 in H; subst
  end.


(** * Trees *)

Module ISpec.

  Inductive tF (E : esig) (A : Type) (X : Type) : Type :=
    | RetF (a : A)
    | VisF {ar} (m : E ar) (k : ar -> X)
    | SupF {I : Type} (k : I -> X)
    | InfF {I : Type} (k : I -> X).

  Arguments RetF {E A X} a.
  Arguments VisF {E A X ar} m k.
  Arguments SupF {E A X I} k.
  Arguments InfF {E A X I} k.

  CoInductive t (E : esig) (A : Type) : Type := go { observe : tF E A (t E A) }.

  Arguments go {E A} _.
  Arguments observe {E A} _.

  Definition ret {E A} (a : A) : t E A := go (RetF a).
  Definition Vis {E A ar} (m : E ar) (k : ar -> t E A) : t E A := go (VisF m k).
  Definition Sup {E A I} (k : I -> t E A) : t E A := go (SupF k).
  Definition Inf {E A I} (k : I -> t E A) : t E A := go (InfF k).
  Definition Tau {E A} (x : t E A) : t E A := Sup (fun _ : unit => x).
  Definition int {E ar} (m : E ar) : t E ar := Vis m ret.

  Definition bind {E A B} (f : A -> t E B) : t E A -> t E B :=
    cofix bind_ (x : t E A) : t E B :=
      match observe x with
      | RetF a => f a
      | VisF m k => go (VisF m (fun n => bind_ (k n)))
      | SupF k => go (SupF (fun i => bind_ (k i)))
      | InfF k => go (InfF (fun i => bind_ (k i)))
      end.

  Definition iter {E A I} (step : I -> t E (I + A)) : I -> t E A :=
    cofix iter_ (i : I) : t E A :=
      bind (fun r => match r with
                     | inl i' => Tau (iter_ i')
                     | inr a => ret a
                     end) (step i).

  Definition bot {E A} : t E A := Sup (fun x : False => match x with end).
  Definition top {E A} : t E A := Inf (fun x : False => match x with end).
  Definition join {E A} (x y : t E A) : t E A := Sup (fun b : bool => if b then x else y).
  Definition meet {E A} (x y : t E A) : t E A := Inf (fun b : bool => if b then x else y).
  Definition fsup {E A I} (P : I -> Prop) (f : I -> t E A) : t E A :=
    Sup (I := sig P) (fun z => f (proj1_sig z)).
  Definition finf {E A I} (P : I -> Prop) (f : I -> t E A) : t E A :=
    Inf (I := sig P) (fun z => f (proj1_sig z)).

  CoFixpoint dual {E A} (x : t E A) : t E A :=
    go match observe x with
       | RetF a => RetF a
       | VisF m k => VisF m (fun n => dual (k n))
       | SupF k => InfF (fun i => dual (k i))
       | InfF k => SupF (fun i => dual (k i))
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

  Section FUNCTOR.
    Context {E : esig} {A : Type}.

    (** One round of the game.  [R] is the relation used for the
      coinductive continuations. *)

    Inductive refF (R : t E A -> t E A -> Prop) : tF E A (t E A) -> tF E A (t E A) -> Prop :=
      | refF_ret a :
          refF R (RetF a) (RetF a)
      | refF_vis {ar} (m : E ar) k k' :
          (forall n, R (k n) (k' n)) ->
          refF R (VisF m k) (VisF m k')
      | refF_sup_l {I} (k : I -> t E A) oy :
          (forall i, R (k i) (go oy)) ->
          refF R (SupF k) oy
      | refF_inf_l {I} (k : I -> t E A) (i : I) oy :
          R (k i) (go oy) ->
          refF R (InfF k) oy
      | refF_sup_r ox {J} (k' : J -> t E A) (j : J) :
          refF R ox (observe (k' j)) ->
          refF R ox (SupF k')
      | refF_inf_r ox {J} (k' : J -> t E A) :
          (forall j, refF R ox (observe (k' j))) ->
          refF R ox (InfF k').

    Lemma refF_mono (R R' : t E A -> t E A -> Prop) :
      (forall x y, R x y -> R' x y) ->
      forall ox oy, refF R ox oy -> refF R' ox oy.
    Proof.
      intros HR ox oy H. induction H.
      - constructor.
      - constructor. auto.
      - constructor. auto.
      - econstructor. eauto.
      - econstructor. eauto.
      - constructor. auto.
    Qed.

    (** The greatest fixed point, Knaster-Tarski style. *)

    Definition closed (R : t E A -> t E A -> Prop) :=
      forall x y, R x y -> refF R (observe x) (observe y).

    Definition ref (x y : t E A) : Prop :=
      exists R, closed R /\ R x y.

    Lemma ref_coind (R : t E A -> t E A -> Prop) :
      closed R -> forall x y, R x y -> ref x y.
    Proof.
      intros HR x y H. exists R. auto.
    Qed.

    Lemma ref_unfold x y :
      ref x y -> refF ref (observe x) (observe y).
    Proof.
      intros [R [HR H]]. apply HR in H.
      eapply refF_mono; [ | exact H ].
      intros x' y' H'. exists R. auto.
    Qed.

    Lemma ref_fold x y :
      refF ref (observe x) (observe y) -> ref x y.
    Proof.
      intros H. apply (ref_coind (fun x y => refF ref (observe x) (observe y))); auto.
      intros x' y' H'. eapply refF_mono; [ | exact H' ].
      intros x'' y''. apply ref_unfold.
    Qed.

    Lemma ref_go_l ox y :
      ref (go ox) y <-> refF ref ox (observe y).
    Proof.
      split.
      - intros H. apply ref_unfold in H. exact H.
      - intros H. apply ref_fold. exact H.
    Qed.

    Lemma ref_go ox oy :
      ref (go ox) (go oy) <-> refF ref ox oy.
    Proof.
      split.
      - intros H. apply ref_unfold in H. exact H.
      - intros H. apply ref_fold. exact H.
    Qed.

    (** ** Reflexivity *)

    (** The post-fixed point for reflexivity needs the pairs [(k i, Sup k)]
      and [(x, go (observe x))] besides the diagonal. *)

    Definition refl_rel (x y : t E A) : Prop :=
      x = y \/
      y = go (observe x) \/
      (exists I (k : I -> t E A) i, x = k i /\ y = Sup k).

    Lemma refF_refl (R : t E A -> t E A -> Prop) :
      (forall x, R x x) ->
      (forall x, R x (go (observe x))) ->
      (forall I (k : I -> t E A) i, R (k i) (Sup k)) ->
      forall o, refF R o o.
    Proof.
      intros H0 H1 H2 o. destruct o.
      - constructor.
      - constructor. intros n. apply H0.
      - constructor. intros i. apply H2.
      - constructor. intros j. econstructor. apply H1.
    Qed.

    Lemma refl_rel_closed : closed refl_rel.
    Proof.
      intros x y [H | [H | [I [k [i [Hx Hy]]]]]].
      - subst. apply refF_refl.
        + intros x'. left. reflexivity.
        + intros x'. right. left. reflexivity.
        + intros I k i. right. right. eauto.
      - subst. cbn. apply refF_refl.
        + intros x'. left. reflexivity.
        + intros x'. right. left. reflexivity.
        + intros I k i. right. right. eauto.
      - subst. cbn. econstructor. apply refF_refl.
        + intros x'. left. reflexivity.
        + intros x'. right. left. reflexivity.
        + intros I' k' i'. right. right. eauto.
    Qed.

    Lemma refl x : ref x x.
    Proof.
      apply (ref_coind refl_rel refl_rel_closed). left. reflexivity.
    Qed.

    (** ** Transitivity *)

    Definition trans_rel (x z : t E A) : Prop :=
      exists y, ref x y /\ ref y z.

    (** The cut, with an arbitrary relation on the left: refinement
      composes on the right with one game step of any relation. *)

    Lemma cut_r (X : t E A -> t E A -> Prop) ox oy :
      refF X ox oy ->
      forall oz, refF ref oy oz ->
      refF (fun u w => exists v, X u v /\ ref v w) ox oz.
    Proof.
      intros d1. induction d1; intros oz d2.
      - (* ret *)
        remember (RetF a) as o eqn:Ho. induction d2; try discriminate.
        + injection Ho as ->. constructor.
        + econstructor. eauto.
        + constructor. eauto.
      - (* vis *)
        remember (VisF m k') as o eqn:Ho. induction d2; try discriminate.
        + injection Ho. intros Hk Hm ->. inj_pair.
          constructor. intros n. exists (k' n). auto.
        + econstructor. eauto.
        + constructor. eauto.
      - (* sup_l *)
        constructor. intros i. exists (go oy). split; auto.
        apply ref_go. exact d2.
      - (* inf_l *)
        econstructor. exists (go oy). split; eauto.
        apply ref_go. exact d2.
      - (* sup_r *)
        remember (SupF k') as o eqn:Ho. induction d2; try discriminate.
        + injection Ho. intros Hk ->. inj_pair.
          apply IHd1. exact (ref_unfold _ _ (H j)).
        + econstructor. eauto.
        + constructor. eauto.
      - (* inf_r *)
        remember (InfF k') as o eqn:Ho. induction d2; try discriminate.
        + injection Ho. intros Hk ->. inj_pair.
          apply (H0 i). exact (ref_unfold _ _ H1).
        + econstructor. eauto.
        + constructor. eauto.
    Qed.

    Lemma trans_rel_closed : closed trans_rel.
    Proof.
      intros x z [y [Hxy Hyz]].
      apply ref_unfold in Hxy. apply ref_unfold in Hyz.
      eapply cut_r; eauto.
    Qed.

    Lemma trans x y z : ref x y -> ref y z -> ref x z.
    Proof.
      intros Hxy Hyz. apply (ref_coind trans_rel trans_rel_closed). exists y. auto.
    Qed.

    Global Instance preorder : PreOrder ref.
    Proof. split; [ exact refl | exact trans ]. Qed.

  End FUNCTOR.

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
Proof. intros x y [H _]. exact H. Qed.

Global Instance ref_eqv_proper E A : Proper (eqv ==> eqv ==> iff) (@ref E A).
Proof.
  intros x x' [Hx Hx'] y y' [Hy Hy']. split; intros H.
  - etransitivity; eauto. etransitivity; eauto.
  - etransitivity; eauto. etransitivity; eauto.
Qed.


(** * Lattice properties *)

Section LATTICE.
  Context {E : esig} {A : Type}.

  Lemma refF_refl_ref (o : tF E A (t E A)) : Ref.refF ref o o.
  Proof. exact (Ref.ref_unfold (go o) (go o) (Ref.refl (go o))). Qed.

  (** Wrapping and unwrapping one layer is invisible. *)

  Lemma go_observe_r (x : t E A) : x [= go (observe x).
  Proof. apply Ref.ref_fold. apply refF_refl_ref. Qed.

  Lemma go_observe_l (x : t E A) : go (observe x) [= x.
  Proof. apply Ref.ref_fold. apply refF_refl_ref. Qed.

  Lemma ref_go_r (x y : t E A) : x [= go (observe y) <-> x [= y.
  Proof.
    split; intros H; apply Ref.ref_fold; apply Ref.ref_unfold in H; exact H.
  Qed.

  Lemma sup_ub {I} (k : I -> t E A) i : k i [= Sup k.
  Proof. apply Ref.ref_fold. cbn. eapply Ref.refF_sup_r. apply refF_refl_ref. Qed.

  Lemma sup_lub {I} (k : I -> t E A) y : (forall i, k i [= y) -> Sup k [= y.
  Proof.
    intros H. apply Ref.ref_fold. cbn. constructor. intros i. apply ref_go_r. auto.
  Qed.

  Lemma sup_at {I} (i : I) x (k : I -> t E A) : x [= k i -> x [= Sup k.
  Proof.
    intros H. apply Ref.ref_fold. cbn. eapply Ref.refF_sup_r. apply Ref.ref_unfold. exact H.
  Qed.

  Lemma inf_lb {I} (k : I -> t E A) i : Inf k [= k i.
  Proof. apply Ref.ref_fold. cbn. econstructor. apply ref_go_r. reflexivity. Qed.

  Lemma inf_glb {I} x (k : I -> t E A) : (forall i, x [= k i) -> x [= Inf k.
  Proof.
    intros H. apply Ref.ref_fold. cbn. constructor. intros j. apply Ref.ref_unfold. auto.
  Qed.

  Lemma inf_at {I} (i : I) (k : I -> t E A) y : k i [= y -> Inf k [= y.
  Proof.
    intros H. apply Ref.ref_fold. cbn. econstructor. apply ref_go_r. exact H.
  Qed.

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
  Proof. intros H. apply Ref.ref_fold. cbn. constructor. auto. Qed.

  Global Instance sup_ref_proper I : Proper (pointwise_relation I ref ==> ref) (@Sup E A I).
  Proof. intros k k' H. apply sup_mono. exact H. Qed.

  Global Instance inf_ref_proper I : Proper (pointwise_relation I ref ==> ref) (@Inf E A I).
  Proof. intros k k' H. apply inf_mono. exact H. Qed.

  Global Instance sup_eqv_proper I : Proper (pointwise_relation I eqv ==> eqv) (@Sup E A I).
  Proof. intros k k' H. split; apply sup_mono; intros i; apply H. Qed.

  Global Instance inf_eqv_proper I : Proper (pointwise_relation I eqv ==> eqv) (@Inf E A I).
  Proof. intros k k' H. split; apply inf_mono; intros i; apply H. Qed.

  Global Instance vis_ref_proper {ar} (m : E ar) : Proper (pointwise_relation ar ref ==> ref) (@Vis E A ar m).
  Proof. intros k k' H. apply vis_mono. exact H. Qed.

  Global Instance vis_eqv_proper {ar} (m : E ar) : Proper (pointwise_relation ar eqv ==> eqv) (@Vis E A ar m).
  Proof. intros k k' H. split; apply vis_mono; intros n; apply H. Qed.

  (** Silent steps are invisible, and silent divergence is bottom. *)

  Lemma tau_l (x : t E A) : Tau x [= x.
  Proof. apply sup_lub. intros _. reflexivity. Qed.

  Lemma tau_r (x : t E A) : x [= Tau x.
  Proof. apply (sup_at tt). reflexivity. Qed.

  Lemma tau_eqv (x : t E A) : Tau x [=] x.
  Proof. split; [ apply tau_l | apply tau_r ]. Qed.

  CoFixpoint spin : t E A := Tau spin.

  Lemma spin_bot (x : t E A) : spin [= x.
  Proof.
    apply (Ref.ref_coind (fun u v => u = spin)); [ | reflexivity ].
    intros u v ->. cbn. constructor. intros _. reflexivity.
  Qed.

End LATTICE.


(** * Structural maps are monotonic *)

(** Most operations on trees are defined by corecursion over one tree,
  replacing [Ret] leaves by trees and keeping the other nodes.  The
  following lemma proves monotonicity for all of them at once: if two
  such maps agree on the shape of the nodes and their leaf
  replacements are pointwise related, they preserve refinement. *)

Section LMAP.
  Context {E : esig} {A B : Type}.

  Definition layer (fr : A -> t E B) (ft : t E A -> t E B) (o : tF E A (t E A)) : tF E B (t E B) :=
    match o with
    | RetF a => observe (fr a)
    | VisF m k => VisF m (fun n => ft (k n))
    | SupF k => SupF (fun i => ft (k i))
    | InfF k => InfF (fun i => ft (k i))
    end.

  Definition is_layer_map (fr : A -> t E B) (ft : t E A -> t E B) :=
    forall x, observe (ft x) = layer fr ft (observe x).

  Variables (fr gr : A -> t E B) (ft gt : t E A -> t E B).
  Hypothesis Hft : is_layer_map fr ft.
  Hypothesis Hgt : is_layer_map gr gt.
  Hypothesis Hr : forall a, fr a [= gr a.

  Let R (u v : t E B) : Prop :=
    u [= v \/
    exists x x', observe u = layer fr ft (observe x) /\
                 observe v = layer gr gt (observe x') /\
                 x [= x'.

  Lemma layer_ref ox ox' :
    Ref.refF ref ox ox' -> Ref.refF R (layer fr ft ox) (layer gr gt ox').
  Proof.
    intros d. induction d; cbn.
    - eapply Ref.refF_mono; [ | apply Ref.ref_unfold; apply Hr ].
      intros u v H. left. exact H.
    - constructor. intros n. right. exists (k n), (k' n). auto.
    - constructor. intros i. right. exists (k i), (go oy). cbn. auto.
    - econstructor. right. exists (k i), (go oy). cbn. auto.
    - econstructor. rewrite Hgt. exact IHd.
    - constructor. intros j. rewrite Hgt. auto.
  Qed.

  Lemma lmap_mono x x' : x [= x' -> ft x [= gt x'.
  Proof.
    intros H. apply (Ref.ref_coind R).
    - intros u v [Huv | [y [y' [Hu [Hv Hyy']]]]].
      + eapply Ref.refF_mono; [ | apply Ref.ref_unfold; exact Huv ].
        intros u' v' H'. left. exact H'.
      + rewrite Hu, Hv. apply layer_ref. apply Ref.ref_unfold. exact Hyy'.
    - right. exists x, x'. auto.
  Qed.

End LMAP.


(** * Monad laws *)

Section MONAD.
  Context {E : esig}.

  Lemma observe_bind {A B} (f : A -> t E B) (x : t E A) :
    observe (bind f x) = layer f (bind f) (observe x).
  Proof.
    destruct x as [ox]. destruct ox; reflexivity.
  Qed.

  Lemma bind_layer_map {A B} (f : A -> t E B) : is_layer_map f (bind f).
  Proof. intros x. apply observe_bind. Qed.

  Lemma id_layer_map {A} : is_layer_map (@ret E A) (fun x => x).
  Proof. intros [ox]. destruct ox; reflexivity. Qed.

  Lemma bind_mono {A B} (f f' : A -> t E B) (x x' : t E A) :
    (forall a, f a [= f' a) -> x [= x' -> bind f x [= bind f' x'.
  Proof.
    intros Hf. apply lmap_mono with (fr := f) (gr := f'); auto using bind_layer_map.
  Qed.

  Global Instance bind_ref_proper A B :
    Proper (pointwise_relation A ref ==> ref ==> ref) (@bind E A B).
  Proof. intros f f' Hf x x' Hx. apply bind_mono; auto. Qed.

  Global Instance bind_eqv_proper A B :
    Proper (pointwise_relation A eqv ==> eqv ==> eqv) (@bind E A B).
  Proof.
    intros f f' Hf x x' [Hx Hx']. split; apply bind_mono; auto; intros a; apply Hf.
  Qed.

  Lemma bind_ret_l {A} (x : t E A) : bind ret x [=] x.
  Proof.
    split.
    - exact (lmap_mono ret ret (bind ret) (fun y => y) (bind_layer_map ret) id_layer_map
               (fun a => Ref.refl _) x x (Ref.refl x)).
    - exact (lmap_mono ret ret (fun y => y) (bind ret) id_layer_map (bind_layer_map ret)
               (fun a => Ref.refl _) x x (Ref.refl x)).
  Qed.

  Lemma bind_ret_r {A B} (a : A) (f : A -> t E B) : bind f (ret a) [=] f a.
  Proof.
    split; apply Ref.ref_fold; rewrite observe_bind; cbn; apply refF_refl_ref.
  Qed.

  Lemma bind_bind_layer_map {A B C} (g : B -> t E C) (f : A -> t E B) :
    is_layer_map (fun a => bind g (f a)) (fun x => bind g (bind f x)).
  Proof.
    intros x. rewrite observe_bind, observe_bind. destruct x as [ox]. destruct ox; cbn.
    - symmetry. apply observe_bind.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma bind_bind {A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
    bind g (bind f x) [=] bind (fun a => bind g (f a)) x.
  Proof.
    split.
    - exact (lmap_mono _ _ (fun y => bind g (bind f y)) (bind (fun a => bind g (f a)))
               (bind_bind_layer_map g f) (bind_layer_map _) (fun a => Ref.refl _) x x (Ref.refl x)).
    - exact (lmap_mono _ _ (bind (fun a => bind g (f a))) (fun y => bind g (bind f y))
               (bind_layer_map _) (bind_bind_layer_map g f) (fun a => Ref.refl _) x x (Ref.refl x)).
  Qed.

  Lemma bind_int {A X} (f : X -> t E A) (m : E X) : bind f (int m) [=] Vis m f.
  Proof.
    split; apply Ref.ref_fold; rewrite observe_bind; cbn; constructor; intros n;
      apply bind_ret_r.
  Qed.

  Lemma bind_sup {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (Sup k) [=] Sup (fun i => bind f (k i)).
  Proof.
    split; apply Ref.ref_fold; rewrite observe_bind; cbn; apply refF_refl_ref.
  Qed.

  Lemma bind_inf {A B I} (f : A -> t E B) (k : I -> t E A) :
    bind f (Inf k) [=] Inf (fun i => bind f (k i)).
  Proof.
    split; apply Ref.ref_fold; rewrite observe_bind; cbn; apply refF_refl_ref.
  Qed.

  Lemma bind_tau {A B} (f : A -> t E B) (x : t E A) :
    bind f (Tau x) [=] Tau (bind f x).
  Proof. apply bind_sup. Qed.

  (** Unfolding [iter]. *)

  Lemma iter_unfold {A I} (step : I -> t E (I + A)) (i : I) :
    iter step i [=] bind (fun r => match r with
                                  | inl i' => Tau (iter step i')
                                  | inr a => ret a
                                  end) (step i).
  Proof.
    split; apply Ref.ref_fold; exact (refF_refl_ref _).
  Qed.

End MONAD.


(** * Coinduction up to bind contexts and refinement *)

(** A relation closed under one game step up to refinement on the
  right and up to [bind] contexts is included in refinement.  Up to
  refinement on the *left* would be unsound, as for weak
  simulations, because the left rules are the coinductive ones. *)

Section UPTO.
  Context {E : esig} {B : Type}.

  Definition bindclo (L : t E B -> t E B -> Prop) (u v : t E B) : Prop :=
    exists A (y y' : t E A) (k k' : A -> t E B),
      observe u = layer k (bind k) (observe y) /\
      observe v = layer k' (bind k') (observe y') /\
      y [= y' /\ (forall a, L (k a) (k' a)).

  Definition upclo (R : t E B -> t E B -> Prop) (u w : t E B) : Prop :=
    exists v, (R u v \/ u [= v \/ bindclo R u v) /\ v [= w.

  Lemma bindclo_layer (R' L : t E B -> t E B -> Prop) {A} (k k' : A -> t E B) :
    (forall u v, bindclo L u v -> R' u v) ->
    (forall a b, L a b -> Ref.refF R' (observe a) (observe b)) ->
    (forall a, L (k a) (k' a)) ->
    forall oy oy', Ref.refF ref oy oy' ->
    Ref.refF R' (layer k (bind k) oy) (layer k' (bind k') oy').
  Proof.
    intros Hin HL Hk oy oy' d. induction d; cbn.
    - apply HL. apply Hk.
    - constructor. intros n. apply Hin.
      exists A, (k0 n), (k'0 n), k, k'. repeat split; auto using observe_bind.
    - constructor. intros i. apply Hin.
      exists A, (k0 i), (go oy), k, k'. repeat split; auto using observe_bind.
    - econstructor. apply Hin.
      exists A, (k0 i), (go oy), k, k'. repeat split; auto using observe_bind.
    - econstructor. rewrite observe_bind. apply IHd.
    - constructor. intros j. rewrite observe_bind. apply H0.
  Qed.

  Lemma bindclo_closed (R' L : t E B -> t E B -> Prop) :
    (forall u v, bindclo L u v -> R' u v) ->
    (forall a b, L a b -> Ref.refF R' (observe a) (observe b)) ->
    forall u v, bindclo L u v -> Ref.refF R' (observe u) (observe v).
  Proof.
    intros Hin HL u v (A & y & y' & k & k' & Hu & Hv & Hyy' & Hk).
    rewrite Hu, Hv. apply bindclo_layer with (L := L); auto.
    apply Ref.ref_unfold. exact Hyy'.
  Qed.

  Lemma ref_coind_up (R : t E B -> t E B -> Prop) :
    (forall u v, R u v -> Ref.refF (upclo R) (observe u) (observe v)) ->
    forall u v, R u v -> u [= v.
  Proof.
    intros HR u v Huv. apply (Ref.ref_coind (upclo R)).
    - intros u0 w0 [v0 [Huv0 Hvw0]].
      assert (Hstep : Ref.refF (upclo R) (observe u0) (observe v0)).
      { destruct Huv0 as [H | [H | H]].
        - apply HR. exact H.
        - eapply Ref.refF_mono; [ | apply Ref.ref_unfold; exact H ].
          intros a b Hab. exists b. split; [ right; left; exact Hab | reflexivity ].
        - eapply bindclo_closed with (L := R); [ | | exact H ].
          + intros a b Hab. exists b. split; [ right; right; exact Hab | reflexivity ].
          + intros a b Hab. apply HR. exact Hab. }
      apply Ref.ref_unfold in Hvw0.
      eapply Ref.refF_mono; [ | eapply Ref.cut_r; [ exact Hstep | exact Hvw0 ] ].
      intros a c [b [[v' [Hab Hv']] Hbc]]. exists v'. split; [ exact Hab | etransitivity; eauto ].
    - exists v. split; [ left; exact Huv | reflexivity ].
  Qed.

End UPTO.


(** * Substitutions *)

(** Applying a substitution inserts a silent step at every [Vis], as
  [interp] does for interaction trees: it keeps the corecursion
  productive when the substituted tree returns immediately, and it
  makes an infinite chain of immediately-returning operations a
  silent divergence, that is bottom. *)

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

  Definition apply {E F A} (f : t E F) : ISpec.t F A -> ISpec.t E A :=
    cofix ap (x : ISpec.t F A) : ISpec.t E A :=
      match observe x with
      | RetF a => ret a
      | VisF m k => Tau (bind (fun n => ap (k n)) (f _ m))
      | SupF k => Sup (fun i => ap (k i))
      | InfF k => Inf (fun i => ap (k i))
      end.

  Definition compose {E F G} (g : t F G) (f : t E F) : t E G :=
    fun ar m => apply f (g ar m).

  Definition applyF {E F A} (f : t E F) (ap : ISpec.t F A -> ISpec.t E A)
      (o : tF F A (ISpec.t F A)) : tF E A (ISpec.t E A) :=
    match o with
    | RetF a => RetF a
    | VisF m k => SupF (fun _ : unit => bind (fun n => ap (k n)) (f _ m))
    | SupF k => SupF (fun i => ap (k i))
    | InfF k => InfF (fun i => ap (k i))
    end.

  Lemma observe_apply {E F A} (f : t E F) (x : ISpec.t F A) :
    observe (apply f x) = applyF f (apply f) (observe x).
  Proof. destruct x as [ox]. destruct ox; reflexivity. Qed.

End Subst.

Infix "~>" := Subst.t (at level 99).
Infix "[~=" := Subst.ref (at level 70).
Notation "x / f" := (Subst.apply f x).
Infix "@" := Subst.compose (at level 40, left associativity).

Section APPLY.
  Import Subst.

  Lemma apply_mono {E F A} (f f' : E ~> F) (x x' : ISpec.t F A) :
    f [~= f' -> x [= x' -> x / f [= x' / f'.
  Proof.
    intros Hf Hxx'.
    pose (R := fun u v => exists y y' : ISpec.t F A,
                 observe u = applyF f (apply f) (observe y) /\
                 observe v = applyF f' (apply f') (observe y') /\
                 y [= y').
    apply (ref_coind_up R).
    2: { exists x, x'. split; [ apply observe_apply | ]. split; [ apply observe_apply | ]. exact Hxx'. }
    intros u v H. hnf in H. destruct H as (y & y' & Hu & Hv & Hyy'). rewrite Hu, Hv.
    apply Ref.ref_unfold in Hyy'. clear Hu Hv.
    generalize dependent (observe y'). generalize dependent (observe y).
    intros oy oy' d. induction d; cbn.
    - constructor.
    - constructor. intros _.
      exists (go (SupF (fun _ : unit => bind (fun n => apply f' (k' n)) (f' _ m)))).
      split; [ right; right | reflexivity ].
      exists ar, (f _ m), (Tau (f' _ m)), (fun n => apply f (k n)), (fun n => apply f' (k' n)).
      split; [ apply observe_bind | ].
      split; [ reflexivity | ].
      split; [ etransitivity; [ apply Hf | apply tau_r ] | ].
      intros n. exists (k n), (k' n).
      split; [ apply observe_apply | ]. split; [ apply observe_apply | ]. apply H.
    - constructor. intros i.
      exists (go (applyF f' (apply f') oy)). split; [ left | reflexivity ].
      exists (k i), (go oy). split; [ apply observe_apply | ]. split; [ reflexivity | ]. apply H.
    - econstructor.
      exists (go (applyF f' (apply f') oy)). split; [ left | reflexivity ].
      exists (k i), (go oy). split; [ apply observe_apply | ]. split; [ reflexivity | ]. exact H.
    - econstructor. rewrite observe_apply. apply IHd.
    - constructor. intros j. rewrite observe_apply. apply H0.
  Qed.

  Global Instance apply_ref_proper E F A :
    Proper (Subst.ref ==> Ref.ref ==> Ref.ref) (@apply E F A).
  Proof. intros f f' Hf x x' Hx. apply apply_mono; auto. Qed.

  Global Instance apply_eqv_proper E F A :
    Proper (eq ==> eqv ==> eqv) (@apply E F A).
  Proof. intros f f' [] x x' [Hx Hx']. split; apply apply_mono; auto; reflexivity. Qed.

  Global Instance compose_ref_proper E F G :
    Proper (Subst.ref ==> Subst.ref ==> Subst.ref) (@compose E F G).
  Proof. intros g g' Hg f f' Hf ar m. apply apply_mono; auto. Qed.

  Lemma apply_ret {E F A} (f : E ~> F) (a : A) :
    ret a / f [=] ret a.
  Proof. split; apply Ref.ref_fold; rewrite observe_apply; cbn; apply refF_refl_ref. Qed.

  Lemma apply_vis {E F A ar} (f : E ~> F) (m : F ar) (k : ar -> ISpec.t F A) :
    Vis m k / f [=] Tau (bind (fun n => k n / f) (f _ m)).
  Proof. split; apply Ref.ref_fold; rewrite observe_apply; cbn; apply refF_refl_ref. Qed.

  Lemma apply_sup {E F A I} (f : E ~> F) (k : I -> ISpec.t F A) :
    Sup k / f [=] Sup (fun i => k i / f).
  Proof. split; apply Ref.ref_fold; rewrite observe_apply; cbn; apply refF_refl_ref. Qed.

  Lemma apply_inf {E F A I} (f : E ~> F) (k : I -> ISpec.t F A) :
    Inf k / f [=] Inf (fun i => k i / f).
  Proof. split; apply Ref.ref_fold; rewrite observe_apply; cbn; apply refF_refl_ref. Qed.

  Lemma apply_tau {E F A} (f : E ~> F) (x : ISpec.t F A) :
    Tau x / f [=] Tau (x / f).
  Proof. apply apply_sup. Qed.

  Lemma apply_int_r {E F ar} (m : F ar) (f : E ~> F) :
    int m / f [=] f ar m.
  Proof.
    unfold int. rewrite apply_vis, tau_eqv.
    etransitivity; [ | apply bind_ret_l ].
    apply bind_eqv_proper; [ | reflexivity ].
    intros n. apply apply_ret.
  Qed.

End APPLY.


(** * Strong bisimulation *)

(** Several laws hold node for node, not only up to the refinement
  game.  Strong bisimulation is the symmetric relation with no left
  or right rules, so it supports coinduction up to bisimulation on
  both sides and up to [bind] contexts.  It is included in
  refinement, so bisimulation laws transfer to [eqv]. *)

Module Bisim.

  Section BISIM.
    Context {E : esig} {A : Type}.

    Inductive bisimF (R : t E A -> t E A -> Prop) : tF E A (t E A) -> tF E A (t E A) -> Prop :=
      | bisimF_ret a : bisimF R (RetF a) (RetF a)
      | bisimF_vis {ar} (m : E ar) k k' : (forall n, R (k n) (k' n)) -> bisimF R (VisF m k) (VisF m k')
      | bisimF_sup {I} (k k' : I -> t E A) : (forall i, R (k i) (k' i)) -> bisimF R (SupF k) (SupF k')
      | bisimF_inf {I} (k k' : I -> t E A) : (forall i, R (k i) (k' i)) -> bisimF R (InfF k) (InfF k').

    Lemma bisimF_mono (R R' : t E A -> t E A -> Prop) :
      (forall x y, R x y -> R' x y) -> forall o o', bisimF R o o' -> bisimF R' o o'.
    Proof. intros H o o' d. destruct d; constructor; auto. Qed.

    Definition closed (R : t E A -> t E A -> Prop) :=
      forall x y, R x y -> bisimF R (observe x) (observe y).

    Definition bisim (x y : t E A) : Prop := exists R, closed R /\ R x y.

    Lemma bisim_coind R : closed R -> forall x y, R x y -> bisim x y.
    Proof. intros HR x y H. exists R. auto. Qed.

    Lemma bisim_unfold x y : bisim x y -> bisimF bisim (observe x) (observe y).
    Proof.
      intros [R [HR H]]. apply HR in H. eapply bisimF_mono; [ | exact H ].
      intros x' y' H'. exists R. auto.
    Qed.

    Lemma bisim_fold x y : bisimF bisim (observe x) (observe y) -> bisim x y.
    Proof.
      intros H. apply (bisim_coind (fun x y => bisimF bisim (observe x) (observe y))); auto.
      intros x' y' H'. eapply bisimF_mono; [ | exact H' ]. intros x'' y''. apply bisim_unfold.
    Qed.

    Lemma bisimF_refl (R : t E A -> t E A -> Prop) :
      (forall x, R x x) -> forall o, bisimF R o o.
    Proof. intros H o. destruct o; constructor; auto. Qed.

    Lemma refl x : bisim x x.
    Proof.
      apply (bisim_coind (fun x y => x = y)); [ | reflexivity ].
      intros x' y' ->. apply bisimF_refl. auto.
    Qed.

    Lemma cut (X Y : t E A -> t E A -> Prop) o1 o2 o3 :
      bisimF X o1 o2 -> bisimF Y o2 o3 ->
      bisimF (fun u w => exists v, X u v /\ Y v w) o1 o3.
    Proof.
      intros d1 d2. destruct d1; inversion d2; subst; inj_pair; constructor; intros; eexists; eauto.
    Qed.

    Lemma sym x y : bisim x y -> bisim y x.
    Proof.
      intros H. apply (bisim_coind (fun u v => bisim v u)); auto.
      intros u v Huv. apply bisim_unfold in Huv.
      remember (observe v) as ov. remember (observe u) as ou.
      destruct Huv; constructor; intros; cbn; auto.
    Qed.

    Lemma trans x y z : bisim x y -> bisim y z -> bisim x z.
    Proof.
      intros Hxy Hyz.
      apply (bisim_coind (fun u w => exists v, bisim u v /\ bisim v w)); [ | eauto ].
      intros u w [v [Huv Hvw]]. apply bisim_unfold in Huv. apply bisim_unfold in Hvw.
      exact (cut _ _ _ _ _ Huv Hvw).
    Qed.

    Global Instance bisim_equiv : Equivalence bisim.
    Proof. split; [ exact refl | exact sym | exact trans ]. Qed.

  End BISIM.

End Bisim.

Abbreviation bisim := Bisim.bisim.

(** ** Bisimulation implies refinement *)

Lemma bisim_ref {E A} (x y : t E A) : bisim x y -> x [= y.
Proof.
  pose (R := fun u v => bisim u v \/
                        (exists I (k' : I -> t E A) i, bisim u (k' i) /\ v = Sup k') \/
                        (exists v', bisim u v' /\ v = go (observe v'))).
  assert (step : forall o o', Bisim.bisimF bisim o o' -> Ref.refF R o o').
  { intros o o' d. destruct d.
    - constructor.
    - constructor. intros n. left. auto.
    - apply Ref.refF_sup_l. intros i. right. left. exists I, k', i. split; [ apply H | reflexivity ].
    - apply Ref.refF_inf_r. intros j. eapply Ref.refF_inf_l. right. right. exists (k' j).
      split; [ apply H | reflexivity ]. }
  intros H. apply (Ref.ref_coind R); [ | left; exact H ].
  intros u v [Huv | [(I & k' & i & Hu & ->) | (v' & Hu & ->)]].
  - apply step. apply Bisim.bisim_unfold. exact Huv.
  - cbn. eapply Ref.refF_sup_r. apply step. apply Bisim.bisim_unfold. exact Hu.
  - cbn. apply step. apply Bisim.bisim_unfold. exact Hu.
Qed.

Lemma bisim_eqv {E A} (x y : t E A) : bisim x y -> x [=] y.
Proof. intros H. split; apply bisim_ref; [ exact H | symmetry; exact H ]. Qed.

Global Instance bisim_eqv_subrel E A : subrelation (@bisim E A) eqv.
Proof. intros x y. apply bisim_eqv. Qed.

Global Instance bisim_ref_subrel E A : subrelation (@bisim E A) ref.
Proof. intros x y. apply bisim_ref. Qed.

(** ** Coinduction up to bisimulation and bind contexts *)

Section BUPTO.
  Context {E : esig} {B : Type}.

  Definition bbindclo (L : t E B -> t E B -> Prop) (u v : t E B) : Prop :=
    exists A (y y' : t E A) (k k' : A -> t E B),
      observe u = layer k (bind k) (observe y) /\
      observe v = layer k' (bind k') (observe y') /\
      bisim y y' /\ (forall a, L (k a) (k' a)).

  Definition bupclo (R : t E B -> t E B -> Prop) (u w : t E B) : Prop :=
    exists u' v, bisim u u' /\ (R u' v \/ bisim u' v \/ bbindclo R u' v) /\ bisim v w.

  Lemma bbindclo_closed (R' L : t E B -> t E B -> Prop) :
    (forall u v, bbindclo L u v -> R' u v) ->
    (forall a b, L a b -> Bisim.bisimF R' (observe a) (observe b)) ->
    forall u v, bbindclo L u v -> Bisim.bisimF R' (observe u) (observe v).
  Proof.
    intros Hin HL u v (A & y & y' & k & k' & Hu & Hv & Hyy' & Hk).
    rewrite Hu, Hv. apply Bisim.bisim_unfold in Hyy'.
    remember (observe y) as oy. remember (observe y') as oy'. destruct Hyy'; cbn.
    - apply HL. apply Hk.
    - constructor. intros n. apply Hin. exists A, (k0 n), (k'0 n), k, k'.
      split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. auto.
    - constructor. intros i. apply Hin. exists A, (k0 i), (k'0 i), k, k'.
      split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. auto.
    - constructor. intros i. apply Hin. exists A, (k0 i), (k'0 i), k, k'.
      split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. auto.
  Qed.

  Lemma bisim_coind_up (R : t E B -> t E B -> Prop) :
    (forall u v, R u v -> Bisim.bisimF (bupclo R) (observe u) (observe v)) ->
    forall u v, R u v -> bisim u v.
  Proof.
    intros HR u v Huv. apply (Bisim.bisim_coind (bupclo R)).
    - intros u0 w0 (u' & v0 & Hu & Huv0 & Hvw).
      assert (Hstep : Bisim.bisimF (bupclo R) (observe u') (observe v0)).
      { destruct Huv0 as [H | [H | H]].
        - apply HR. exact H.
        - eapply Bisim.bisimF_mono; [ | apply Bisim.bisim_unfold; exact H ].
          intros a b Hab. exists a, b. split; [ reflexivity | ]. split; [ right; left; exact Hab | reflexivity ].
        - eapply bbindclo_closed with (L := R); [ | | exact H ].
          + intros a b Hab. exists a, b. split; [ reflexivity | ]. split; [ right; right; exact Hab | reflexivity ].
          + intros a b Hab. apply HR. exact Hab. }
      apply Bisim.bisim_unfold in Hu. apply Bisim.bisim_unfold in Hvw.
      pose proof (Bisim.cut _ _ _ _ _ Hu Hstep) as H1.
      pose proof (Bisim.cut _ _ _ _ _ H1 Hvw) as H2.
      eapply Bisim.bisimF_mono; [ | exact H2 ].
      intros a c (b & (b' & Hab' & (u1 & v1 & H1' & H2' & H3')) & Hbc).
      exists u1, v1. split; [ etransitivity; eauto | ]. split; [ exact H2' | etransitivity; eauto ].
    - exists u, v. split; [ reflexivity | ]. split; [ left; exact Huv | reflexivity ].
  Qed.

  Lemma bisimF_refl_up (R : t E B -> t E B -> Prop) o : Bisim.bisimF (bupclo R) o o.
  Proof.
    apply Bisim.bisimF_refl. intros x. exists x, x.
    split; [ reflexivity | ]. split; [ right; left; reflexivity | reflexivity ].
  Qed.

End BUPTO.

(** ** Structural maps preserve bisimulation *)

Section BLMAP.
  Context {E : esig} {A B : Type}.
  Variables (fr gr : A -> t E B) (ft gt : t E A -> t E B).
  Hypothesis Hft : is_layer_map fr ft.
  Hypothesis Hgt : is_layer_map gr gt.
  Hypothesis Hr : forall a, bisim (fr a) (gr a).

  Lemma blmap_bisim x x' : bisim x x' -> bisim (ft x) (gt x').
  Proof.
    intros H.
    apply (Bisim.bisim_coind (fun u v => bisim u v \/
      exists x x', observe u = layer fr ft (observe x) /\ observe v = layer gr gt (observe x') /\ bisim x x')).
    - intros u v [Huv | (y & y' & Hu & Hv & Hyy')].
      + eapply Bisim.bisimF_mono; [ | apply Bisim.bisim_unfold; exact Huv ]. intros. left. auto.
      + rewrite Hu, Hv. apply Bisim.bisim_unfold in Hyy'.
        remember (observe y) as oy. remember (observe y') as oy'. destruct Hyy'; cbn.
        * eapply Bisim.bisimF_mono; [ | apply Bisim.bisim_unfold; apply Hr ]. intros. left. auto.
        * constructor. intros n. right. exists (k n), (k' n). auto.
        * constructor. intros i. right. exists (k i), (k' i). auto.
        * constructor. intros i. right. exists (k i), (k' i). auto.
    - right. exists x, x'. auto.
  Qed.

End BLMAP.

Lemma bind_bind_bisim {E A B C} (g : B -> t E C) (f : A -> t E B) (x : t E A) :
  bisim (bind g (bind f x)) (bind (fun a => bind g (f a)) x).
Proof.
  exact (blmap_bisim _ _ (fun y => bind g (bind f y)) (bind (fun a => bind g (f a)))
           (bind_bind_layer_map g f) (bind_layer_map _) (fun a => Bisim.refl _) x x (Bisim.refl x)).
Qed.

Lemma bind_ret_l_bisim {E A} (x : t E A) : bisim (bind ret x) x.
Proof.
  exact (blmap_bisim ret ret (bind ret) (fun y => y) (bind_layer_map ret) id_layer_map
           (fun a => Bisim.refl _) x x (Bisim.refl x)).
Qed.

Global Instance bind_bisim_proper E A B :
  Proper (pointwise_relation A bisim ==> bisim ==> bisim) (@bind E A B).
Proof.
  intros f f' Hf x x' Hx.
  exact (blmap_bisim f f' (bind f) (bind f') (bind_layer_map f) (bind_layer_map f') Hf x x' Hx).
Qed.


(** * Laws of substitution *)

Section APPLYLAWS.
  Import Subst.

  Lemma apply_bind_bisim {E F A B} (f : E ~> F) (g : A -> ISpec.t F B) (x : ISpec.t F A) :
    bisim (bind g x / f) (bind (fun a => g a / f) (x / f)).
  Proof.
    pose (G := fun a => g a / f).
    pose (R := fun u v => exists x : ISpec.t F A,
                 observe u = applyF f (apply f) (layer g (bind g) (observe x)) /\
                 observe v = layer G (bind G) (applyF f (apply f) (observe x))).
    apply (bisim_coind_up R).
    2: { exists x. split.
         - rewrite observe_apply, observe_bind. reflexivity.
         - rewrite observe_bind, observe_apply. reflexivity. }
    intros u v H. hnf in H. destruct H as (y & Hu & Hv). rewrite Hu, Hv. clear Hu Hv.
    destruct y as [oy]. destruct oy; cbn.
    - unfold G. rewrite observe_apply. apply bisimF_refl_up.
    - constructor. intros _.
      exists (bind (fun n => apply f (bind g (k n))) (f _ m)),
             (bind (fun n => bind G (apply f (k n))) (f _ m)).
      split; [ reflexivity | ]. split.
      + right. right.
        exists ar, (f _ m), (f _ m), (fun n => apply f (bind g (k n))), (fun n => bind G (apply f (k n))).
        split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. split; [ reflexivity | ].
        intros n. exists (k n). split.
        * rewrite observe_apply, observe_bind. reflexivity.
        * rewrite observe_bind, observe_apply. reflexivity.
      + symmetry. apply bind_bind_bisim.
    - constructor. intros i.
      exists (apply f (bind g (k i))), (bind G (apply f (k i))).
      split; [ reflexivity | ]. split; [ | reflexivity ].
      left. exists (k i). split.
      + rewrite observe_apply, observe_bind. reflexivity.
      + rewrite observe_bind, observe_apply. reflexivity.
    - constructor. intros i.
      exists (apply f (bind g (k i))), (bind G (apply f (k i))).
      split; [ reflexivity | ]. split; [ | reflexivity ].
      left. exists (k i). split.
      + rewrite observe_apply, observe_bind. reflexivity.
      + rewrite observe_bind, observe_apply. reflexivity.
  Qed.

  Lemma apply_bind {E F A B} (f : E ~> F) (g : A -> ISpec.t F B) (x : ISpec.t F A) :
    bind g x / f [=] bind (fun a => g a / f) (x / f).
  Proof. apply bisim_eqv. apply apply_bind_bisim. Qed.

  Lemma apply_assoc_bisim {E F G A} (f : E ~> F) (g : F ~> G) (x : ISpec.t G A) :
    bisim (x / g / f) (x / (g @ f)).
  Proof.
    pose (R := fun u v => exists x : ISpec.t G A,
                 observe u = applyF f (apply f) (applyF g (apply g) (observe x)) /\
                 observe v = applyF (g @ f) (apply (g @ f)) (observe x)).
    apply (bisim_coind_up R).
    2: { exists x. split; [ rewrite observe_apply, observe_apply; reflexivity | apply observe_apply ]. }
    intros u v H. hnf in H. destruct H as (y & Hu & Hv). rewrite Hu, Hv. clear Hu Hv.
    destruct y as [oy]. destruct oy; cbn.
    - constructor.
    - constructor. intros _.
      exists (bind (fun n => apply f (apply g (k n))) (apply f (g _ m))),
             (bind (fun n => apply (g @ f) (k n)) (apply f (g _ m))).
      split; [ apply apply_bind_bisim | ]. split; [ | reflexivity ].
      right. right.
      exists ar, (apply f (g _ m)), (apply f (g _ m)),
             (fun n => apply f (apply g (k n))), (fun n => apply (g @ f) (k n)).
      split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. split; [ reflexivity | ].
      intros n. exists (k n). split; [ rewrite observe_apply, observe_apply; reflexivity | apply observe_apply ].
    - constructor. intros i.
      exists (apply f (apply g (k i))), (apply (g @ f) (k i)).
      split; [ reflexivity | ]. split; [ | reflexivity ].
      left. exists (k i). split; [ rewrite observe_apply, observe_apply; reflexivity | apply observe_apply ].
    - constructor. intros i.
      exists (apply f (apply g (k i))), (apply (g @ f) (k i)).
      split; [ reflexivity | ]. split; [ | reflexivity ].
      left. exists (k i). split; [ rewrite observe_apply, observe_apply; reflexivity | apply observe_apply ].
  Qed.

  Lemma apply_assoc {E F G A} (f : E ~> F) (g : F ~> G) (x : ISpec.t G A) :
    x / g / f [=] x / (g @ f).
  Proof. apply bisim_eqv. apply apply_assoc_bisim. Qed.

  (** The identity substitution inserts silent steps, so this one is
    only an equivalence, not a bisimulation. *)

  Lemma apply_int_l {E A} (x : ISpec.t E A) : x / Subst.id [=] x.
  Proof.
    split.
    - pose (R := fun u v => exists x : ISpec.t E A,
                   observe u = applyF Subst.id (apply Subst.id) (observe x) /\ v = x).
      apply (ref_coind_up R); [ | exists x; split; [ apply observe_apply | reflexivity ] ].
      intros u v H. hnf in H. destruct H as (y & Hu & ->). rewrite Hu. clear Hu.
      destruct y as [oy]. destruct oy; cbn.
      + constructor.
      + constructor. intros _. exists (bind k (int m)). split.
        * right. right. exists ar, (int m), (int m), (fun n => apply Subst.id (k n)), k.
          split; [ apply observe_bind | ]. split; [ apply observe_bind | ]. split; [ reflexivity | ].
          intros n. exists (k n). split; [ apply observe_apply | reflexivity ].
        * apply (proj1 (bind_int k m)).
      + constructor. intros i. exists (k i).
        split; [ left; exists (k i); split; [ apply observe_apply | reflexivity ] | apply sup_ub ].
      + apply Ref.refF_inf_r. intros j. eapply Ref.refF_inf_l. exists (k j).
        split; [ left; exists (k j); split; [ apply observe_apply | reflexivity ] | apply go_observe_r ].
    - pose (R := fun u v => exists x : ISpec.t E A,
                   u = x /\ observe v = applyF Subst.id (apply Subst.id) (observe x)).
      apply (ref_coind_up R); [ | exists x; split; [ reflexivity | apply observe_apply ] ].
      intros u v H. hnf in H. destruct H as (y & -> & Hv). rewrite Hv. clear Hv.
      destruct y as [oy]. destruct oy; cbn.
      + constructor.
      + eapply Ref.refF_sup_r with (j := tt). rewrite observe_bind. cbn.
        constructor. intros n. exists (apply Subst.id (k n)).
        split; [ left; exists (k n); split; [ reflexivity | apply observe_apply ] | ].
        apply (proj2 (bind_ret_r n (fun n => k n / Subst.id))).
      + constructor. intros i. exists (apply Subst.id (k i)).
        split; [ left; exists (k i); split; [ reflexivity | apply observe_apply ] | ].
        apply (sup_ub (fun i => apply Subst.id (k i)) i).
      + apply Ref.refF_inf_r. intros j. eapply Ref.refF_inf_l. exists (apply Subst.id (k j)).
        split; [ left; exists (k j); split; [ reflexivity | apply observe_apply ] | apply go_observe_r ].
  Qed.

  Definition seqv {E F} (f g : E ~> F) := forall ar m, f ar m [=] g ar m.

  Lemma compose_id_l {E F} (f : E ~> F) : seqv (Subst.id @ f) f.
  Proof. intros ar m. apply apply_int_r. Qed.

  Lemma compose_id_r {E F} (f : E ~> F) : seqv (f @ Subst.id) f.
  Proof. intros ar m. apply apply_int_l. Qed.

  Lemma compose_assoc {E F G H} (h : G ~> H) (g : F ~> G) (f : E ~> F) :
    seqv ((h @ g) @ f) (h @ (g @ f)).
  Proof. intros ar m. apply apply_assoc. Qed.

End APPLYLAWS.

Inductive form :=
| Tr (* true *)
| Fa (* absurd *)
| And (_ _:form) (* conjunction *)
| Or (_ _:form) (* disjunction *)
| Impl (_ _:form) (* Implication *)
| All {A:Type} (_:A->form) (* Universal quantifier *)
| Ex {A:Type} (_:A->form) (* Existential quantifier *)
| Atom (_:Prop) (* Atomic propositions *).

(* We give a name to the context *)
Definition context := form -> Prop.

(* We can extend a context G by adding a proposition p *)
Definition extend (G:context) (x:form) : context := fun y => x = y \/ G y.

(** 1.1.1 *)
Inductive deriv:context -> form -> Prop :=
| TrI : forall (G:context), deriv G Tr
| FaE : forall (G:context) phi, deriv G Fa -> deriv G phi
| Ax : forall (G:context) x, G x -> deriv G x
| AndI  : forall (G:context) p q, deriv G p -> deriv G q -> deriv G (And p q)
| AndEL : forall (G:context) p q, deriv G (And p q) -> deriv G p
| AndER : forall (G:context) p q, deriv G (And p q) -> deriv G q
| OrIL  : forall (G:context) p q, deriv G p -> deriv G (Or p q)
| OrIR  : forall (G:context) p q, deriv G q -> deriv G (Or p q)
| OrE   : forall (G:context) p q phi,
    deriv G (Or p q) -> (deriv (extend G p) phi) -> (deriv (extend G q) phi) -> deriv G phi
| ImplI : forall (G:context) p q, deriv (extend G p) q -> deriv G (Impl p q)
| ImplE : forall (G:context) p q, deriv G (Impl p q) -> deriv G p -> deriv G q
| AllI : forall (G:context) A p, (forall a, deriv G (p a)) -> deriv G (@All A p)
| AllE : forall (G:context) A p, deriv G (@All A p) -> forall a, deriv G (p a)
| ExI  : forall (G:context) A p a, deriv G (p a) -> deriv G (@Ex A p)
| ExE  : forall (G:context) A p q, deriv G (@Ex A p) -> (forall a, deriv (extend G (p a)) q) -> deriv G q.

Create HintDb derivdb.
Hint Constructors deriv : derivdb.

(* Very small tactics allowing to search in the context for a given hypothesis. *)
Ltac explore_context := repeat ((left; easy) + right).
Ltac axiom := apply Ax; explore_context.
(* Apply an arrow that is in the context *)
Ltac harrow p := apply ImplE with p; only 1:axiom.

Definition classical := fun hyp => exists A:form, hyp = Or A (Impl A Fa).

(* The negation *)
Definition neg := fun x => Impl x Fa.

(** 1.1.2 *)
Lemma drinker (bar:Type) (barfly:bar) (drinks:bar->Prop) :
  deriv classical (Ex (fun p =>Impl (Atom (drinks p)) (All (fun q => Atom (drinks q))))).
Proof.
  apply OrE with (p:=(Ex (fun p => neg (Atom (drinks p))))) (q:= neg (Ex (fun p => neg (Atom (drinks p))))).
  - apply Ax; exists (Ex (fun p => neg (Atom (drinks p)))); easy.
  - apply ExE with (p:=(fun p : bar => neg (Atom (drinks p)))).
    + axiom.
    + intros a.
      apply ExI with a.
      apply ImplI, FaE.
      harrow (Atom (drinks a)); axiom.
  - apply ExI with barfly, ImplI, AllI; intros a.
    apply OrE with (p:=Atom (drinks a)) (q:= neg (Atom (drinks a))).
    + apply Ax; right; right; exists (Atom (drinks a)); easy.
    + axiom.
    + apply FaE.
      harrow (Ex (fun p : bar => neg (Atom (drinks p)))).
      apply ExI with a.
      axiom.
Qed.

(* The inclusion of contexts. Useful to state intermediate lemmas. *)
Definition Included (X Y: context) := forall a, X a -> Y a.

Lemma Included_extend X p: Included X (extend X p).
Proof. firstorder. Qed.

(* extend is monotonic w.r.t the inclusion *)
Lemma extend_mon_Included X Y p: Included X Y -> Included (extend X p) (extend Y p).
Proof.
  intros H x R; destruct R; firstorder.
Qed.

(** 1.2.1 *)
Lemma deriv_weakening (L L':context) f : deriv L f -> Included L L' -> deriv L' f.
Proof.
  intros H; revert L'; induction H; intros L' I; eauto using extend_mon_Included with derivdb.
  apply OrE with p q; firstorder.
Qed.

(* All formulas in L are provable from L' *)
Definition ProvableFrom (L L':context) := forall f, L f -> deriv L' f.

(* extend is monotonic w.r.t. the ProvableFrom predicate *)
Lemma extend_mon_ProvableFrom X Y p : ProvableFrom X Y -> ProvableFrom (extend X p) (extend Y p).
Proof.
  intros H x R; destruct R.
  - destruct H0; apply Ax; left; easy.
  - apply deriv_weakening with (L:=Y).
    + now apply H.
    + apply Included_extend.
Qed.

(** 1.2.2 *)
Lemma deriv_substitution (L L':context) f : deriv L f -> ProvableFrom L L' -> deriv L' f.
Proof.
  intros H; revert L'; induction H; intros L' I; eauto using extend_mon_ProvableFrom with derivdb.
  apply OrE with p q.
  - firstorder.
  - now apply IHderiv2, extend_mon_ProvableFrom.
  - now apply IHderiv3, extend_mon_ProvableFrom.
Qed.

(** 2.1.1 *)
Fixpoint nnt (x:form) :=
  match x with
  | Tr => Tr
  | Fa => Fa
  | Atom x => neg (neg (Atom x))
  | And x y => And (nnt x) (nnt y)
  | Or x y => neg (neg (Or (nnt x) (nnt y)))
  | Impl x y => Impl (nnt x) (nnt y)
  | All p => All (fun x => nnt (p x))
  | Ex p => neg (neg (Ex (fun x => nnt (p x)))) end.

(* One can "extend" the context if possible *)
Lemma extend_context L p f : deriv L p -> deriv (extend L p) f -> deriv L f.
Proof.
  intros H x.
  apply deriv_substitution with (L:= extend L p).
  - easy.
  - intros y I.
    destruct I.
    + now destruct H0.
    + eauto with derivdb.
Qed.

(** 2.2.1 *)
Lemma double_elimination L f : deriv L (neg (neg (nnt f))) -> deriv L (nnt f).
Proof.
  revert L; induction f; intros L D; simpl in *.
  - eauto with derivdb.
  - apply extend_context with (p:=neg (neg Fa)); try easy.
    harrow (neg Fa).
    apply ImplI; axiom.
  - apply extend_context with (p:=(neg (neg (And (nnt f1) (nnt f2))))); try easy.
    apply AndI.
    + apply IHf1, ImplI.
      harrow (neg (And (nnt f1) (nnt f2))).
      apply ImplI.
      harrow (nnt f1).
      apply AndEL with (q:= nnt f2); axiom.
    + apply IHf2, ImplI.
      harrow (neg (And (nnt f1) (nnt f2))).
      apply ImplI.
      harrow (nnt f2).
      apply AndER with (p:= nnt f1); axiom.
  - apply extend_context with (p:=(neg (neg (neg (neg (Or (nnt f1) (nnt f2))))))); try easy.
    apply ImplI.
    harrow (neg (neg (neg (Or (nnt f1) (nnt f2))))).
    apply ImplI.
    harrow (neg (Or (nnt f1) (nnt f2))).
    axiom.
  - apply extend_context with (p:=(neg (neg (Impl (nnt f1) (nnt f2))))); try easy.
    apply ImplI, IHf2, ImplI.
    harrow (neg (Impl (nnt f1) (nnt f2))).
    apply ImplI.
    harrow (nnt f2); harrow (nnt f1); axiom.
  - apply extend_context with (p:=(neg (neg (All (fun x : A => nnt (f x)))))); try easy.
    apply AllI; intros a.
    apply H, ImplI.
    harrow (neg (All (fun x : A => nnt (f x)))).
    apply ImplI.
    harrow (nnt (f a)).
    apply AllE with (p:= fun x => nnt (f x)).
    axiom.
  - apply extend_context with (neg (neg (neg (neg (Ex (fun x : A => nnt (f x))))))); try easy.
    apply ImplI.
    harrow (neg (neg (neg (Ex (fun x : A => nnt (f x)))))).
    apply ImplI.
    harrow (neg (Ex (fun x : A => nnt (f x)))).
    axiom.
  - apply extend_context with (neg (neg (neg (neg (Atom P))))); try easy.
    apply ImplI.
    harrow (neg (neg (neg (Atom P)))).
    apply ImplI.
    harrow (neg (Atom P)).
    apply ImplI.
    harrow (Atom P).
    axiom.
Qed.

Definition nnt_context L := fun p => exists p', p=nnt p' /\ L p'.

Definition EquivContext (X Y: context) := forall p, X p <-> Y p.

Lemma nnt_context_extend L p : EquivContext (nnt_context (extend L p)) (extend (nnt_context L) (nnt p)).
Proof.
  intros x.
  split.
  - firstorder; destruct H0,H; firstorder.
  - firstorder; destruct H; exists p; firstorder.
Qed.

Lemma replace_context L L' f: EquivContext L L' -> deriv L f -> deriv L' f.
Proof.
  intros E H.
  apply deriv_weakening with L; try easy; firstorder.
Qed.

(** 2.2.2 *)
Lemma ntt_soundness L f : deriv L f -> deriv (nnt_context L) (nnt f).
Proof.
  induction 1; simpl in *.
  1-2:eauto with derivdb.
  2-4:eauto with derivdb.
  6-7:eauto with derivdb.
  - apply Ax; exists x; easy.
  - apply ImplI; harrow (Or (nnt p) (nnt q)); apply OrIL with (q:= (nnt q)).
    apply deriv_weakening with (L:=nnt_context G); firstorder.
  - apply ImplI; harrow (Or (nnt p) (nnt q)); apply OrIR with (p:= (nnt p)).
    apply deriv_weakening with (L:=nnt_context G); firstorder.
  - apply double_elimination.
    apply extend_context with (neg (neg (Or (nnt p) (nnt q)))); try easy.
    apply ImplI.
    harrow (neg (Or (nnt p) (nnt q))).
    apply ImplI.
    harrow (nnt phi).
    apply OrE with (p:=nnt p) (q:=nnt q).
    + axiom.
    + apply deriv_weakening with (nnt_context (extend G p)); try easy.
      intros x E; apply nnt_context_extend in E; firstorder.
    + apply deriv_weakening with (nnt_context (extend G q)); try easy.
      intros x E; apply nnt_context_extend in E; firstorder.
  - apply ImplI.
    apply replace_context with (nnt_context (extend G p)); [apply nnt_context_extend | easy].
  - apply extend_context with (All (fun x : A => nnt (p x))); try easy.
    apply AllE with (p:=(fun x : A => nnt (p x))).
    axiom.
  - apply extend_context with (nnt (p a)); try easy.
    apply ImplI.
    harrow (Ex (fun x : A => nnt (p x))).
    apply ExI with a; axiom.
  - apply double_elimination.
    apply extend_context with (neg (neg (Ex (fun x : A => nnt (p x))))); try easy.
    apply ImplI.
    harrow (neg (Ex (fun x : A => nnt (p x)))).
    apply ImplI.
    harrow (nnt q).
    apply ExE with (p:= fun x => nnt (p x)).
    + axiom.
    + intros a.
      specialize H1 with a.
      apply deriv_weakening with (nnt_context (extend G (p a))); try easy.
      intros x E; apply nnt_context_extend in E; firstorder.
Qed.

Inductive classic : form -> Prop :=
  Cem P : classic (Or P (Impl P Fa)).

(* Intuitionistic de Morgan *)
Lemma neg_or L A B : deriv L (Impl (neg (Or A B)) (And (neg A) (neg B))).
Proof.
  apply ImplI, AndI; apply ImplI; harrow (Or A B).
  - apply OrIL; axiom.
  - apply OrIR; axiom.
Qed.

(** 3.1.1 *)
Lemma nnt_classic L P: deriv L (nnt (Or P (Impl P Fa))).
Proof.
  simpl; apply ImplI.
  harrow (Or (nnt P) (Impl (nnt P) Fa)).
  apply extend_context with (And (neg (nnt P)) (neg (neg (nnt P)))).
  - apply ImplE with (p:=neg (Or (nnt P) (neg (nnt P)))).
    apply neg_or.
    axiom.
  - apply OrIL.
    apply double_elimination.
    apply AndER with (p:=neg (nnt P)).
    axiom.
Qed.

Definition union (L L' : context) := fun y => L y \/ L' y.

Lemma nnt_context_union L L' :
  EquivContext (nnt_context (union L L')) (union (nnt_context L) (nnt_context L')).
Proof. firstorder. Qed.

(** 3.2.1 *)
Lemma excluded_middle_elim L f : deriv (union classic L) f -> deriv (nnt_context L) (nnt f).
Proof.
  intros H.
  apply deriv_substitution with (L:=nnt_context (union classic L)).
  - now apply ntt_soundness.
  - intros x E.
    apply nnt_context_union in E.
    destruct E.
    + destruct H0 as (y,(E,Hy)); symmetry in E; destruct E.
      destruct Hy.
      apply nnt_classic.
    + now apply Ax.
Qed.

Notation "a == b" := (Atom (a = b)) (at level 90).

Inductive equality (A:Type) : form -> Prop :=
| Reflexivity : equality A (All (fun x:A => x == x))
| Symmetry : equality A (All (fun x:A => All (fun y => Impl (x == y) (y == x))))
| Transitivity : equality A (All (fun x:A =>All (fun y => All (fun z => Impl (x == y) (Impl (y == z) (x == z)))))).

(** 5.1.1 *)
Fixpoint intf f : Prop :=
  match f with
  | Tr => True
  | Fa => False
  | And x y => intf x /\ intf y
  | Or x y => intf x \/ intf y
  | Impl x y => intf x -> intf y
  | All p => forall x, intf (p x)
  | Ex p => exists x, intf (p x)
  | Atom X => X end.

(* A predicate to say that the context is sound. *)
Definition sound_context (G:context) := forall x, G x -> intf x.

(* Extending a sound context with a sound formula is sound. *)
Lemma sound_extend L p : sound_context L -> intf p -> sound_context (extend L p).
Proof.
  intros S I x U; destruct U; [destruct H; easy | firstorder].
Qed.

(** 5.2.1 *)
Lemma intf_sound L f : sound_context L -> deriv L f -> intf f.
Proof.
  induction 2; firstorder using sound_extend.
Qed.

(** 5.3.1.1 *)
Lemma sound_equality A : sound_context (equality A).
Proof.
  intros x Ex.
  destruct Ex.
  - easy.
  - now intros x y [].
  - now intros x y z [] [].
Qed.

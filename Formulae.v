Inductive form :=
| Tr (* true *)
| Fa (* absurd *)
| And (_ _:form) (* conjunction *)
| Or (_ _:form) (* disjunction *)
| Impl (_ _:form) (* Implication *)
| All {A:Type} (_:A->form) (* Universal quantifier *)
| Ex {A:Type} (_:A->form) (* Existential quantifier *)
| Atom (_:Prop) (* Atomic propositions *).

Definition context := form -> Prop.

Definition extend (G:context) (x:form) : context := fun y => x = y \/ G y.

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
| AllI : forall A (G:context) p, (forall a, deriv G (p a)) -> deriv G (@All A p)
| AllE : forall A (G:context) p a, deriv G (@All A p) -> deriv G (p a)
| ExI  : forall A (G:context) p a, deriv G (p a) -> deriv G (@Ex A p)
| ExE  : forall A (G:context) p q, deriv G (@Ex A p) -> (forall a, deriv (extend G (p a)) q) -> deriv G q.

Create HintDb derivdb.
Hint Constructors deriv : derivdb.

Definition classical := fun hyp => exists A:form, hyp = Or A (Impl A Fa).

Definition empty A := fun (_:A) => True.

Definition neg := fun x => Impl x Fa.

Lemma drinker (bar:Type) (barfly:bar) (drinks:bar->Prop) :
  deriv classical (Ex (fun p =>Impl (Atom (drinks p)) (All (fun q => Atom (drinks q))))).
Proof.
  apply OrE with (p:=(All (fun p => Atom (drinks p)))) (q:= neg (All (fun p => Atom (drinks p)))).
  - apply Ax. exists ((All (fun p => Atom (drinks p)))); easy.
  - apply ExI with (a:=barfly).
    apply ImplI, Ax.
    right; left.
    easy.
  - apply ImplE with (p:=Ex (fun x => neg (Atom (drinks x)))). (* There exists someone not drinking *)
    + apply ImplI.
      apply ExE with _ (fun x : bar => neg (Atom (drinks x))).
      * apply Ax; left; easy.
      * intros a.
        apply ExI with a.
        apply ImplI, FaE.
        apply ImplE with (p:=(Atom (drinks a))); apply Ax; [right; left | left] ; easy.
    + admit.
Admitted.

Definition Included (X Y: context) := forall a, X a -> Y a.

Lemma Included_extend X p: Included X (extend X p).
Proof. firstorder. Qed.

Lemma extend_mon_Included X Y p: Included X Y -> Included (extend X p) (extend Y p).
Proof.
  intros H x R; destruct R; firstorder.
Qed.
Lemma deriv_weakening (L L':context) f : deriv L f -> Included L L' -> deriv L' f.
Proof.
  intros H; revert L'; induction H; intros L' I.
  1-8:eauto with derivdb.
  3-7:eauto with derivdb.
  - apply OrE with p q; firstorder.
  - now apply ImplI, IHderiv, extend_mon_Included.
  - apply ExE with A p.
    + now apply IHderiv.
    + intros a; now apply H1 with a, extend_mon_Included.
Qed.

Definition ProvableFrom (L L':context) := forall f, L f -> deriv L' f.

Lemma extend_mon_ProvableFrom X Y p : ProvableFrom X Y -> ProvableFrom (extend X p) (extend Y p).
Proof.
  intros H x R; destruct R.
  - destruct H0; apply Ax; left; easy.
  - apply deriv_weakening with (L:=Y).
    + now apply H.
    + apply Included_extend.
Qed.

Lemma deriv_substitution (L L':context) f : deriv L f -> ProvableFrom L L' -> deriv L' f.
Proof.
  intros H; revert L'; induction H; intros L' I.
  1-8:eauto with derivdb.
  3-7:eauto with derivdb.
  - apply OrE with p q.
    + firstorder.
    + now apply IHderiv2, extend_mon_ProvableFrom.
    + now apply IHderiv3, extend_mon_ProvableFrom.
  - apply ImplI, IHderiv.
    now apply extend_mon_ProvableFrom.
  - apply ExE with A p.
    + now apply IHderiv.
    + intros a; now apply H1 with a, extend_mon_ProvableFrom.
Qed.

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

Lemma double_elimination L f : deriv L (neg (neg (nnt f))) -> deriv L (nnt f).
Proof.
  revert L; induction f; intros L D; simpl in *.
  - eauto with derivdb.
  - apply deriv_substitution with (L:= extend L (neg (neg Fa))).
    + apply ImplE with (p:=neg Fa).
      * apply Ax; left; easy.
      * apply ImplI, Ax; left; easy.
    + intros f E.
      destruct E.
      * now destruct H.
      * now apply Ax.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

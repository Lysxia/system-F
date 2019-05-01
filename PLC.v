Require Import List.
Import ListNotations.

(** * Generic dependent data structures *)

Variant void1 {T : Type} : T -> Type := .
Variant sum1 {T : Type} (A B : T -> Type) (t : T) : Type :=
| inl1 : A t -> sum1 A B t
| inr1 : B t -> sum1 A B t
.

Arguments inl1 {T A B t} _.
Arguments inr1 {T A B t} _.

Record iso (A B : Type) : Type :=
  { iso_from : A -> B
  ; iso_to   : B -> A
  }.

Arguments iso_from {A B} _.
Arguments iso_to {A B} _.

Definition iso_id {A} : iso A A :=
  {| iso_from := fun i => i ; iso_to := fun i => i |}.

(** ** Generic collections *)

(** Length-indexed lists *)
Fixpoint vec (A : Type) (n : nat)
  : Type :=
  match n with
  | O => unit
  | S n => A * vec A n
  end.

(** Bounded indices *)
Fixpoint tyvar (n : nat) : Type :=
  match n with
  | O => Empty_set
  | S n => option (tyvar n)
  end.

(** Bounded lookup *)
Fixpoint lookup_tyvar {A : Type} {n : nat}
  : tyvar n -> vec A n -> A :=
  match n with
  | O => fun y => match y with end
  | S n => fun tv ts =>
    match tv with
    | None => fst ts
    | Some tv => lookup_tyvar tv (snd ts)
    end
  end.

(** Heterogeneous lists (list-indexed lists) *)
Fixpoint dvec {A : Type} (f : A -> Type) (xs : list A)
  : Type :=
  match xs with
  | [] => unit
  | x :: xs => f x * dvec f xs
  end.

(** Heterogeneous lists indexed by two lists. *)
Fixpoint zipvec {A B : Type} {n : nat} (f : A -> B -> Type)
  : vec A n -> vec B n -> Type :=
  match n with
  | O => fun _ _ => unit
  | S n => fun ts1 ts2 =>
      (f (fst ts1) (fst ts2) * zipvec f (snd ts1) (snd ts2))%type
  end.

(** Bounded lookup *)
Fixpoint lookup_tyvar_zipvec {A B} {f : A -> B -> Type} {n : nat}
  : forall {ts1 : vec A n} {ts2 : vec B n} (tv : tyvar n),
      zipvec f ts1 ts2 -> f (lookup_tyvar tv ts1) (lookup_tyvar tv ts2) :=
  match n with
  | O => fun _ _ tv => match tv with end
  | S n => fun ts1 ts2 tv rs =>
      match tv with
      | None => fst rs
      | Some tv => lookup_tyvar_zipvec tv (snd rs)
      end
  end.

Arguments lookup_tyvar_zipvec : simpl never.
Arguments lookup_tyvar : simpl never.

Definition rvec {n : nat} : vec Type n -> vec Type n -> Type :=
  zipvec (fun a b => a -> b -> Prop).

(** ** Shifts *)

Fixpoint shift_tyvar (m : nat) {n : nat} : tyvar n -> tyvar (S n) :=
  match n with
  | O => fun v => match v with end
  | S n => fun v =>
    match m with
    | O => Some v
    | S m =>
      match v with
      | None => None
      | Some v => Some (shift_tyvar m v)
      end
    end
  end.

Fixpoint shift_vec {A} (m : nat) (t0 : A) {n : nat}
  : vec A n -> vec A (S n) :=
  match m with
  | O => fun ts => (t0, ts)
  | S m =>
    match n with
    | O => fun _ => (t0, tt)
    | S n => fun ts => (fst ts, shift_vec m t0 (snd ts))
    end
  end.

Fixpoint shift_sem_var (m : nat) (t0 : Type) {n : nat}
  : forall {ts : vec Type n} (tv : tyvar n),
      iso (lookup_tyvar tv ts) (lookup_tyvar (shift_tyvar m tv) (shift_vec m t0 ts)) :=
  match n with
  | O => fun ts tv => match tv with end
  | S n => fun ts tv =>
    match m with
    | O => iso_id
    | S m =>
      match tv with
      | None => iso_id
      | Some tv => shift_sem_var m t0 tv
      end
    end
  end.

Fixpoint shift_rvec (m : nat) {n : nat}
  {t01 t02 : Type} (r0 : t01 -> t02 -> Prop)
  : forall {ts01 ts02 : vec Type n},
      rvec ts01 ts02 -> rvec (shift_vec m t01 ts01) (shift_vec m t02 ts02) :=
  match m with
  | O => fun _ _ rs => (r0, rs)
  | S m =>
    match n with
    | O => fun _ _ rs => (r0, rs)
    | S n => fun _ _ rs => (fst rs, shift_rvec m r0 (snd rs))
    end
  end.

(** * Polymorphic lambda calculus *)

(** ** Syntax *)

(** *** Types *)

Inductive ty (n : nat) : Type :=
| Arrow : ty n -> ty n -> ty n
| Forall : ty (S n) -> ty n
| Tyvar : tyvar n -> ty n
| Bool : ty n
.

Arguments Arrow {n}.
Arguments Forall {n}.
Arguments Tyvar {n}.
Arguments Bool {n}.

Fixpoint var (n : nat) (vs : list (ty n))
  : ty n -> Type :=
  match vs with
  | [] => void1
  | t :: vs => sum1 (eq t) (var n vs)
  end.

Fixpoint shift_ty (m : nat) {n : nat} (t : ty n) : ty (S n) :=
  match t with
  | Arrow t1 t2 => Arrow (shift_ty m t1) (shift_ty m t2)
  | Forall t => Forall (shift_ty (S m) t)
  | Tyvar v => @Tyvar (S n) (shift_tyvar m v)
  | Bool => Bool
  end.

(** *** Terms *)

Inductive tm (n : nat) (vs : list (ty n)) : ty n -> Type :=
| TAbs {t} : tm (S n) (map (shift_ty 0) vs) t -> tm n vs (Forall t)
| Abs {t1 t2} : tm n (t1 :: vs) t2 -> tm n vs (Arrow t1 t2)
| App {t1 t2} : tm n vs (Arrow t1 t2) -> tm n vs t1 -> tm n vs t2
| Con : bool -> tm n vs Bool
| Var {t} : var n vs t -> tm n vs t
.

Arguments TAbs {n vs t}.
Arguments Abs {n vs t1 t2}.
Arguments App {n vs t1 t2}.
Arguments Con {n vs}.
Arguments Var {n vs t}.

(** ** Semantics *)

(** Semantics of types as Coq types *)
Fixpoint sem_ty {n : nat} (ts : vec Type n) (t : ty n)
  : Type :=
  match t with
  | Arrow t1 t2 => sem_ty ts t1 -> sem_ty ts t2
  | Forall t => forall (t0 : Type), @sem_ty (S n) (t0, ts) t
  | Tyvar tv => lookup_tyvar tv ts
  | Bool => bool
  end.

Fixpoint shift_sem (m : nat) {n : nat} {ts : vec Type n} (t0 : Type) (t : ty n)
  : iso (sem_ty ts t) (@sem_ty (S n) (shift_vec m t0 ts) (shift_ty m t)) :=
  match t with
  | Arrow t1 t2 =>
      let i1 := shift_sem m t0 t1 in
      let i2 := shift_sem m t0 t2 in
      {| iso_from := fun f x1 => iso_from i2 (f (iso_to i1 x1))
       ; iso_to := fun f x0 => iso_to i2 (f (iso_from i1 x0))
      |}
  | Forall t =>
      {| iso_from := fun (f : forall a : Type, @sem_ty (S n) (a, ts) t) a =>
           let i := @shift_sem (S m) (S n) (a, ts) t0 t in
           iso_from i (f a)
       ; iso_to := fun (f : forall a : Type, @sem_ty (S (S n)) (a, _) (shift_ty (S m) t)) a =>
           let i := @shift_sem (S m) (S n) (a, _) t0 t in
           iso_to i (f a)
      |} : iso (forall (a : Type), @sem_ty (S n) (a, ts) t) _
  | Tyvar tv => shift_sem_var m t0 tv
  | Bool => iso_id
  end.

Fixpoint shift_dvec {n : nat} {ts : vec Type n} {vs : list (ty n)} (t0 : Type)
  : dvec (sem_ty ts) vs -> dvec (@sem_ty (S n) (t0, ts)) (map (shift_ty 0) vs) :=
  match vs with
  | [] => fun _ => tt
  | t :: vs => fun ts =>
    (iso_from (shift_sem 0 t0 _) (fst ts), shift_dvec t0 (snd ts))
  end.

(* TODO: Generalize *)
Fixpoint lookup_var {n} {f : ty n -> Type} {vs t}
  : var n vs t -> dvec f vs -> f t :=
  match vs with
  | [] => fun v => match v with end
  | t :: vs => fun v =>
    match v with
    | inl1 e =>
      match e with
      | eq_refl => fun vls => fst vls
      end
    | inr1 v => fun vls => lookup_var v (snd vls)
    end
  end.

(** Semantics of terms as Coq values *)
Fixpoint sem_tm
  {n : nat} (ts : vec Type n)
  {vs : list (ty n)} (vls : dvec (sem_ty ts) vs)
  {t : ty n} (u : tm n vs t)
  : sem_ty ts t :=
  match u with
  | TAbs u => fun t0 => @sem_tm (S n) (t0, ts) _ (shift_dvec t0 vls) _ u
  | Abs u => fun x => @sem_tm _ ts (_ :: vs) (x, vls) _ u
  | App u1 u2 => (sem_tm ts vls u1) (sem_tm ts vls u2)
  | Con b => b
  | Var v => lookup_var v vls
  end.

(** Relational semantics of types *)
Fixpoint sem2_ty {n : nat}
  {ts1 ts2 : vec Type n}
  (rs : rvec ts1 ts2)
  (t : ty n)
  : sem_ty ts1 t -> sem_ty ts2 t -> Prop :=
  match t with
  | Arrow t1 t2 => fun f1 f2 =>
      forall x1 x2, sem2_ty rs t1 x1 x2 -> sem2_ty rs t2 (f1 x1) (f2 x2)
  | Forall t => fun f1 f2 =>
      forall (t01 t02 : Type) (r0 : t01 -> t02 -> Prop),
        @sem2_ty (S n) (t01, ts1) (t02, ts2) (r0, rs) t (f1 t01) (f2 t02)
  | Tyvar tv => lookup_tyvar_zipvec tv rs
  | Bool => eq
  end.

(** Relational semantics of contexts *)
Fixpoint sem2_ctx {n : nat} {vs : list (ty n)}
  : forall
      {ts1 ts2 : vec Type n} (rs : rvec ts1 ts2)
      (vls1 : dvec (sem_ty ts1) vs) (vls2 : dvec (sem_ty ts2) vs),
        Prop :=
  match vs with
  | [] => fun _ _ _ _ _ => True
  | v :: vs => fun _ _ rs vls1 vls2 =>
    sem2_ty rs v (fst vls1) (fst vls2) /\
    sem2_ctx rs (snd vls1) (snd vls2)
  end.

(** ** Parametricity theorem *)

(** Shifts preserve relations *)

Lemma param_shift_tyvar_from (m : nat)
  : forall {n : nat}
      (ts1 ts2 : vec Type n)
      (rs : rvec ts1 ts2)
      (v : tyvar n)
      (t01 t02 : Type) (r0 : t01 -> t02 -> Prop)
      (vl1 : lookup_tyvar v ts1) (vl2 : lookup_tyvar v ts2)
      , lookup_tyvar_zipvec v rs vl1 vl2 ->
        lookup_tyvar_zipvec (shift_tyvar m v) (shift_rvec m r0 rs)
          (iso_from (shift_sem_var m t01 v) vl1)
          (iso_from (shift_sem_var m t02 v) vl2).
Proof.
  induction m; intros; cbn; (destruct n; [ destruct v |]); auto.
  destruct v; cbn; auto.
  apply IHm. auto.
Qed.

Lemma param_shift_tyvar_to (m : nat)
  : forall {n : nat}
      (ts1 ts2 : vec Type n)
      (rs : rvec ts1 ts2)
      (v : tyvar n)
      (t01 t02 : Type) (r0 : t01 -> t02 -> Prop)
      (vl1' : lookup_tyvar (shift_tyvar m v) (shift_vec m t01 ts1))
      (vl2' : lookup_tyvar (shift_tyvar m v) (shift_vec m t02 ts2))
      , lookup_tyvar_zipvec (shift_tyvar m v) (shift_rvec m r0 rs) vl1' vl2'->
        lookup_tyvar_zipvec v rs
          (iso_to (shift_sem_var m t01 v) vl1')
          (iso_to (shift_sem_var m t02 v) vl2').
Proof.
  induction m; intros; cbn; (destruct n; [ destruct v |]); auto.
  destruct v; cbn in *; auto.
  apply IHm in H. auto.
Qed.

Lemma param_shift (m : nat) {n : nat}
  (ts1 ts2 : vec Type n)
  (rs : rvec ts1 ts2)
  (t : ty n)
  (t01 t02 : Type)
  (r0 : t01 -> t02 -> Prop)
  : (forall (vl1 : sem_ty ts1 t) (vl2 : sem_ty ts2 t),
       sem2_ty rs t vl1 vl2 ->
       @sem2_ty (S n) _ _ (shift_rvec m r0 rs) (shift_ty m t)
         (iso_from (shift_sem m t01 _) vl1)
         (iso_from (shift_sem m t02 _) vl2))
  /\ (forall vl1' vl2',
       sem2_ty (shift_rvec m r0 rs) (shift_ty m t) vl1' vl2' ->
       sem2_ty rs t
         (iso_to (shift_sem m t01 _) vl1')
         (iso_to (shift_sem m t02 _) vl2')).
Proof.
  revert m.
  induction t; cbn; intros; auto.
  - edestruct IHt1, IHt2; auto.
  - split; intros;
      eapply (IHt (_, ts1) (_, ts2) (r1, rs) (S m));
      eauto.
  - split; intros.
    + auto using param_shift_tyvar_from.
    + eauto using param_shift_tyvar_to.
Qed.

Lemma param_tabs {n : nat}
  (ts1 ts2 : vec Type n)
  (rs : rvec ts1 ts2)
  (vs : list (ty n)) (vls1 : dvec (sem_ty ts1) vs) (vls2 : dvec (sem_ty ts2) vs)
  (t01 t02 : Type)
  (r0 : t01 -> t02 -> Prop)
  : sem2_ctx rs vls1 vls2 ->
    @sem2_ctx (S n) _ (t01, ts1) (t02, ts2) (r0, rs)
      (shift_dvec t01 vls1)
      (shift_dvec t02 vls2).
Proof.
  induction vs; auto.
  destruct vls1, vls2; cbn.
  intros []; split; auto.
  apply (param_shift 0); auto.
Qed.

Lemma param_var {n : nat}
  (ts1 ts2 : vec Type n)
  (rs : rvec ts1 ts2)
  (vs : list (ty n)) (vls1 : dvec (sem_ty ts1) vs) (vls2 : dvec (sem_ty ts2) vs)
  (t : ty n)
  (v : var n vs t)
  : sem2_ctx rs vls1 vls2 ->
    sem2_ty rs t (lookup_var v vls1) (lookup_var v vls2).
Proof.
  induction vs; [ contradiction | ].
  destruct v.
  - destruct vls1, vls2; cbn in *.
    destruct e; cbn.
    intros []; auto.
  - destruct vls1, vls2; cbn in *.
    intros []; auto.
Qed.

(* Main theorem! Every term satisfies the logical relation of its type. *)
Definition parametricity {n : nat}
  (ts1 ts2 : vec Type n)
  (rs : rvec ts1 ts2)
  (vs : list (ty n)) (vls1 : dvec (sem_ty ts1) vs) (vls2 : dvec (sem_ty ts2) vs)
  (t : ty n)
  (u : tm n vs t)
  : sem2_ctx rs vls1 vls2 -> sem2_ty rs t (sem_tm ts1 vls1 u) (sem_tm ts2 vls2 u).
Proof.
  induction u; cbn; intros; auto.
  - (* TAbs u *)
    auto using param_tabs.

  - (* Abs u *)
    apply IHu; split; auto.

  - (* App u1 u2 *)
    pose proof H as H'.
    apply IHu1 in H.
    apply IHu2 in H'.
    auto.

  - (* Var v *)
    apply param_var; auto.
Qed.

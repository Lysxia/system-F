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

Definition iso_prod {A A' B B'}
  : iso A A' -> iso B B' -> iso (A * B) (A' * B') :=
  fun ia ib =>
    {| iso_from := fun x => (iso_from ia (fst x), iso_from ib (snd x))
     ; iso_to   := fun x => (iso_to ia (fst x), iso_to ib (snd x))
    |}.

Definition iso_sum {A A' B B'}
  : iso A A' -> iso B B' -> iso (A + B) (A' + B') :=
  fun ia ib =>
    {| iso_from := fun x =>
         match x with
         | inl y => inl (iso_from ia y)
         | inr z => inr (iso_from ib z)
         end
     ; iso_to := fun x =>
         match x with
         | inl y => inl (iso_to ia y)
         | inr z => inr (iso_to ib z)
         end
    |}.

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

Definition N0 {n : nat} : tyvar (S n) := None.
Definition NS {n : nat} : tyvar n -> tyvar (S n) := Some.

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

(** ** Bounded lookup *)

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

Fixpoint lookup_list {A : Type} (xs : list A) : tyvar (length xs) -> A :=
  match xs with
  | [] => fun v => match v with end
  | x :: xs => fun v =>
    match v with
    | None => x
    | Some v => lookup_list xs v
    end
  end.

Fixpoint lookup_var {A} {f : A -> Type} {vs : list A}
  : forall v : tyvar (length vs), dvec f vs -> f (lookup_list vs v) :=
  match vs with
  | [] => fun v => match v with end
  | t :: vs => fun v vls =>
    match v with
    | None => fst vls
    | Some v => lookup_var v (snd vls)
    end
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

(** Length-indexed lists as an [Inductive] type *)
Inductive vec' (A : Type) : nat -> Type :=
| nil_vec : vec' A 0
| cons_vec {n} : A -> vec' A n -> vec' A (S n)
.

Arguments nil_vec {A}.
Arguments cons_vec {A n}.

Definition map_vec' {A B : Type} (f : A -> B)
  : forall {n : nat}, vec' A n -> vec' B n :=
  fix _map _ xs :=
    match xs with
    | nil_vec => nil_vec
    | cons_vec x xs => cons_vec (f x) (_map _ xs)
    end.

(** * Polymorphic lambda calculus *)

(** ** Syntax *)

(** *** Types *)

Inductive ty (n : nat) : Type :=
| Arrow : ty n -> ty n -> ty n
| Forall : ty (S n) -> ty n
| Tyvar : tyvar n -> ty n

(* Basic data types *)
| Unit : ty n
| Prod : ty n -> ty n -> ty n
| Sum : ty n -> ty n -> ty n
.

Arguments Arrow  {n}.
Arguments Forall {n}.
Arguments Tyvar  {n}.

Arguments Unit {n}.
Arguments Prod {n}.
Arguments Sum  {n}.

Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

Infix "->" := Arrow : ty_scope.
Coercion Tyvar : tyvar >-> ty.

Definition V0 {n} : tyvar (S n) := N0.
Definition V1 {n} : tyvar (S (S n)) := NS N0.
Definition V2 {n} : tyvar (S (S (S n))) := NS (NS N0).

Fixpoint shift_ty (m : nat) {n : nat} (t : ty n) : ty (S n) :=
  match t with
  | Arrow t1 t2 => Arrow (shift_ty m t1) (shift_ty m t2)
  | Forall t => Forall (shift_ty (S m) t)
  | Tyvar v => @Tyvar (S n) (shift_tyvar m v)
  | Unit => Unit
  | Prod t1 t2 => Prod (shift_ty m t1) (shift_ty m t2)
  | Sum t1 t2 => Sum (shift_ty m t1) (shift_ty m t2)
  end.

(** *** Terms *)

(** Constants *)
Inductive cn {n : nat} : ty n -> Type :=
| One : cn Unit
| Pair : cn (Forall (Forall (V1 -> V0 -> Prod V1 V0)))
| Proj1 : cn (Forall (Forall (Prod V1 V0 -> V1)))
| Proj2 : cn (Forall (Forall (Prod V1 V0 -> V0)))
| Inl : cn (Forall (Forall (V1 -> Sum V1 V0)))
| Inr : cn (Forall (Forall (V0 -> Sum V1 V0)))
| Case : cn (Forall (Forall (Forall (
    (V2 -> V0) ->
    (V1 -> V0) ->
    Sum V2 V1 -> V0))))
.

Arguments One {n}.
Arguments Pair {n}.
Arguments Proj1 {n}.
Arguments Proj2 {n}.
Arguments Inl {n}.
Arguments Inr {n}.
Arguments Case {n}.

Inductive tm (n : nat) (vs : list (ty n)) : ty n -> Type :=
| TAbs {t} : tm (S n) (map (shift_ty 0) vs) t -> tm n vs (Forall t)
| Abs {t1 t2} : tm n (t1 :: vs) t2 -> tm n vs (Arrow t1 t2)
| App {t1 t2} : tm n vs (Arrow t1 t2) -> tm n vs t1 -> tm n vs t2
| Var (v : tyvar (length vs)) : tm n vs (lookup_list vs v)
| Con {t} : cn t -> tm n vs t
.

Arguments TAbs {n vs t}.
Arguments Abs  {n vs t1 t2}.
Arguments App  {n vs t1 t2}.
Arguments Var  {n vs}.
Arguments Con  {n vs t}.

(** ** Semantics *)

(** Semantics of types as Coq types *)
Fixpoint sem_ty {n : nat} (ts : vec Type n) (t : ty n)
  : Type :=
  match t with
  | Arrow t1 t2 => sem_ty ts t1 -> sem_ty ts t2
  | Forall t => forall (t0 : Type), @sem_ty (S n) (t0, ts) t
  | Tyvar tv => lookup_tyvar tv ts
  | Unit => unit
  | Prod t1 t2 => sem_ty ts t1 * sem_ty ts t2
  | Sum t1 t2 => sem_ty ts t1 + sem_ty ts t2
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
  | Unit => iso_id
  | Prod t1 t2 => iso_prod (shift_sem m t0 t1) (shift_sem m t0 t2)
  | Sum t1 t2 => iso_sum (shift_sem m t0 t1) (shift_sem m t0 t2)
  end.

Fixpoint shift_dvec {n : nat} {ts : vec Type n} {vs : list (ty n)} (t0 : Type)
  : dvec (sem_ty ts) vs -> dvec (@sem_ty (S n) (t0, ts)) (map (shift_ty 0) vs) :=
  match vs with
  | [] => fun _ => tt
  | t :: vs => fun ts =>
    (iso_from (shift_sem 0 t0 _) (fst ts), shift_dvec t0 (snd ts))
  end.

Definition sem_cn {n : nat} (ts : vec Type n) {t : ty n} (c : cn t)
  : sem_ty ts t :=
  match c with
  | One => tt
  | Pair => @pair
  | Proj1 => @fst
  | Proj2 => @snd
  | Inl => @inl
  | Inr => @inr
  | Case => fun _ _ _ f g x =>
    match x with
    | inl y => f y
    | inr z => g z
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
  | Var v => lookup_var v vls
  | Con c => sem_cn _ c
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

  | Unit => fun _ _ => True
  | Prod t1 t2 => fun x1 x2 =>
      sem2_ty rs t1 (fst x1) (fst x2) /\
      sem2_ty rs t2 (snd x1) (snd x2)
  | Sum t1 t2 => fun x1 x2 =>
      match x1, x2 with
      | inl y1, inl y2 => sem2_ty rs t1 y1 y2
      | inr z1, inr z2 => sem2_ty rs t2 z1 z2
      | _, _ => False
      end
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
  - split; intros; destruct H; split; apply IHt1 + apply IHt2; auto.
  - split; intros; destruct (_ : _ + _), (_ : _ + _);
      contradiction + apply IHt1 + apply IHt2; auto.
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
  (v : tyvar (length vs))
  : sem2_ctx rs vls1 vls2 ->
    sem2_ty rs (lookup_list vs v) (lookup_var v vls1) (lookup_var v vls2).
Proof.
  induction vs; [ contradiction | ].
  destruct vls1, vls2, v; cbn; intros []; auto.
Qed.

Definition param_cn {n : nat}
  (ts1 ts2 : vec Type n)
  (rs : rvec ts1 ts2)
  (t : ty n)
  (c : cn t)
  : sem2_ty rs t (sem_cn ts1 c) (sem_cn ts2 c).
Proof.
  destruct c; simpl; auto; intros.
  - apply H.
  - apply H.
  - do 2 destruct (_ : _ + _); contradiction + auto.
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

  - (* Con c *)
    apply param_cn.
Qed.

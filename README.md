Parametricity of the polymorphic lambda calculus
================================================

This is a formalization of the polymorphic lambda calculus (System F)
with a proof of Reynolds's parametricity theorem.

The formalization uses a dependently-typed representation,
which ensures that all terms are well-typed by construction.
This enables a natural style of denotational semantics.

## References

- *Types, Abstraction and Parametric Polymorphism*, by John C. Reynolds, IFIP 1983.
- *Theorems for free!*, by Philip Wadler, ICFP 1989.

## Highlights

### Syntax

#### Types

```coq
(**
<<
t ::= t -> t     (* Function *)
    | forall t   (* Type generalization *)
    | i          (* Type variable (DeBruijn index) *)
    | unit       (* Unit type *)
    | t * t      (* Product *)
    | t + t      (* Sum *)
>>
  *)
Inductive ty (n : nat) : Type :=
| Arrow : ty n -> ty n -> ty n
| Forall : ty (S n) -> ty n
| Tyvar : bnat n -> ty n

(* Basic data types *)
| Unit : ty n
| Prod : ty n -> ty n -> ty n
| Sum : ty n -> ty n -> ty n
.
```

#### Terms

```coq
(**
<<
u ::= tyfun u   (* Type abstraction *)
    | fun u     (* Value abstraction *)
    | u u       (* Application *)
    | i         (* Variable *)
    | c         (* Constant *)
>>
  *)
Inductive tm (n : nat) (vs : list (ty n)) : ty n -> Type :=
| TAbs {t}
  : tm (S n) (map (shift_ty 0) vs) t ->
    tm n vs (Forall t)
| Abs {t1 t2}
  : tm n (t1 :: vs) t2 ->
    tm n vs (Arrow t1 t2)
| App {t1 t2}
  : tm n vs (Arrow t1 t2) ->
    tm n vs t1 ->
    tm n vs t2
| Var (v : bnat (length vs))
  : tm n vs (lookup_list vs v)
| Con {t}
  : cn t ->
    tm n vs t
.
```

#### Semantics

Signatures of the denotation functions.
Simplified versions, where `tm0` is `tm` specialized to the empty context
(`n = 0` and `vs = []`).

```coq
(** Semantics of types as Coq types *)
Definition eval_ty0 : ty 0 -> Type.

(** Semantics of terms as Coq values *)
Definition eval_tm0 {t : ty 0} : tm0 t -> eval_ty0 t.

(** Relational semantics of types *)
Definition eval2_ty0 (t : ty 0) : eval_ty0 t -> eval_ty0 t -> Prop.
```

#### Parametricity theorem

```coq
(** For any term [u] of type [t], the interpretation of [u] ([eval_tm0 u])
    satisfies the relational interpretation of [t] ([eval2_ty t]). *)
Theorem parametricity0 (t : ty 0) (u : tm0 t)
  : eval2_ty0 t (eval_tm0 u) (eval_tm0 u).
```

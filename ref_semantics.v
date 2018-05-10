Require Import ref_syntax.
Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list_scope.

Definition State : Type :=  Code * Env.

Inductive step : State -> State -> Prop :=
| skip:
    forall rest env,
      step (Skip :: rest, env) (rest, env)
| assign :
    forall a x v rest env,
      Some v = (evalaexp env a) ->
      step (Assignment x a :: rest, env) (rest, update env x v)
| if_true :
    forall b s1 s2 rest env,
      Some true = (evalbexp env b) ->
      step (IfThenElse b s1 s2 :: rest, env) (s1 ++ rest, env)
| if_false :
    forall b s1 s2 rest env,
      Some false = (evalbexp env b) ->
      step (IfThenElse b s1 s2 :: rest, env) (s2 ++ rest, env)
| while:
    forall (s : list instr) b rest env,
      step (While b s :: rest, env)
           ((IfThenElse b (s ++ While b s :: nil) (Skip :: nil)) :: rest, env).

Inductive steps : State -> State -> Prop :=
| refl : forall S,
    steps S S
| trans: forall S S' S'',
    step S S' -> steps S' S'' -> steps S S''.

Definition n := Id "n".
Definition sum := Id "sum".

Definition SUM := (Assignment n (Int 10) ::
                   Assignment sum (Int 0) ::
                   While (aexpGeq n (Int 1)) (
                     Assignment sum (Plus n sum) ::
                     Assignment n (Plus n (Int (Z.opp 1))) :: nil
                   ) :: nil).

Eval compute in SUM.

Definition A := Assignment n (Int 10) :: nil.


Lemma A_to_nil :
  steps (A,emptyEnv) (nil, update emptyEnv n 10).
Proof.
  apply trans with (S' := (nil, update emptyEnv n 10)).
  - apply assign. simpl. reflexivity.
  - apply refl.
Qed.










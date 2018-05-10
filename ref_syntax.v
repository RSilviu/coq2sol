Require Import ZArith.
Require Import String.


Inductive aexp :=
| Int : Z -> aexp
| Id : string -> aexp
| Plus : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp.

Inductive bexp :=
| boolean : bool -> bexp
| aexpEq : aexp -> aexp -> bexp
| aexpLeq : aexp -> aexp -> bexp
| aexpGeq : aexp -> aexp -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp.

Inductive instr :=
| Assignment : aexp -> aexp -> instr
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr.

Definition Code := list instr.
Definition Env := aexp -> option Z.
Definition emptyEnv : Env := fun x => None.
(* UTILS *)

Definition update (env : Env) (var : aexp) (value : Z) : aexp -> option Z :=
  fun x' => match x', var with 
  | Id x, Id y => if (string_dec x y) then Some value else (env x')
  | _, _ => None
  end.

Fixpoint evalaexp (env : Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | Id x => (env a)
  | Plus a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                  | Some v1, Some v2 => Some (Z.add v1 v2)
                  | _, _ => None
                  end
  | Mul a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                  | Some v1, Some v2 => Some (Z.mul v1 v2)
                  | _, _ => None
                  end
  | Div a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.div v1 v2)
                 | _, _ => None
                 end
  | Rem a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.rem v1 v2)
                 | _, _ => None
                 end
  end.

Fixpoint evalbexp (env : Env) (b : bexp) : option bool :=
  match b with
  | boolean b' => Some b'
  | aexpEq a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | aexpLeq a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | aexpGeq a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Not b' => match (evalbexp env b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (evalbexp env b1), (evalbexp env b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  end.





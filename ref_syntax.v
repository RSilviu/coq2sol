Require Import ZArith.
Require Import String.

Open Scope list_scope.

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
| aexpLt : aexp -> aexp -> bexp
| aexpGt : aexp -> aexp -> bexp
| aexpLeq : aexp -> aexp -> bexp
| aexpGeq : aexp -> aexp -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp.


(******************)
(* Solidity decls *)
(******************)

Inductive var_decl :=
| uint : string -> var_decl.

Definition vars_decl := list var_decl.

Let a : string := "a".

Compute uint a.


Inductive instr :=
| Assignment : aexp -> aexp -> instr
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr
| Return : aexp -> instr.

(************************************)
(* Solidity functions related stuff *)
(************************************)

Inductive fn_visibility :=
| public : fn_visibility
| private : fn_visibility.

Definition param_decl := var_decl.
Definition params_decl := list param_decl.

Inductive fn_return :=
| returns : params_decl -> fn_return.


Definition fn_body := list instr.

Inductive fn_decl :=
| function : string -> params_decl -> option fn_visibility -> fn_return ->
 fn_body -> fn_decl.

Definition fn_decls := list fn_decl.

Let bid : string := "bid".
Definition no_params : params_decl := nil.
Let body : list instr := Skip :: nil.
Let ret_params := returns (uint "a" :: uint "b" :: nil).

Compute ret_params.

Let bid_fn : fn_decl := function bid no_params (Some public) ret_params body.
Compute bid_fn.

(* Contracts *)
(*************)

Inductive contract_body_decl :=
| contract_fn_decl : fn_decl -> contract_body_decl
| contract_var_decl: var_decl -> contract_body_decl.

Definition contract_body_decls := list contract_body_decl.

Inductive sol_contract :=
| contract : string -> contract_body_decls -> sol_contract.

Let contract_body := (contract_fn_decl bid_fn)
 :: (contract_var_decl (uint "address")) :: nil.

Compute contract_body.

Compute contract "Purchase" contract_body.


(*********************************)
(* End of Solidity related stuff *)
(*********************************)

Definition Code := list instr.
Definition Env := string -> option Z. 
Definition emptyEnv : Env := fun x => None.
(* UTILS *)

Definition update (env : Env) (var : aexp) (value : Z) : string -> option Z :=
  fun x =>
  match var with
  | Id s => if (string_dec x s) then Some value else (env x)
  | _ => None
  end.

Fixpoint evalaexp (env : Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | Id x => (env x)
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
  | aexpLt a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | aexpLeq a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | aexpGt a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
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



























Require Import ZArith.
Require Import String.

Require Import List.

(* consistency in types: w/o option *)

Inductive aexp :=
| Int : Z -> aexp
| AId : string -> aexp
| Plus : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp.

Check aexp.

Inductive bexp :=
| Boolean : bool -> bexp
| BId : string -> bexp
| Aexp_Lt : aexp -> aexp -> bexp
| Aexp_Leq : aexp -> aexp -> bexp
| Aexp_Eq : aexp -> aexp -> bexp
| Aexp_Geq : aexp -> aexp -> bexp
| Aexp_Gt : aexp -> aexp -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp.


Definition Default_Aexp := Int 0.
Definition Default_Bexp := Boolean false.

(** ADDRESS *)
Definition address := nat.
Definition address_payable := nat.

Inductive instr :=
| Assignment_Aexp : string -> aexp -> instr
| Assignment_Bexp : string -> bexp -> instr
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr
(* to be continued *)
| Function_Call : address -> string -> Z -> instr (* determine calling contract *) (* add args & return *) (* support message calls *)
| Transfer : address_payable -> Z -> instr
(* | Balance : address -> instr *).


(* Notation "id ()" := (Function_Call id) (at level 50).

Let fn := "pay"%string.

Check fn ().
 *)
Inductive err :=
| VarError.

(* Record function :=
mkFunction{
 name : string;
 body : list instr
}. *)

Inductive function_body :=
| Body : list instr -> function_body
| EmptyBody : function_body.

Definition Code := list instr.

(* Definition Env := string ->  option Z. *)
Definition Env (T : Type) := string -> option T.

Definition Aexp_Env := Env Z.
Definition Empty_Aexp_Env : Aexp_Env := fun x => None.

Definition Bexp_Env := Env bool.
Definition Empty_Bexp_Env : Bexp_Env := fun x => None.

Definition Functions_Env := Env function_body.
Definition Empty_Functions_Env : Functions_Env := fun x => None.

Definition BalanceMap := address -> Z.
Definition Empty_BalanceMap : BalanceMap := fun a => 0%Z.

Definition updateBalance (map : BalanceMap) (addr : address) (amount : Z) : address -> Z :=
fun a' => if beq_nat addr a' then amount else map a'.



Record msg :=
mkMsg {
value : Z;
sender : address_payable
}.

Definition Default_Msg := {| value := 0%Z;
                             sender := 0 |}.

(* contract fn env, contract state *)

Record FunctionEnv :=
mkEnv {
(*  names : list string; *)
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 next_code : Code;
 balance_map : BalanceMap;
 msg_data : msg
}.

Definition replace_aexp_env := 
fun (fenv : FunctionEnv) (new_env : Aexp_Env) => mkEnv new_env (bexp_env fenv) (next_code fenv) (balance_map fenv) (msg_data fenv).

Definition replace_bexp_env := 
fun (fenv : FunctionEnv) (new_env : Bexp_Env) => mkEnv (aexp_env fenv) new_env (next_code fenv) (balance_map fenv) (msg_data fenv).

Definition replace_next_code := 
fun (fenv : FunctionEnv) (new_next_code : Code) => mkEnv (aexp_env fenv) (bexp_env fenv) new_next_code (balance_map fenv) (msg_data fenv).

Definition replace_bmap := 
fun (fenv : FunctionEnv) (bmap : BalanceMap) => mkEnv (aexp_env fenv) (bexp_env fenv) (next_code fenv) bmap (msg_data fenv).

Definition replace_msg_data := 
fun (fenv : FunctionEnv) (new_msg : msg) => mkEnv (aexp_env fenv) (bexp_env fenv) (next_code fenv) (balance_map fenv) new_msg.


Record ContractState :=
mkContractState {
 c_address : address;
 constructed : bool;
 fn_env : Functions_Env;
 aexp_vars : Aexp_Env;
 bexp_vars : Bexp_Env
}.

Definition Default_ContractState := {| c_address := 0;
                                       constructed := true;
                                       fn_env := Empty_Functions_Env;
                                       aexp_vars := Empty_Aexp_Env;
                                       bexp_vars := Empty_Bexp_Env |}.


Definition Empty_FunctionEnv := {| aexp_env := Empty_Aexp_Env;
                                bexp_env := Empty_Bexp_Env;
                                next_code := nil;
                                balance_map := Empty_BalanceMap;
                                msg_data := Default_Msg |}.

Definition defineFunction (env : Functions_Env) (name : string) (body : function_body) : Functions_Env :=
  fun x => if (string_dec x name) then Some body
  else (env x).


Definition getFunctionCode (opt_body : option function_body) : Code :=
  match opt_body with
  | Some (Body code) => code
  | _ => nil
  end.

(* Let body := Body (Skip :: nil).
Let emptyBody := EmptyBody.
Let emptyFnEnv : Functions_Env := fun f => None.
Let fn_name : string := "foo".

Let fun_env := defineFunction emptyFnEnv fn_name emptyBody.

Compute getFunctionCode (fun_env "foo"%string). *)


(* UTILS *)
Definition declareAexp (ident : string) : Aexp_Env :=
  fun x => if (string_dec x ident) then Some 0%Z
           else None.

Definition updateAexp (env : Aexp_Env) (var : string) (val : Z) : Aexp_Env :=
  fun x => if (string_dec x var) then Some val
  else (env x).


Fixpoint evalaexp (env : Aexp_Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | AId x => env x
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


Definition declareBexp (ident : string) : Bexp_Env :=
  fun x => if (string_dec x ident) then Some false
           else None.

Definition updateBexp (env : Bexp_Env) (var : string) (val : bool) : Bexp_Env :=
  fun x => if (string_dec x var) then Some val
  else (env x).

Fixpoint evalbexp (aexp_env : Aexp_Env) (bexp_env : Bexp_Env) (b : bexp) : option bool :=
  match b with
  | Boolean b' => Some b'
  | BId x => bexp_env x
  | Aexp_Lt a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Leq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Eq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Geq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Aexp_Gt a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
                    | _, _ => None
                    end
  | Not b' => match (evalbexp aexp_env bexp_env b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (evalbexp aexp_env bexp_env b1), (evalbexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  | Or b1 b2 => match (evalbexp aexp_env bexp_env b1), (evalbexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (orb b1' b2')
                 | _, _ => None
                 end
  end.


(* Let n := AId "n".
Let x := AId "x".

Let x_decl := declareAexp "x" emptyEnv.

Compute evalaexp x_decl x.

Let vars := updateAexp x_decl "n" 10.

Compute evalaexp vars n.
Compute evalaexp vars x.

Let new_vars := updateAexp vars "x" 1.

Compute evalaexp new_vars x.

Compute evalaexp vars n. *)

(* Inductive DataType :=
| int : DataType
| bool : DataType. *)

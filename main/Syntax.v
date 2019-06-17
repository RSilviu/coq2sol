Require Export ZArith.
Require Export String.
Require Export List.

Open Scope string_scope.
Open Scope Z_scope.

Import ListNotations.

(**************************************************************)
(** Solidity address *)

Definition address := string.
Definition address_payable := address.

Definition Default_Address := "0x0".

(*
 *
TODO Consider better separation for address i.e.:

Inductive address :=
| AddrId : string -> address
| Address : string -> address
| Address_Payable : string -> address
| Msg_Sender -> address
.

Definition get_contract_by_id (mapping : id_state_mapping) (c_id : string) : ContractState := id_state_mapping c_id.

Definition contract_id_2_addr (c_id : string) : address := c_address (get_contract_by_id c_id).

*)


(**************************************************************)
(** Integers *)
 
Inductive aexp :=
| Int : Z -> aexp
| AId : string -> aexp
| Plus : aexp -> aexp -> aexp
| Sub : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp
| BalanceOf : address -> aexp
| Msg_Value : aexp.

Definition Default_Aexp := Int 0.


(**************************************************************)
(** Bool *)

Inductive bexp :=
| Boolean : bool -> bexp
| BId : string -> bexp
| Aexp_Lt : aexp -> aexp -> bexp
| Aexp_Leq : aexp -> aexp -> bexp
| Aexp_Eq : aexp -> aexp -> bexp
| Aexp_Neq : aexp -> aexp -> bexp
| Aexp_Geq : aexp -> aexp -> bexp
| Aexp_Gt : aexp -> aexp -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp.

Definition Default_Bexp := Boolean false.


(** Message *)

Record msg :=
mkMsg {
value : Z;
sender : address_payable
}.

Definition Default_Msg_Value := 0.

Definition Default_Msg := {| value := Default_Msg_Value;
                             sender := Default_Address |}.


(**************************************************************)
(** Statements *)

Inductive instr :=
| Declare_Aexp : string -> instr
| Declare_Bexp : string -> instr

| Define_Aexp : (string * aexp) -> instr
| Define_Bexp : (string * bexp) -> instr

| Assign_Aexp : aexp -> aexp -> instr
| Assign_Bexp : bexp -> bexp -> instr

| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr

(* no params, no return value, with value setter *)
(* example: "this" "f" Some Int value *)
| Function_Call : option address -> string -> option aexp -> instr 
| Transfer : address_payable -> aexp -> instr (* | Transfer : address -> aexp -> instr *)

| Revert : option string -> instr
| Require : bexp -> option string -> instr.


Inductive contract_part :=
| Define_Function : string -> list instr -> contract_part

| Declare_Aexp_Field : string -> contract_part
| Declare_Bexp_Field : string -> contract_part

| Define_Aexp_Field : (string * aexp) -> contract_part
| Define_Bexp_Field : (string * bexp) -> contract_part.


Definition contract_parts := list contract_part.


(**************************************************************)
(** * Environments *)

Definition Env T1 T2 := T1 -> option T2.


(** aexp *)

Definition Aexp_Vars := Env string Z.

(* Record aexp_env :=
mk_aexp_env {
aexp_vars : Aexp_Env;

}. *)

Definition Empty_Aexp_Vars : Aexp_Vars := fun x => None.

Definition update_aexp_vars (env : Aexp_Vars) (var : option string) (val : Z) : Aexp_Vars :=
  fun x => match var with
  | Some str => if (string_dec x str) then Some val
                else (env x)
  | _ => None
  end.


(** bexp *)

Definition Bexp_Vars := Env string bool.
Definition Empty_Bexp_Vars : Bexp_Vars := fun x => None.

Definition update_bexp_vars (env : Bexp_Vars) (var : option string) (val : bool) : Bexp_Vars :=
  fun x => match var with
  | Some str => if (string_dec x str) then Some val
                else (env x)
  | _ => None
  end.


(** contract functions *)

Definition Code := list instr.

Inductive function_body :=
| Body : Code -> function_body
| EmptyBody : function_body.

Definition Functions := Env string function_body.
Definition Empty_Functions : Functions := fun x => None.

Definition define_function (env : Functions) (name : string) (body : function_body) : Functions :=
  fun x => if (string_dec x name) then Some body
  else (env x).

Definition get_function_code (opt_body : option function_body) : Code :=
  match opt_body with
  | Some (Body code) => code
  | _ => nil
  end.


(** balances *)

Definition Balances := Env address Z.
Definition Empty_Balances : Balances := fun a => None.
Definition Default_Balance := 0.

Definition update_balance (map : Balances) (addr : address) (amount : Z) : Balances :=
fun a' => if string_dec addr a' then Some amount else map a'.


(** function locals *)

Record FunctionState :=
mkFunctionState {
 aexp_locals : Aexp_Vars;
 bexp_locals : Bexp_Vars;
 next_code : Code;
 msg_data : msg
}.

Definition Empty_FunctionState := {| aexp_locals := Empty_Aexp_Vars;
                                bexp_locals := Empty_Bexp_Vars;
                                next_code := [];
                                msg_data := Default_Msg |}.

Definition update_function_aexp_locals := 
fun (fstate : FunctionState) (new_env : Aexp_Vars) => mkFunctionState new_env (bexp_locals fstate) (next_code fstate) (msg_data fstate).

Definition update_function_bexp_locals := 
fun (fstate : FunctionState) (new_env : Bexp_Vars) => mkFunctionState (aexp_locals fstate) new_env (next_code fstate) (msg_data fstate).

Definition update_function_next_code := 
fun (fstate : FunctionState) (new_next_code : Code) => mkFunctionState (aexp_locals fstate) (bexp_locals fstate) new_next_code (msg_data fstate).

Definition update_function_msg_data := 
fun (fstate : FunctionState) (new_msg : msg) => mkFunctionState (aexp_locals fstate) (bexp_locals fstate) (next_code fstate) new_msg.


(** Contract state *)

(**
  * Introducing contract type.
  
 Definition Contract_Vars := string -> ContractState.

Definition Empty_Contract_Vars : Contract_Vars := fun x => Default_ContractState.

Definition updateContract_Vars (env : Contract_Vars) (name : string) (state : ContractState) : Contract_Vars :=
  fun x => if (string_dec x name) then state
  else (env x).

Inductive Contract_Vars := 
| contract_vars : string -> ContractState -> 
with ContractState :=
| ctor (c_address : address) (fn_env : Functions_Env)
       (aexp_vars : Aexp_Env) (bexp_vars : Bexp_Env) (contract_vars : Contract_Vars)
.
 *)

Record ContractState :=
mkContractState {
 c_address : address;
 functions : Functions;
 aexp_fields : Aexp_Vars;
 bexp_fields : Bexp_Vars
(*  contract_vars : Contract_Vars *)
}.


Definition update_contract_aexp_vars := 
fun (cstate : ContractState) (new_env : Aexp_Vars)
 => mkContractState (c_address cstate) (functions cstate) new_env (bexp_fields cstate).

Definition update_contract_bexp_vars := 
fun (cstate : ContractState) (new_env : Bexp_Vars)
 => mkContractState (c_address cstate) (functions cstate) (aexp_fields cstate) new_env.

Definition update_contract_functions := 
fun (cstate : ContractState) (new_env : Functions)
 => mkContractState (c_address cstate) new_env (aexp_fields cstate) (bexp_fields cstate).


Definition Default_ContractState := {| c_address := Default_Address;
                                       functions := Empty_Functions;
                                       aexp_fields := Empty_Aexp_Vars;
                                       bexp_fields := Empty_Bexp_Vars |}.


(**************************************************************)
(** Contracts Env *)

Definition Address2ContractState := address -> ContractState.
Definition Empty_Address2ContractState : Address2ContractState := fun x => Default_ContractState.


Definition get_calling_contract (opt_addr : option address) (env : Address2ContractState) (current_contract : ContractState) :=
match opt_addr with
| Some v => env v
| _ => current_contract
end.


Definition update_contract_state  (env : Address2ContractState) (addr : address) (state : ContractState) : Address2ContractState :=
  fun x => if (string_dec x addr) then state
           else (env x).


(**************************************************************)
(** More unfold/unpack helpers *)

(* * More generic *)
(* 
Definition unfold_option {T1} {T2} (opt : option T1) (default : T2) (t1_to_t2 : T1 -> T2) : T2 :=
match opt with
| Some t1 => t1_to_t2 t1
| _ => default
end.
*)


Definition unfold_option {T} (opt : option T) (default : T) : T :=
match opt with
| Some v => v
| _ => default
end.

Definition unfold_option_z := fun opt => unfold_option opt 0.
Definition unfold_option_bool := fun opt => unfold_option opt false.


Definition unfold_aexp_literal (e : aexp) : option Z :=
match e with
| Int v => Some v
| _ => None
end.

Definition unfold_bexp_literal (e : bexp) : option bool :=
match e with
| Boolean v => Some v
| _ => None
end.

Definition unfold_aexp_id (e : aexp) : option string :=
match e with
| AId s => Some s
| _ => None
end.

Definition unfold_bexp_id (e : bexp) : option string :=
match e with
| BId s => Some s
| _ => None
end.


(**************************************************************)
(** Declaration helpers *)

Definition declare_aexp (env : Aexp_Vars) (name : string) : Aexp_Vars :=
fun x => if (string_dec x name) then unfold_aexp_literal Default_Aexp
         else env x.

(** [TEST] declareAexp *)

Let env := update_aexp_vars Empty_Aexp_Vars (Some "x") 1.
Compute (declare_aexp env "y") "x".

(***************************)

Definition define_aexp (env : Aexp_Vars) (def : string * aexp) : Aexp_Vars :=
fun x => match def with
| (id, Int v) => if (string_dec x id) then Some v
                 else env x
| (_, _) => env x
end.

(** [TEST] defineAexp *)

Let env1 := update_aexp_vars Empty_Aexp_Vars (Some "x") 1.
Compute (define_aexp env1 ("z", Int 33)) "z".
Compute (define_aexp env1 ("z", AId "x")) "z".

(***************************)


Definition declare_bexp (env : Bexp_Vars) (name : string) : Bexp_Vars :=
fun x => if (string_dec x name) then unfold_bexp_literal Default_Bexp
         else env x.

Definition define_bexp (env : Bexp_Vars) (def : string * bexp) : Bexp_Vars :=
fun x => match def with
| (id, Boolean v) => if (string_dec x id) then Some v
                 else env x
| (_, _) => env x
end.


(**************************************************************)
(** * Evaluation of expressions *)

(** aexp *)

Definition Msg_Sender := "".

Record aexp_eval_context :=
mk_aexp_eval_context {
vars : Aexp_Vars;
balances : Balances;
msg_value : Z
}.

Definition get_aexp_eval_context (fstate : FunctionState) (bm : Balances) := 
mk_aexp_eval_context (aexp_locals fstate) bm (value (msg_data fstate)).


Fixpoint eval_aexp (context : aexp_eval_context) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | AId x => (vars context) x
  
  | BalanceOf x => (balances context) x
  | Msg_Value => Some (msg_value context)
  
  | Plus a1 a2 => match (eval_aexp context a1), (eval_aexp context a2) with
                  | Some v1, Some v2 => Some (Z.add v1 v2)
                  | _, _ => None
                  end
  | Sub a1 a2 => match (eval_aexp context a1), (eval_aexp context a2) with
                  | Some v1, Some v2 => Some (Z.sub v1 v2)
                  | _, _ => None
                  end
  | Mul a1 a2 => match (eval_aexp context a1), (eval_aexp context a2) with
                  | Some v1, Some v2 => Some (Z.mul v1 v2)
                  | _, _ => None
                  end
  | Div a1 a2 => match (eval_aexp context a1), (eval_aexp context a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.div v1 v2)
                 | _, _ => None
                 end
  | Rem a1 a2 => match (eval_aexp context a1), (eval_aexp context a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.rem v1 v2)
                 | _, _ => None
                 end
  end.


Definition unfold_opt_aexp (opt_aexp : option aexp) (context : aexp_eval_context) : option Z :=
match opt_aexp with
| Some v => eval_aexp context v
| _ => None
end.


(** * Some proof examples *)

(* Example mixed_aexp_ops:
  eval_aexp Empty_Aexp_Env Empty_BalanceEnv (Plus (Int 1) (Div (Int 4) (Int 2))) = Some 3.
Proof.
  reflexivity.
Qed.

Example unknown_id_evals_none:
  eval_aexp Empty_Aexp_Env Empty_BalanceEnv (AId "a") = None.
Proof.
  reflexivity.
Qed.

Example zero_division:
  eval_aexp Empty_Aexp_Env Empty_BalanceEnv (Div (Int 1) (Int 0)) = None.
Proof.
  reflexivity.
Qed.

Example zero_division_remainder:
  eval_aexp Empty_Aexp_Env Empty_BalanceEnv (Rem (Int 1) (Int 0)) = None.
Proof.
  reflexivity.
Qed. *)


(** bexp *)

Fixpoint eval_bexp (aexp_context : aexp_eval_context) (bexp_context : Bexp_Vars) (b : bexp) : option bool :=
  match b with
  | Boolean b' => Some b'
  | BId x => bexp_context x
  | Aexp_Lt a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Leq a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Eq a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Neq a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Zneq_bool v1 v2)
                    | _, _ => None
                    end
  | Aexp_Geq a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Aexp_Gt a1 a2 => match (eval_aexp aexp_context a1), (eval_aexp aexp_context a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
                    | _, _ => None
                    end
  | Not b' => match (eval_bexp aexp_context bexp_context b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (eval_bexp aexp_context bexp_context b1), (eval_bexp aexp_context bexp_context b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  | Or b1 b2 => match (eval_bexp aexp_context bexp_context b1), (eval_bexp aexp_context bexp_context b2) with
                 | Some b1', Some b2' => Some (orb b1' b2')
                 | _, _ => None
                 end
  end.






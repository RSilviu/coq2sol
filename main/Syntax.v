Require Import ZArith.
Require Import List.

Require Import String.

Open Scope string_scope.

(* TODO use modules, for balance, envs, etc *)


(** Basic types *)

Inductive aexp :=
| Int : Z -> aexp
| AId : string -> aexp
| Plus : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp.

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


(** Solidity address *)

Definition address := string.
Definition address_payable := string.


(** Statements *)

Inductive instr :=
| Declare_Aexp : list (string * option aexp) -> instr
| Assignment_Aexp : aexp -> aexp -> instr
| Assignment_Bexp : string -> bexp -> instr (* TODO: replace string with bexp *)
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr
(* no params, no return value, with value setter *)
| Function_Call : option address -> string -> option aexp -> instr (* "this" "f" Some Int value *)
| Transfer : address_payable -> aexp -> instr.


Inductive function_body :=
| Body : list instr -> function_body
| EmptyBody : function_body.

Definition Code := list instr.


(** Environment *)

Definition Env (T : Type) := string -> option T.

Definition Aexp_Env := Env Z.
Definition Empty_Aexp_Env : Aexp_Env := fun x => None.

Definition Bexp_Env := Env bool.
Definition Empty_Bexp_Env : Bexp_Env := fun x => None.

Definition Functions_Env := Env function_body.
Definition Empty_Functions_Env : Functions_Env := fun x => None.


(** Contract balances *)

Definition BalanceMap := address -> Z.
Definition Empty_BalanceMap : BalanceMap := fun a => 0%Z.

Definition updateBalance (map : BalanceMap) (addr : address) (amount : Z) : address -> Z :=
fun a' => if string_dec addr a' then amount else map a'.



(** Message structure *)

Record msg :=
mkMsg {
value : Z;
sender : address_payable
}.

Definition Default_Msg := {| value := 0%Z;
                             sender := "default_sender" |}.


(** Function scope *)

Record FunctionEnv :=
mkEnv {
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


(** Contract scope *)

Record ContractState :=
mkContractState {
 c_address : address;
 fn_env : Functions_Env;
 aexp_vars : Aexp_Env;
 bexp_vars : Bexp_Env
}.

Definition replace_contract_aexp_env := 
fun (cstate : ContractState) (new_env : Aexp_Env)
 => mkContractState (c_address cstate) (fn_env cstate) new_env (bexp_vars cstate).


Definition Default_Address := "default_address".

Definition Default_ContractState := {| c_address := Default_Address;
                                       fn_env := Empty_Functions_Env;
                                       aexp_vars := Empty_Aexp_Env;
                                       bexp_vars := Empty_Bexp_Env |}.

Definition Empty_FunctionEnv := {| aexp_env := Empty_Aexp_Env;
                                bexp_env := Empty_Bexp_Env;
                                next_code := nil;
                                balance_map := Empty_BalanceMap;
                                msg_data := Default_Msg |}.


(** Environment utils *)

Definition defineFunction (env : Functions_Env) (name : string) (body : function_body) : Functions_Env :=
  fun x => if (string_dec x name) then Some body
  else (env x).

Definition getFunctionCode (opt_body : option function_body) : Code :=
  match opt_body with
  | Some (Body code) => code
  | _ => nil
  end.


Definition ContractsEnv := address -> ContractState.
Definition Empty_ContractsEnv : ContractsEnv := fun x => Default_ContractState.
Definition updateContractsEnv (env : ContractsEnv) (addr : address) (state : ContractState) : ContractsEnv :=
  fun x => if (string_dec x addr) then state
  else (env x).

Definition unfold_aexp_literal (e : aexp) : option Z :=
match e with
| Int z => Some z
| _ => None
end.

Check unfold_aexp_literal.

Fixpoint declareAexpList (env : Aexp_Env) (decl_pairs : list (string * option aexp)) : Aexp_Env :=
fun x => match decl_pairs with
| nil => env x
| decl :: rest => if (string_dec x (fst decl)) then 
                      match (snd decl) with
                      | None => unfold_aexp_literal Default_Aexp
                      | Some v => unfold_aexp_literal v
                      end
                  else declareAexpList env rest x
end.

Definition update_aexp (env : Aexp_Env) (var : option string) (val : Z) : Aexp_Env :=
  fun x => match var with
  | Some str => if (string_dec x str) then Some val
                else (env x)
  | _ => None
  end.

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


Definition unfold_aexp_id (e : aexp) : option string :=
match e with
| AId s => Some s
| _ => None
end.


Definition unfold_option_z := fun opt => unfold_option opt 0%Z.
Definition unfold_option_bool := fun opt => unfold_option opt false.

Fixpoint eval_aexp (env : Aexp_Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | AId x => env x
  | Plus a1 a2 => match (eval_aexp env a1), (eval_aexp env a2) with
                  | Some v1, Some v2 => Some (Z.add v1 v2)
                  | _, _ => None
                  end
  | Mul a1 a2 => match (eval_aexp env a1), (eval_aexp env a2) with
                  | Some v1, Some v2 => Some (Z.mul v1 v2)
                  | _, _ => None
                  end
  | Div a1 a2 => match (eval_aexp env a1), (eval_aexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.div v1 v2)
                 | _, _ => None
                 end
  | Rem a1 a2 => match (eval_aexp env a1), (eval_aexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.rem v1 v2)
                 | _, _ => None
                 end
  end.


Definition unfold_opt_aexp (opt_aexp : option aexp) (env : Aexp_Env) : option Z :=
match opt_aexp with
| Some v => eval_aexp env v
| _ => None
end.


Example unknown_id_evals_none:
  eval_aexp Empty_Aexp_Env (AId "a") = None.
Proof.
  reflexivity.
Qed.

Example zero_division:
  eval_aexp Empty_Aexp_Env (Div (Int 1) (Int 0)) = None.
Proof.
  reflexivity.
Qed.

Example zero_division_remainder:
  eval_aexp Empty_Aexp_Env (Rem (Int 1) (Int 0)) = None.
Proof.
  reflexivity.
Qed.

Definition declare_bexp (ident : string) : Bexp_Env :=
  fun x => if (string_dec x ident) then Some false
           else None.

Definition update_bexp (env : Bexp_Env) (var : string) (val : bool) : Bexp_Env :=
  fun x => if (string_dec x var) then Some val
  else (env x).

Fixpoint eval_bexp (aexp_env : Aexp_Env) (bexp_env : Bexp_Env) (b : bexp) : option bool :=
  match b with
  | Boolean b' => Some b'
  | BId x => bexp_env x
  | Aexp_Lt a1 a2 => match (eval_aexp aexp_env a1), (eval_aexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Leq a1 a2 => match (eval_aexp aexp_env a1), (eval_aexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Eq a1 a2 => match (eval_aexp aexp_env a1), (eval_aexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Geq a1 a2 => match (eval_aexp aexp_env a1), (eval_aexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Aexp_Gt a1 a2 => match (eval_aexp aexp_env a1), (eval_aexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
                    | _, _ => None
                    end
  | Not b' => match (eval_bexp aexp_env bexp_env b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (eval_bexp aexp_env bexp_env b1), (eval_bexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  | Or b1 b2 => match (eval_bexp aexp_env bexp_env b1), (eval_bexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (orb b1' b2')
                 | _, _ => None
                 end
  end.


Definition get_calling_contract (opt_addr : option address) (env : ContractsEnv) (current_contract : ContractState) :=
match opt_addr with
| Some v => env v
| _ => current_contract
end.












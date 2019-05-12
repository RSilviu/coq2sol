Require Export ZArith.
Require Export String.
Require Export List.

Open Scope string_scope.
Open Scope Z_scope.


(**************************************************************)
(** Solidity address *)

Definition address := string.
Definition address_payable := address.

Definition Default_Address := "default_address".

(*
 *
 TODO Consider better separation for address i.e.:
Inductive address :=
| Address : string -> address
| Address_Payable : string -> address
.
*)


(**************************************************************)
(** Integers *)
 
Inductive aexp :=
| Int : Z -> aexp
| AId : string -> aexp
| Plus : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp
| BalanceOf : address -> aexp.

Definition Default_Aexp := Int 0.


(**************************************************************)
(** Bool *)

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

Definition Default_Bexp := Boolean false.


(** Message *)

Record msg :=
mkMsg {
value : Z;
sender : address_payable
}.

Definition Default_Msg := {| value := 0;
                             sender := Default_Address |}.


(**************************************************************)
(** Statements *)

Inductive instr :=
| Declare_Aexp : list (string * option aexp) -> instr
| Declare_Bexp : list (string * option bexp) -> instr
| Assignment_Aexp : aexp -> aexp -> instr
| Assignment_Bexp : bexp -> bexp -> instr
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr
(* no params, no return value, with value setter *)
| Function_Call : option address -> string -> option aexp -> instr (* "this" "f" Some Int value *)
| Transfer : address_payable -> aexp -> instr.


(**************************************************************)
(** * Environments *)

Definition Env T1 T2 := T1 -> option T2.


(** aexp *)

Definition Aexp_Env := Env string Z.
Definition Empty_Aexp_Env : Aexp_Env := fun x => None.

Definition update_aexp (env : Aexp_Env) (var : option string) (val : Z) : Aexp_Env :=
  fun x => match var with
  | Some str => if (string_dec x str) then Some val
                else (env x)
  | _ => None
  end.


(** bexp *)

Definition Bexp_Env := Env string bool.
Definition Empty_Bexp_Env : Bexp_Env := fun x => None.

Definition update_bexp (env : Bexp_Env) (var : option string) (val : bool) : Bexp_Env :=
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

Definition Functions_Env := Env string function_body.
Definition Empty_Functions_Env : Functions_Env := fun x => None.

Definition defineFunction (env : Functions_Env) (name : string) (body : function_body) : Functions_Env :=
  fun x => if (string_dec x name) then Some body
  else (env x).

Definition getFunctionCode (opt_body : option function_body) : Code :=
  match opt_body with
  | Some (Body code) => code
  | _ => nil
  end.


(** balances *)

Definition Balance_Env := Env address Z.
Definition Empty_BalanceEnv : Balance_Env := fun a => None.

Definition updateBalance (map : Balance_Env) (addr : address) (amount : Z) : Balance_Env :=
fun a' => if string_dec addr a' then Some amount else map a'.


(** function locals *)

Record FunctionEnv :=
mkEnv {
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 next_code : Code;
 msg_data : msg
}.

Definition Empty_FunctionEnv := {| aexp_env := Empty_Aexp_Env;
                                bexp_env := Empty_Bexp_Env;
                                next_code := nil;
                                msg_data := Default_Msg |}.

Definition replace_aexp_env := 
fun (fenv : FunctionEnv) (new_env : Aexp_Env) => mkEnv new_env (bexp_env fenv) (next_code fenv) (msg_data fenv).

Definition replace_bexp_env := 
fun (fenv : FunctionEnv) (new_env : Bexp_Env) => mkEnv (aexp_env fenv) new_env (next_code fenv) (msg_data fenv).

Definition replace_next_code := 
fun (fenv : FunctionEnv) (new_next_code : Code) => mkEnv (aexp_env fenv) (bexp_env fenv) new_next_code (msg_data fenv).

Definition replace_msg_data := 
fun (fenv : FunctionEnv) (new_msg : msg) => mkEnv (aexp_env fenv) (bexp_env fenv) (next_code fenv) new_msg.


(** Contract state *)

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

Definition replace_contract_bexp_env := 
fun (cstate : ContractState) (new_env : Bexp_Env)
 => mkContractState (c_address cstate) (fn_env cstate) (aexp_vars cstate) new_env.

Definition Default_ContractState := {| c_address := Default_Address;
                                       fn_env := Empty_Functions_Env;
                                       aexp_vars := Empty_Aexp_Env;
                                       bexp_vars := Empty_Bexp_Env |}.


(**************************************************************)
(** Contracts Env *)

Definition ContractsEnv := address -> ContractState.
Definition Empty_ContractsEnv : ContractsEnv := fun x => Default_ContractState.

Definition updateContractsEnv (env : ContractsEnv) (addr : address) (state : ContractState) : ContractsEnv :=
  fun x => if (string_dec x addr) then state
  else (env x).

Definition get_calling_contract (opt_addr : option address) (env : ContractsEnv) (current_contract : ContractState) :=
match opt_addr with
| Some v => env v
| _ => current_contract
end.


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

Fixpoint declareBexpList (env : Bexp_Env) (decl_pairs : list (string * option bexp)) : Bexp_Env :=
fun x => match decl_pairs with
| nil => env x
| decl :: rest => if (string_dec x (fst decl)) then 
                      match (snd decl) with
                      | None => unfold_bexp_literal Default_Bexp
                      | Some v => unfold_bexp_literal v
                      end
                  else declareBexpList env rest x
end.


(**************************************************************)
(** * Evaluation of expressions *)

(** aexp *)

Fixpoint eval_aexp (env : Aexp_Env) (bm : Balance_Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | AId x => env x
  | BalanceOf x => bm x
  | Plus a1 a2 => match (eval_aexp env bm a1), (eval_aexp env bm a2) with
                  | Some v1, Some v2 => Some (Z.add v1 v2)
                  | _, _ => None
                  end
  | Mul a1 a2 => match (eval_aexp env bm a1), (eval_aexp env bm a2) with
                  | Some v1, Some v2 => Some (Z.mul v1 v2)
                  | _, _ => None
                  end
  | Div a1 a2 => match (eval_aexp env bm a1), (eval_aexp env bm a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.div v1 v2)
                 | _, _ => None
                 end
  | Rem a1 a2 => match (eval_aexp env bm a1), (eval_aexp env bm a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.rem v1 v2)
                 | _, _ => None
                 end
  end.


Definition unfold_opt_aexp (opt_aexp : option aexp) (env : Aexp_Env) (bm : Balance_Env) : option Z :=
match opt_aexp with
| Some v => eval_aexp env bm v
| _ => None
end.


(** * Some proof examples *)

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
Qed.


(** bexp *)

Fixpoint eval_bexp (aexp_env : Aexp_Env) (bm : Balance_Env) (bexp_env : Bexp_Env) (b : bexp) : option bool :=
  match b with
  | Boolean b' => Some b'
  | BId x => bexp_env x
  | Aexp_Lt a1 a2 => match (eval_aexp aexp_env bm a1), (eval_aexp aexp_env bm a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Leq a1 a2 => match (eval_aexp aexp_env bm a1), (eval_aexp aexp_env bm a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Eq a1 a2 => match (eval_aexp aexp_env bm a1), (eval_aexp aexp_env bm a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Geq a1 a2 => match (eval_aexp aexp_env bm a1), (eval_aexp aexp_env bm a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Aexp_Gt a1 a2 => match (eval_aexp aexp_env bm a1), (eval_aexp aexp_env bm a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
                    | _, _ => None
                    end
  | Not b' => match (eval_bexp aexp_env bm bexp_env b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (eval_bexp aexp_env bm bexp_env b1), (eval_bexp aexp_env bm bexp_env b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  | Or b1 b2 => match (eval_bexp aexp_env bm bexp_env b1), (eval_bexp aexp_env bm bexp_env b2) with
                 | Some b1', Some b2' => Some (orb b1' b2')
                 | _, _ => None
                 end
  end.






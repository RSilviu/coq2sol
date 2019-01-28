Require Import ZArith.
Require Import String.
Require Import List.

Require Import main.Syntax.
Require Import SolEnv.

Open Scope list_scope.


(* Definition EnvStack := list AlphaEnv. *)
Definition EnvStack := list (FunctionEnv * ContractState).
(* Definition State : Type :=  Code * AlphaEnv * EnvStack. *)
Definition ExecutionState : Type :=  Code * FunctionEnv * EnvStack * ContractState.

(* ecord AlphaEnv :=
{
(*  names : list string; *)
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 fn_env : Functions_Env
}.*)

Definition unfoldOptionZ (opt_z : option Z) :=
match opt_z with
| Some v => v
| _ => 0%Z
end.

Definition unfoldOptionBool (opt_bool : option bool) :=
match opt_bool with
| Some v => v
| _ => false
end.

(* Definition BalanceMap := address -> Z

Definition updateBalance (map : BalanceMap) (addr : address) (amount : Z) : address -> Z :=
fun a' => if addr = a' then amount else map a'.
 *)

(* Record FunctionEnv :=
mkEnv {
(*  names : list string; *)
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 fn_env : Functions_Env;
 next_code : Code;
 balance_map : BalanceMap;
 msg_data : msg
}.

Record ContractState :=
mkContractState {
 c_address : address;
 constructed : bool;
 aexp_vars : Aexp_Env;
 bexp_vars : Bexp_Env
}. *)

Inductive step : ExecutionState -> ExecutionState -> Prop :=
| transfer:
    forall dest_addr amount final_bm rest fenv env_stack c_st,
      let src_addr := (c_address c_st) in
      let old_bm := (balance_map fenv) in
      let new_bm := (updateBalance old_bm dest_addr ((old_bm dest_addr) + amount)) in
      final_bm = (updateBalance new_bm src_addr ((new_bm src_addr) - amount)) ->
      step (Transfer dest_addr amount :: rest, fenv, env_stack, c_st)
           (rest,
           mkEnv (aexp_env fenv) (bexp_env fenv) rest final_bm (msg_data fenv),
           env_stack,
           c_st)

(* handle fn args & return *)
(* consider contract state changes *)
(* for now, all happens in same contract *)
| function_call:
    forall called_addr msg_val env env_stack c_st fenv fcode fname rest,
      fcode = getFunctionCode ((fn_env c_st) fname) ->
      fenv = mkEnv (Empty_Aexp_Env) (Empty_Bexp_Env) (rest) (balance_map env) (mkMsg msg_val (c_address c_st)) ->
      step ((Function_Call called_addr fname msg_val) :: rest, env, env_stack, c_st) (fcode, fenv, (env, c_st) :: env_stack, (c_env called_addr))

| function_exit:
    forall (fenv fenv' : FunctionEnv) (c_st c_st' : ContractState) env_stack,
      step (nil, fenv, (fenv', c_st') :: env_stack, c_st)
           (next_code fenv', fenv', env_stack, c_st')
| skip:
    forall rest env env_stack c_st,
      step (Skip :: rest, env, env_stack, c_st) (rest, env, env_stack, c_st)

| assign_aexp : 
    forall a x rest env env' env_stack c_st,
      let v := unfoldOptionZ (evalaexp (aexp_env env) a) in
      let aexp_env' := updateAexp (aexp_env env) x v in
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st) (rest, env', env_stack, c_st)

| assign_bexp :
    forall b x rest env env' env_stack c_st,
      let v := unfoldOptionBool (evalbexp (aexp_env env) (bexp_env env) b) in
      let bexp_env' := updateBexp (bexp_env env) x v in
      env' = mkEnv (aexp_env env) (bexp_env') (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Bexp x b :: rest, env, env_stack, c_st) (rest, env', env_stack, c_st)

| if_true :
    forall b s1 s2 rest env env_stack c_st,
      Some true = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st) (s1 ++ rest, env, env_stack, c_st)

| if_false :
    forall b s1 s2 rest env env_stack c_st,
      Some false = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st) (s2 ++ rest, env, env_stack, c_st)

| while:
    forall (s : list instr) b rest env env_stack c_st,
      step (While b s :: rest, env, env_stack, c_st)
           ((IfThenElse b (s ++ While b s :: nil) (Skip :: nil)) :: rest, env, env_stack, c_st)
.

Inductive steps : ExecutionState -> ExecutionState -> Prop :=
| refl : forall S,
    steps S S
| trans: forall S S' S'',
    step S S' -> steps S' S'' -> steps S S''.




Example transfer_ex:
  steps (Transfer 7 1 :: nil, Empty_FunctionEnv, nil, Default_ContractState)
        (nil, replace_bmap Empty_FunctionEnv (updateBalance (updateBalance Empty_BalanceMap 7 1) 0 (-1)%Z), nil, Default_ContractState)
  .
Proof.
  apply trans with (S' := (nil, replace_bmap Empty_FunctionEnv (updateBalance (updateBalance Empty_BalanceMap 7 1) 0 (-1)%Z), nil, Default_ContractState)).
  {
    apply transfer. simpl. reflexivity.
  }
  {
    apply refl.
  }
  Qed.













Definition SUM_Code := (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil).
                  
Check SUM_Code.

Let body := Body SUM_Code.
(* Let emptyBody := EmptyBody. *)
Let emptyFnEnv : Functions_Env := fun f => None.
Let fn_name : string := "SUM".

Let fun_env := defineFunction emptyFnEnv fn_name body.

Definition Program_Env := mkEnv Empty_Aexp_Env Empty_Bexp_Env nil.

Definition Program := Assignment_Aexp "n" (Int 1) :: 
                      Function_Call 10 fn_name 0 :: nil.

Let targetCode := Assignment_Aexp "n" (Int 10) :: nil.

(* Let stackEnv := mkEnv (updateAexp (aexp_env ( Program_Env) "n" 1) Empty_Bexp_Env fun_env nil. *)

Let targetEnv := Program_Env. 

Let targetEnvStack := stackEnv :: nil.

Example Step_Into_Call :
  steps (Assignment_Aexp "n" (Int 1) :: Function_Call "SUM" :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil,
   nil)
  (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil,
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil) :: nil).
Proof.
  apply trans with (S' := (Function_Call "SUM" :: nil,
                          (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil),
                          nil)).
  -apply assign_aexp. simpl. reflexivity.
  (* -apply trans with (S' := (Assignment_Aexp "n" (Int 10) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env,
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env) :: nil)). *)
  -apply trans with (S' := (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil,
  mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil,
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil) :: nil)).
    *apply function_call.
     {
      simpl. reflexivity.
     }
     {
      simpl. reflexivity.
     }
    * apply refl.
  Qed.


Example Call_With_Code_After :
  steps (Assignment_Aexp "n" (Int 1) :: Function_Call "SUM" :: Assignment_Aexp "n" (Int 99) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil,
   nil)
  (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env (Assignment_Aexp "n" (Int 99) :: nil),
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil) :: nil).
Proof.
  apply trans with (S' := (Function_Call "SUM" :: Assignment_Aexp "n" (Int 99) :: nil,
                          (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil),
                          nil)).
  -apply assign_aexp. simpl. reflexivity.
  (* -apply trans with (S' := (Assignment_Aexp "n" (Int 10) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env,
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env) :: nil)). *)
  -apply trans with (S' := (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil,
  mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env (Assignment_Aexp "n" (Int 99) :: nil),
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil) :: nil)).
    *apply function_call.
     {
      simpl. reflexivity.
     }
     {
      simpl. reflexivity.
     }
    * apply refl.
  Qed.

Example Step_Outside_Call :
  steps (Assignment_Aexp "n" (Int 1) :: Function_Call "SUM" :: Assignment_Aexp "n" (Int 99) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil,
   nil)
  (Assignment_Aexp "n" (Int 99) :: nil,
   mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil,
   nil).
Proof.
  apply trans with (S' := (Function_Call "SUM" :: Assignment_Aexp "n" (Int 99) :: nil,
                          (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil),
                          nil)).
  -apply assign_aexp. simpl. reflexivity.
  (* -apply trans with (S' := (Assignment_Aexp "n" (Int 10) :: nil,
   mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env,
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env) :: nil)). *)
  -apply trans with (S' := (Assignment_Aexp "n" (Int 10) ::
                   Assignment_Aexp "sum" (Int 0) ::
                   While (Aexp_Geq (AId "n") (Int 1)) (
                     Assignment_Aexp "sum" (Plus (AId "n") (AId "sum")) ::
                     Assignment_Aexp "n" (Plus (AId "n") (Int (Z.opp 1))) :: nil
                   ) :: nil,
  mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env (Assignment_Aexp "n" (Int 99) :: nil),
   (mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil) :: nil)).
    *apply function_call.
     {
      simpl. reflexivity.
     }
     {
      simpl. reflexivity.
     }
    * apply trans with (S' := (Assignment_Aexp "n" (Int 99) :: nil,
   mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil,
   nil)).
   { simpl. apply function_exit. reflexivity. }
   { apply refl. }
  Qed.










(* Example Run :
  steps (Program, Program_Env, nil) (targetCode, targetEnv, targetEnvStack).
Proof.
  apply trans with (S' := (targetCode, targetEnv, targetEnvStack)).
  -apply assign_aexp.
 *)















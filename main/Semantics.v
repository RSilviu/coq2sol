Require Import ZArith.
Require Import String.
Require Import List.

Require Import main.Syntax.

Open Scope string_scope.


Definition EnvStack := list (FunctionEnv * ContractState).

Definition ExecutionState : Type :=  Code * FunctionEnv * EnvStack * ContractState * ContractsEnv.

Open Scope list_scope.

Inductive step : ExecutionState -> ExecutionState -> Prop :=
| transfer:
    forall dest_addr amount value final_bm rest fenv env_stack c_st c_env new_bm src_addr old_bm,
      src_addr = (c_address c_st) ->
      old_bm = (balance_map fenv) ->
      value = unfoldOptionZ (evalaexp (aexp_env fenv) amount) ->
      new_bm = (updateBalance old_bm dest_addr ((old_bm dest_addr) + value)) ->
      final_bm = (updateBalance new_bm src_addr ((new_bm src_addr) - value)) ->
      step (Transfer dest_addr amount :: rest, fenv, env_stack, c_st, c_env)
           (rest,
           mkEnv (aexp_env fenv) (bexp_env fenv) rest final_bm (msg_data fenv),
           env_stack,
           c_st, c_env)

| function_call:
    forall called_addr msg_val value env env_stack c_st c_env c_st' fenv fcode fname rest,
      c_st' = c_env called_addr ->
      fcode = getFunctionCode ((fn_env c_st') fname) ->
      value = unfoldOptionZ (evalaexp (aexp_env env) msg_val) ->
      fenv = mkEnv (Empty_Aexp_Env) (Empty_Bexp_Env) (rest) (balance_map env) (mkMsg value (c_address c_st)) ->
      step ((Function_Call called_addr fname msg_val) :: rest, env, env_stack, c_st, c_env) (fcode, fenv, (env, c_st) :: env_stack, c_st', c_env)

| function_exit:
    forall (fenv fenv' : FunctionEnv) (c_st c_st' : ContractState) env_stack c_env,
      step (nil, fenv, (fenv', c_st') :: env_stack, c_st, c_env)
           (next_code fenv', fenv', env_stack, c_st', c_env)

| skip:
    forall rest env env_stack c_st c_env,
      step (Skip :: rest, env, env_stack, c_st, c_env) (rest, env, env_stack, c_st, c_env)

| declare_aexp:
    forall aexp_env' aexp_names rest env env' env_stack c_st c_env,
      aexp_env' = declareAexpList (aexp_env env) aexp_names ->
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      step ((Declare_Aexp aexp_names) :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st, c_env)

| assign_aexp : 
    forall a x v aexp_env' rest env env' env_stack c_st c_env,
      v = unfoldOptionZ (evalaexp (aexp_env env) a) ->
      aexp_env' = updateAexp (aexp_env env) x v ->
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st, c_env)

| assign_bexp :
    forall b x v bexp_env' rest env env' env_stack c_st c_env,
      v = unfoldOptionBool (evalbexp (aexp_env env) (bexp_env env) b) ->
      bexp_env' = updateBexp (bexp_env env) x v ->
      env' = mkEnv (aexp_env env) (bexp_env') (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Bexp x b :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st, c_env)

| if_true :
    forall b s1 s2 rest env env_stack c_st c_env,
      Some true = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st, c_env) (s1 ++ rest, env, env_stack, c_st, c_env)

| if_false :
    forall b s1 s2 rest env env_stack c_st c_env,
      Some false = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st, c_env) (s2 ++ rest, env, env_stack, c_st, c_env)

| while:
    forall (s : list instr) b rest env env_stack c_st c_env,
      step (While b s :: rest, env, env_stack, c_st, c_env)
           ((IfThenElse b (s ++ While b s :: nil) (Skip :: nil)) :: rest, env, env_stack, c_st, c_env)
.

Inductive steps : ExecutionState -> ExecutionState -> Prop :=
| refl : forall S,
    steps S S
| trans: forall S S' S'',
    step S S' -> steps S' S'' -> steps S S''.


(* Examples *)


(** address.transfer(amount) *)

Let receiver := "addr".
Let amount := Int 1.
Let amount_z := 1%Z.

Let example_contracts_env := Empty_ContractsEnv.

Example transfer_ex:
  steps (Transfer receiver amount :: nil, Empty_FunctionEnv, nil, Default_ContractState, example_contracts_env)
        (nil, replace_bmap Empty_FunctionEnv 
        (updateBalance (updateBalance Empty_BalanceMap receiver amount_z) 
        (c_address Default_ContractState) (-amount_z)), nil, Default_ContractState, example_contracts_env)
  .
Proof.
  eapply trans.
  {
    eapply transfer; eauto.
  }
  {
    apply refl.
  }
  Qed.




(** Setup *)
Let called_fn_code := Declare_Aexp ("fn_a" :: nil)  :: nil.
Let called_fn := "called_fn".
Let called_contract_funs_env := defineFunction Empty_Functions_Env called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let called_contract_state := mkContractState called_contract_address called_contract_funs_env Empty_Aexp_Env Empty_Bexp_Env.

Let calling_contract_state := Default_ContractState.

Let example2_contracts_env := updateContractsEnv Empty_ContractsEnv called_contract_address called_contract_state.

Let msg_val := Int 0.
Let msg_val_z := 0%Z.
Let current_vars := "a" :: nil.
Let current_code := (Declare_Aexp current_vars) :: (Function_Call called_contract_address called_fn msg_val) :: nil.

Let fn_env_before_call := (replace_aexp_env Empty_FunctionEnv (declareAexpList (aexp_env Empty_FunctionEnv) current_vars)).
Let called_fn_env := replace_msg_data Empty_FunctionEnv (mkMsg  msg_val_z (c_address calling_contract_state)).

(** function call *)
Example Step_Into_Call :
  steps (current_code, Empty_FunctionEnv, nil, calling_contract_state, example2_contracts_env)
        (called_fn_code, called_fn_env, (fn_env_before_call, calling_contract_state) :: nil, called_contract_state, example2_contracts_env).
Proof.
  eapply trans.
  - eapply declare_aexp; eauto.
  - eapply trans.
    * eapply function_call; eauto.
    * apply refl.
Qed.




(** function exit *)

Let fenv_with_remaining_code := replace_next_code Empty_FunctionEnv (Skip :: nil).
Let called_contract_address2 := "called_contract".
Let called_contract_state2 := mkContractState called_contract_address2 Empty_Functions_Env Empty_Aexp_Env Empty_Bexp_Env.

Let calling_contract_state2 := Default_ContractState.

Let example_contracts_env3 := updateContractsEnv 
(updateContractsEnv Empty_ContractsEnv called_contract_address2 called_contract_state2)
Default_Address calling_contract_state2.

Example Function_exit:
  steps (nil, Empty_FunctionEnv, (fenv_with_remaining_code, calling_contract_state2)::nil,
  called_contract_state2, example_contracts_env3)
  (next_code fenv_with_remaining_code, fenv_with_remaining_code, nil,
   calling_contract_state2, example_contracts_env3).
Proof.
  eapply trans.
  {
    eapply function_exit; eauto.
  }
  {
    apply refl.
  }
  Qed.


(** Code sample *)

(*

(Declare_Aexp "a" :: "b")::
(Assignment_Aexp "a" (Int 1))::

IfThenElse (Aexp_Gt (AId "a") (AId "b")) 
  (Transfer "addr" (Int 20))::nil               (* if *)
(Function_Call "addr" "send" (AId "b"))::nil  (* else *)

::nil 

*)















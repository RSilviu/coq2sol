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
      value = unfold_option_z (eval_aexp (aexp_env fenv) amount) ->
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
      value = unfold_option_z (eval_aexp (aexp_env env) msg_val) ->
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

| assign_aexp_local : (* variable is local to function env *)
    forall a x v aexp_env' rest env env' env_stack c_st c_env string_id,
      string_id = unfold_aexp_id x ->
      v = unfold_option_z (eval_aexp (aexp_env env) a) ->
      aexp_env' = update_aexp (aexp_env env) string_id v ->
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st, c_env)

| assign_aexp_contract : (* variable is contract member *)
    forall a x v contract_aexp_env local_aexp_env rest env env' env_stack c_st c_st' c_env string_id,
      string_id = unfold_aexp_id x ->
      v = unfold_option_z (eval_aexp (aexp_env env) a) ->
      local_aexp_env = update_aexp (aexp_env env) string_id v ->
      contract_aexp_env = update_aexp (aexp_vars c_st) string_id v ->
      env' = mkEnv local_aexp_env (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      c_st' = replace_contract_aexp_env c_st contract_aexp_env ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st', c_env)

| assign_bexp :
    forall b x v bexp_env' rest env env' env_stack c_st c_env,
      v = unfold_option_bool (eval_bexp (aexp_env env) (bexp_env env) b) ->
      bexp_env' = update_bexp (bexp_env env) x v ->
      env' = mkEnv (aexp_env env) (bexp_env') (next_code env) (balance_map env) (msg_data env) ->
      step (Assignment_Bexp x b :: rest, env, env_stack, c_st, c_env) (rest, env', env_stack, c_st, c_env)

| if_true :
    forall b s1 s2 rest env env_stack c_st c_env,
      Some true = (eval_bexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st, c_env) (s1 ++ rest, env, env_stack, c_st, c_env)

| if_false :
    forall b s1 s2 rest env env_stack c_st c_env,
      Some false = (eval_bexp (aexp_env env) (bexp_env env) b) ->
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
Section transfer.

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

End transfer.

Import ListNotations.


(** function call *)
Section function_call.

Let called_fn_code := [Declare_Aexp [("fn_a", None)]].
Let called_fn := "called_fn".
Let called_contract_funs_env := defineFunction Empty_Functions_Env called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let called_contract_state := mkContractState called_contract_address called_contract_funs_env Empty_Aexp_Env Empty_Bexp_Env.

Let calling_contract_state := Default_ContractState.

Let example_contracts_env := updateContractsEnv Empty_ContractsEnv called_contract_address called_contract_state.

Let msg_val := Int 0.
Let msg_val_z := 0%Z.
Let current_vars : list (string * option Z) := [("a", None)].
Let current_code := (Declare_Aexp current_vars) :: (Function_Call called_contract_address called_fn msg_val) :: nil.

Let fn_env_before_call := (replace_aexp_env Empty_FunctionEnv (declareAexpList (aexp_env Empty_FunctionEnv) current_vars)).
Let called_fn_env := replace_msg_data Empty_FunctionEnv (mkMsg  msg_val_z (c_address calling_contract_state)).

Example Step_Into_Call :
  steps (current_code, Empty_FunctionEnv, nil, calling_contract_state, example_contracts_env)
        (called_fn_code, called_fn_env, (fn_env_before_call, calling_contract_state) :: nil, called_contract_state, example_contracts_env).
Proof.
  eapply trans.
  - eapply declare_aexp; eauto.
  - eapply trans.
    * eapply function_call; eauto.
    * apply refl.
Qed.

End function_call.


(** function exit *)
Section function_exit.

Let fenv_with_remaining_code := replace_next_code Empty_FunctionEnv (Skip :: nil).
Let called_contract_address := "called_contract".
Let called_contract_state := mkContractState called_contract_address Empty_Functions_Env Empty_Aexp_Env Empty_Bexp_Env.

Let calling_contract_state := Default_ContractState.

Let example_contracts_env := updateContractsEnv 
(updateContractsEnv Empty_ContractsEnv called_contract_address called_contract_state)
Default_Address calling_contract_state.

Example Function_exit:
  steps (nil, Empty_FunctionEnv, (fenv_with_remaining_code, calling_contract_state)::nil,
  called_contract_state, example_contracts_env)
  (next_code fenv_with_remaining_code, fenv_with_remaining_code, nil,
   calling_contract_state, example_contracts_env).
Proof.
  eapply trans.
  {
    eapply function_exit; eauto.
  }
  {
    apply refl.
  }
  Qed.

End function_exit.


(** Contract and local variable *)
Section contract_and_local_var.

Let called_fn_code := [Declare_Aexp [("local_a", Some 100%Z)]; Assignment_Aexp (AId "contract_a") (AId "local_a")].
Let called_fn := "called_fn".
Let called_contract_funs_env := defineFunction Empty_Functions_Env called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let contract_aexp_env := declareAexpList Empty_Aexp_Env [("contract_a", None)].
Let called_contract_state := 
mkContractState called_contract_address called_contract_funs_env contract_aexp_env Empty_Bexp_Env.
Let final_contract_state :=
replace_contract_aexp_env called_contract_state (update_aexp contract_aexp_env (Some "contract_a") 100%Z).
Let initial_fn_env := replace_aexp_env Empty_FunctionEnv contract_aexp_env.
Let final_fn_env := 
replace_aexp_env initial_fn_env (update_aexp (update_aexp contract_aexp_env (Some "local_a") 100%Z) (Some "contract_a") 100%Z).

Example contract_and_local_var:
steps (called_fn_code, initial_fn_env, [], called_contract_state, Empty_ContractsEnv)
      ([], final_fn_env, [], final_contract_state, Empty_ContractsEnv).
Proof.
  eapply trans.
  {
    eapply declare_aexp; eauto.
  }
  eapply trans.
  eapply assign_aexp_contract; eauto.
  eapply refl.
Qed.

End contract_and_local_var.


(** Code sample *)
Section tricky_transfer.

Let address_Alice := "0xA".
Let balance_map_Alice := updateBalance Empty_BalanceMap address_Alice 10%Z. 

Let address_Jane := "0xF".
Let balance_map_Jane := updateBalance Empty_BalanceMap address_Jane 20%Z. 

Let fun_code_Alice := [Transfer address_Jane (Int 10%Z)].
Let fun_name_Alice := "Alice_Fun".
Let funs_env_Alice_contract := defineFunction Empty_Functions_Env fun_name_Alice (Body fun_code_Alice).


Example Tricky_Transfer:
steps ()
().
Proof.

End tricky_transfer.

(*
(Declare_Aexp "a" :: "b")::
(Assignment_Aexp "a" (Int 1))::

IfThenElse (Aexp_Gt (AId "a") (AId "b")) 
  (Transfer "addr" (Int 20))::nil               (* if *)
(Function_Call "addr" "send" (AId "b"))::nil  (* else *)

::nil 
*)















Require Import main.Syntax.
Open Scope list_scope.
Import ListNotations.


(**************************************************************)
(** Transition configuration *)

Definition EnvStack := list (FunctionEnv * ContractState).

Definition ExecutionState : Type :=  Code * FunctionEnv * EnvStack * ContractState * ContractsEnv * Balance_Env.


(**************************************************************)
(** Big Step Transitions *)

Inductive step : ExecutionState -> ExecutionState -> Prop :=
| transfer:
    forall dest_addr amount value final_bm rest fenv env_stack c_st c_env new_bm src_addr bm,
      src_addr = (c_address c_st) ->
      value = unfold_option_z (eval_aexp (aexp_env fenv) bm amount) ->
      new_bm = (updateBalance bm dest_addr (unfold_option_z (bm dest_addr) + value)) ->
      final_bm = (updateBalance new_bm src_addr (unfold_option_z (new_bm src_addr) - value)) ->
      step (Transfer dest_addr amount :: rest, fenv, env_stack, c_st, c_env, bm)
           (rest,
           fenv,
           env_stack,
           c_st, c_env, final_bm)

| function_call:
    forall called_addr msg_val value env env_stack c_st c_env c_st' fenv fcode fname rest bm,
      c_st' = get_calling_contract called_addr c_env c_st ->
      fcode = getFunctionCode ((fn_env c_st') fname) ->
      value = unfold_option_z (eval_aexp (aexp_env env) bm (unfold_option msg_val Default_Aexp)) ->
      fenv = mkEnv (aexp_vars c_st') (bexp_vars c_st') (rest) (mkMsg value (c_address c_st)) ->
      step ((Function_Call called_addr fname msg_val) :: rest, env, env_stack, c_st, c_env, bm) 
           (fcode, fenv, (env, c_st) :: env_stack, c_st', c_env, bm)

| function_exit:
    forall (fenv fenv' : FunctionEnv) (c_st c_st' : ContractState) env_stack c_env bm,
      step (nil, fenv, (fenv', c_st') :: env_stack, c_st, c_env, bm)
           (next_code fenv', fenv', env_stack, c_st', c_env, bm)

| skip:
    forall rest env env_stack c_st c_env bm,
      step (Skip :: rest, env, env_stack, c_st, c_env, bm) (rest, env, env_stack, c_st, c_env, bm)

(** aexp declaration and assignment *)

| declare_aexp_local:
    forall aexp_env' aexp_names rest env env' env_stack c_st c_env bm,
      aexp_env' = declareAexpList (aexp_env env) aexp_names ->
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (msg_data env) ->
      step ((Declare_Aexp aexp_names) :: rest, env, env_stack, c_st, c_env, bm) 
            (rest, env', env_stack, c_st, c_env, bm)

| declare_aexp_contract:
    forall aexp_env' aexp_names rest env env_stack c_st c_st' c_env bm,
      aexp_env' = declareAexpList (aexp_vars c_st) aexp_names ->
      c_st' = replace_contract_aexp_env c_st aexp_env' ->
      step ((Declare_Aexp aexp_names) :: rest, env, env_stack, c_st, c_env, bm) 
            (rest, env, env_stack, c_st', c_env, bm)

| assign_aexp_local :
    forall a x v aexp_env' rest env env' env_stack c_st c_env string_id bm,
      string_id = unfold_aexp_id x ->
      v = unfold_option_z (eval_aexp (aexp_env env) bm a) ->
      aexp_env' = update_aexp (aexp_env env) string_id v ->
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (msg_data env) ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st, c_env, bm) 
           (rest, env', env_stack, c_st, c_env, bm)

| assign_aexp_contract :
    forall a x v contract_aexp_env local_aexp_env rest env env' env_stack c_st c_st' c_env string_id bm,
      string_id = unfold_aexp_id x ->
      v = unfold_option_z (eval_aexp (aexp_env env) bm a) ->
      local_aexp_env = update_aexp (aexp_env env) string_id v ->
      contract_aexp_env = update_aexp (aexp_vars c_st) string_id v ->
      env' = mkEnv local_aexp_env (bexp_env env) (next_code env) (msg_data env) ->
      c_st' = replace_contract_aexp_env c_st contract_aexp_env ->
      step (Assignment_Aexp x a :: rest, env, env_stack, c_st, c_env, bm) 
           (rest, env', env_stack, c_st', c_env, bm)

(** bexp declaration and assignment *)

| declare_bexp_local:
    forall bexp_env' bexp_names rest env env' env_stack c_st c_env bm,
      bexp_env' = declareBexpList (bexp_env env) bexp_names ->
      env' = mkEnv (aexp_env env) bexp_env' (next_code env) (msg_data env) ->
      step ((Declare_Bexp bexp_names) :: rest, env, env_stack, c_st, c_env, bm) 
            (rest, env', env_stack, c_st, c_env, bm)

| declare_bexp_contract:
    forall bexp_env' bexp_names rest env env_stack c_st c_st' c_env bm,
      bexp_env' = declareBexpList (bexp_vars c_st) bexp_names ->
      c_st' = replace_contract_bexp_env c_st bexp_env' ->
      step ((Declare_Bexp bexp_names) :: rest, env, env_stack, c_st, c_env, bm) 
            (rest, env, env_stack, c_st', c_env, bm)

| assign_bexp_local :
    forall b x v bexp_env' rest env env' env_stack c_st c_env bm string_id,
      string_id = unfold_bexp_id x ->
      v = unfold_option_bool (eval_bexp (aexp_env env) bm (bexp_env env) b) ->
      bexp_env' = update_bexp (bexp_env env) string_id v ->
      env' = mkEnv (aexp_env env) (bexp_env') (next_code env) (msg_data env) ->
      step (Assignment_Bexp x b :: rest, env, env_stack, c_st, c_env, bm) 
           (rest, env', env_stack, c_st, c_env, bm)

| assign_bexp_contract :
    forall b x string_id v contract_bexp_env local_bexp_env rest env env' env_stack c_st c_st' c_env bm,
      string_id = unfold_bexp_id x ->
      v = unfold_option_bool (eval_bexp (aexp_env env) bm (bexp_env env) b) ->
      local_bexp_env = update_bexp (bexp_env env) string_id v ->
      contract_bexp_env = update_bexp (bexp_vars c_st) string_id v ->
      env' = mkEnv (aexp_env env) local_bexp_env (next_code env) (msg_data env) ->
      c_st' = replace_contract_bexp_env c_st contract_bexp_env ->
      step (Assignment_Bexp x b :: rest, env, env_stack, c_st, c_env, bm) 
           (rest, env', env_stack, c_st', c_env, bm)

(** if *)

| if_true :
    forall b s1 s2 rest env env_stack c_st c_env bm,
      Some true = (eval_bexp (aexp_env env) bm (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st, c_env, bm) 
           (s1 ++ rest, env, env_stack, c_st, c_env, bm)

| if_false :
    forall b s1 s2 rest env env_stack c_st c_env bm,
      Some false = (eval_bexp (aexp_env env) bm (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack, c_st, c_env, bm)
           (s2 ++ rest, env, env_stack, c_st, c_env, bm)

(** while *)

| while:
    forall (s : list instr) b rest env env_stack c_st c_env bm,
      step (While b s :: rest, env, env_stack, c_st, c_env, bm)
           ([IfThenElse b (s ++ (While b s :: rest)) rest], env, env_stack, c_st, c_env, bm)
.


(**************************************************************)
(** Binary relations on steps *)

Inductive steps : ExecutionState -> ExecutionState -> Prop :=
| refl : forall S,
    steps S S
| trans: forall S S' S'',
    step S S' -> steps S' S'' -> steps S S''.


(**************************************************************)
(** Proven examples of semantics *)


(**************************************************************)
(** address.transfer(amount) *)

Section transfer.

Let receiver := "addr".
Let amount_aexp := Int 1.
Let amount_z := 1.

Let example_contracts_env := Empty_ContractsEnv.
Let new_balances := (updateBalance (updateBalance Empty_BalanceEnv receiver amount_z) (c_address Default_ContractState) (-amount_z)).

Example transfer_ex:
  steps (Transfer receiver amount_aexp :: nil, Empty_FunctionEnv, nil, Default_ContractState, example_contracts_env, Empty_BalanceEnv)
        (nil, Empty_FunctionEnv, nil, Default_ContractState, example_contracts_env, new_balances).
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


(**************************************************************)
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
Let msg_val_z := 0.
Let current_vars : list (string * option aexp) := [("a", None)].
Let current_code := (Declare_Aexp current_vars) :: (Function_Call (Some called_contract_address) called_fn (Some msg_val)) :: nil.

Let fn_env_before_call := (replace_aexp_env Empty_FunctionEnv (declareAexpList (aexp_env Empty_FunctionEnv) current_vars)).
Let called_fn_env := replace_msg_data Empty_FunctionEnv (mkMsg  msg_val_z (c_address calling_contract_state)).

Example Step_Into_Call :
  steps (current_code, Empty_FunctionEnv, nil, calling_contract_state, example_contracts_env, Empty_BalanceEnv)
        (called_fn_code, called_fn_env, (fn_env_before_call, calling_contract_state) :: nil,
         called_contract_state, example_contracts_env, Empty_BalanceEnv).
Proof.
  eapply trans.
  - eapply declare_aexp_local; eauto.
  - eapply trans.
    * eapply function_call; eauto.
    * apply refl.
Qed.

End function_call.


(**************************************************************)
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
  called_contract_state, example_contracts_env, Empty_BalanceEnv)
  (next_code fenv_with_remaining_code, fenv_with_remaining_code, nil,
   calling_contract_state, example_contracts_env, Empty_BalanceEnv).
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


(**************************************************************)
(** Contract and local variables *)

Section contract_and_local_var.

Let called_fn_code := [Declare_Aexp [("local_a", Some (Int 100))]; Assignment_Aexp (AId "contract_a") (AId "local_a")].
Let called_fn := "called_fn".
Let called_contract_funs_env := defineFunction Empty_Functions_Env called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let contract_aexp_env := declareAexpList Empty_Aexp_Env [("contract_a", None)].
Let called_contract_state := 
mkContractState called_contract_address called_contract_funs_env contract_aexp_env Empty_Bexp_Env.
Let final_contract_state :=
replace_contract_aexp_env called_contract_state (update_aexp contract_aexp_env (Some "contract_a") 100).
Let initial_fn_env := replace_aexp_env Empty_FunctionEnv contract_aexp_env.
Let final_fn_env := 
replace_aexp_env initial_fn_env (update_aexp (update_aexp contract_aexp_env (Some "local_a") 100) (Some "contract_a") 100).

Example contract_and_local_var:
steps (called_fn_code, initial_fn_env, [], called_contract_state, Empty_ContractsEnv, Empty_BalanceEnv)
      ([], final_fn_env, [], final_contract_state, Empty_ContractsEnv, Empty_BalanceEnv).
Proof.
  eapply trans.
  {
    eapply declare_aexp_local; eauto.
  }
  eapply trans.
  eapply assign_aexp_contract; eauto.
  eapply refl.
Qed.

End contract_and_local_var.


(**************************************************************)
(** More advanced *)
(** 
  * [WARNING] Default address is used instead of expected sender address when sending contract state is not set.
  *
  *)

Section looped_transfer.

Let address_Alice := "alice".
Let address_Jane := "jane".

Let initial_balances := updateBalance (updateBalance Empty_BalanceEnv address_Jane 0) address_Alice 2.
Let final_balances := updateBalance (updateBalance initial_balances address_Jane 1) address_Alice 1.

Let fun_code_Alice := [While (Aexp_Gt (BalanceOf address_Alice) (BalanceOf address_Jane)) [Transfer address_Jane (Int 1)]].
Let fun_name_Alice := "Alice_Fun".
Let funs_env_Alice := defineFunction Empty_Functions_Env fun_name_Alice (Body fun_code_Alice).

Let contract_Alice := mkContractState address_Alice funs_env_Alice Empty_Aexp_Env Empty_Bexp_Env.

Example Looped_Transfer:
steps (fun_code_Alice, Empty_FunctionEnv, [], contract_Alice, Empty_ContractsEnv, initial_balances)
      ([], Empty_FunctionEnv, [], contract_Alice, Empty_ContractsEnv, final_balances).
Proof.
  eapply trans.
  {
    eapply while; eauto.
  }
  eapply trans.
  {  
    eapply if_true; eauto.
  }
  eapply trans.
  {
    eapply transfer; eauto.
  }
  eapply trans.
  {
    eapply while; eauto.
  }
  eapply trans.
  {  
    eapply if_false; eauto.
  }
  apply refl.
Qed.

End looped_transfer.




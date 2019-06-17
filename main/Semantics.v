Require Import main.Syntax.

Open Scope list_scope.

Import ListNotations.


(**************************************************************)
(** Transition configuration *)

Definition EnvStack := list (FunctionState * ContractState).

Definition ExecutionState : Type :=  Code * FunctionState * EnvStack * ContractState * Address2ContractState * Address2Balance.
Definition CompileState : Type :=  contract_parts * ContractState.

(* Inductive test_step : CompileState -> CompileState :=
| 
.

Definition agg (state : CompileState) (states : list CompileState) := state :: states.
 *)
Inductive compile_step : CompileState -> CompileState -> Prop :=
| function_definition:
    forall name body rest cstate cstate',
      cstate' = update_contract_functions cstate (define_function (functions cstate) name (Body body)) ->
      compile_step (Define_Function name body :: rest, cstate)
                   (rest, cstate')

| declare_aexp_field:
    forall aexp_env' id rest cstate cstate',
      aexp_env' = declare_aexp (aexp_fields cstate) id ->
      cstate' = update_contract_aexp_vars cstate aexp_env' ->
      compile_step ((Declare_Aexp_Field id) :: rest, cstate)
                   (rest, cstate')

| define_aexp_field:
    forall aexp_env' aexp_def rest cstate cstate',
      aexp_env' = define_aexp (aexp_fields cstate) aexp_def ->
      cstate' = update_contract_aexp_vars cstate aexp_env' ->
      compile_step ((Define_Aexp_Field aexp_def) :: rest, cstate)
                   (rest, cstate')

| declare_bexp_field:
    forall bexp_env' id rest cstate cstate',
      bexp_env' = declare_bexp (bexp_fields cstate) id ->
      cstate' = update_contract_bexp_vars cstate bexp_env' ->
      compile_step ((Declare_Bexp_Field id) :: rest, cstate)
               (rest, cstate')

| define_bexp_field:
    forall bexp_env' bexp_def rest cstate cstate',
      bexp_env' = define_bexp (bexp_fields cstate) bexp_def ->
      cstate' = update_contract_bexp_vars cstate bexp_env' ->
      compile_step ((Define_Bexp_Field bexp_def) :: rest, cstate) 
                   (rest, cstate').

Compute function_definition.
Check function_definition "TEST" [] [] Default_ContractState Default_ContractState.



(* 
    Definition CompileState : Type :=  contract_parts * ContractState.
*)


(**************************************************************)
(** Big Step Transitions *)

Inductive run_step : ExecutionState -> ExecutionState -> Prop :=
| transfer:
    forall dest_addr amount value aexp_context final_bm rest fstate env_stack cstate c_env new_bm src_addr bm,
      src_addr = (c_address cstate) ->
      aexp_context = get_aexp_eval_context fstate bm  ->
      value = unfold_option_z (eval_aexp aexp_context amount) ->
      new_bm = (update_balance bm dest_addr (unfold_option_z (bm dest_addr) + value)) ->
      final_bm = (update_balance new_bm src_addr (unfold_option_z (new_bm src_addr) - value)) ->
      run_step (Transfer dest_addr amount :: rest, fstate, env_stack, cstate, c_env, bm)
               (rest, fstate, env_stack, cstate, c_env, final_bm)

| function_call:
    forall aexp_context called_addr msg_val value env_stack cstate c_env cstate' fstate fstate' fcode fname rest bm,
      cstate' = get_calling_contract called_addr c_env cstate ->
      fcode = get_function_code ((functions cstate') fname) ->
      aexp_context = get_aexp_eval_context fstate bm ->
      value = unfold_option_z (eval_aexp aexp_context (unfold_option msg_val Default_Aexp)) ->
      fstate' = mkFunctionState (aexp_fields cstate') (bexp_fields cstate') (rest) (mkMsg value (c_address cstate)) ->
      run_step ((Function_Call called_addr fname msg_val) :: rest, fstate, env_stack, cstate, c_env, bm) 
               (fcode, fstate', (fstate, cstate) :: env_stack, cstate', c_env, bm)

| function_exit:
    forall (fstate fstate' : FunctionState) (cstate cstate' : ContractState) env_stack c_env bm,
      run_step ([], fstate, (fstate', cstate') :: env_stack, cstate, c_env, bm)
               (next_code fstate', fstate', env_stack, cstate', c_env, bm)

| skip:
    forall rest fstate env_stack cstate c_env bm,
      run_step (Skip :: rest, fstate, env_stack, cstate, c_env, bm) (rest, fstate, env_stack, cstate, c_env, bm)

(** aexp var declaration *)

| declare_aexp_local:
    forall aexp_locals' id rest fstate fstate' env_stack cstate c_env bm,
      aexp_locals' = declare_aexp (aexp_locals fstate) id ->
      fstate' = update_function_aexp_locals fstate aexp_locals' ->
      run_step ((Declare_Aexp id) :: rest, fstate, env_stack, cstate, c_env, bm)
                (rest, fstate', env_stack, cstate, c_env, bm)

(** aexp var definition *)

| define_aexp_local:
    forall aexp_locals' aexp_def rest fstate fstate' env_stack cstate c_env bm,
      aexp_locals' = define_aexp (aexp_locals fstate) aexp_def ->
      fstate' = update_function_aexp_locals fstate aexp_locals' ->
      run_step ((Define_Aexp aexp_def) :: rest, fstate, env_stack, cstate, c_env, bm)
               (rest, fstate', env_stack, cstate, c_env, bm)

(** aexp assignment *)

| assign_aexp_local :
    forall aexp_context a x v aexp_locals' rest fstate fstate' env_stack cstate c_env string_id bm,
      string_id = unfold_aexp_id x ->
      aexp_context = get_aexp_eval_context fstate bm ->
      v = unfold_option_z (eval_aexp aexp_context a) ->
      aexp_locals' = update_aexp_vars (aexp_locals fstate) string_id v ->
      fstate' = update_function_aexp_locals fstate aexp_locals' ->
      run_step (Assign_Aexp x a :: rest, fstate, env_stack, cstate, c_env, bm) 
               (rest, fstate', env_stack, cstate, c_env, bm)

| assign_aexp_contract :
    forall aexp_context a x v contract_aexps local_aexps rest fstate fstate' env_stack cstate cstate' c_env string_id bm,
      string_id = unfold_aexp_id x ->
      aexp_context = get_aexp_eval_context fstate bm ->
      v = unfold_option_z (eval_aexp aexp_context a) ->
      local_aexps = update_aexp_vars (aexp_locals fstate) string_id v ->
      contract_aexps = update_aexp_vars (aexp_fields cstate) string_id v ->
      fstate' = update_function_aexp_locals fstate local_aexps ->
      cstate' = update_contract_aexp_vars cstate contract_aexps ->
      run_step (Assign_Aexp x a :: rest, fstate, env_stack, cstate, c_env, bm) 
               (rest, fstate', env_stack, cstate', c_env, bm)

(** bexp var declaration *)

| declare_bexp_local:
    forall bexp_locals' id rest fstate fstate' env_stack cstate c_env bm,
      bexp_locals' = declare_bexp (bexp_locals fstate) id ->
      fstate' = update_function_bexp_locals fstate bexp_locals' ->
      run_step ((Declare_Bexp id) :: rest, fstate, env_stack, cstate, c_env, bm) 
               (rest, fstate', env_stack, cstate, c_env, bm)

(** bexp var definition *)

| define_bexp_local:
    forall bexp_locals' bexp_def rest fstate fstate' env_stack cstate c_env bm,
      bexp_locals' = define_bexp (bexp_locals fstate) bexp_def ->
      fstate' = update_function_bexp_locals fstate bexp_locals' ->
      run_step ((Define_Bexp bexp_def) :: rest, fstate, env_stack, cstate, c_env, bm) 
            (rest, fstate', env_stack, cstate, c_env, bm)

(** bexp assignment *)

| assign_bexp_local :
    forall aexp_context b x v bexp_locals' rest fstate fstate' env_stack cstate c_env bm string_id,
      string_id = unfold_bexp_id x ->
      aexp_context = get_aexp_eval_context fstate bm ->
      v = unfold_option_bool (eval_bexp aexp_context (bexp_locals fstate) b) ->
      bexp_locals' = update_bexp_vars (bexp_locals fstate) string_id v ->
      fstate' = update_function_bexp_locals fstate bexp_locals' ->
      run_step (Assign_Bexp x b :: rest, fstate, env_stack, cstate, c_env, bm) 
           (rest, fstate', env_stack, cstate, c_env, bm)

| assign_bexp_contract :
    forall aexp_context b x string_id v contract_bexps local_bexps rest fstate fstate' env_stack cstate cstate' c_env bm,
      string_id = unfold_bexp_id x ->
      aexp_context = get_aexp_eval_context fstate bm ->
      v = unfold_option_bool (eval_bexp aexp_context (bexp_locals fstate) b) ->
      local_bexps = update_bexp_vars (bexp_locals fstate) string_id v ->
      contract_bexps = update_bexp_vars (bexp_fields cstate) string_id v ->
      fstate' = update_function_bexp_locals fstate local_bexps ->
      cstate' = update_contract_bexp_vars cstate contract_bexps ->
      run_step (Assign_Bexp x b :: rest, fstate, env_stack, cstate, c_env, bm) 
           (rest, fstate', env_stack, cstate', c_env, bm)

(** if *)

| if_true :
    forall aexp_context b s1 s2 rest fstate env_stack cstate c_env bm,
      aexp_context = get_aexp_eval_context fstate bm ->
      Some true = (eval_bexp aexp_context (bexp_locals fstate) b) ->
      run_step (IfThenElse b s1 s2 :: rest, fstate, env_stack, cstate, c_env, bm)
           (s1 ++ rest, fstate, env_stack, cstate, c_env, bm)

| if_false :
    forall aexp_context b s1 s2 rest fstate env_stack cstate c_env bm,
      aexp_context = get_aexp_eval_context fstate bm ->
      Some false = (eval_bexp aexp_context (bexp_locals fstate) b) ->
      run_step (IfThenElse b s1 s2 :: rest, fstate, env_stack, cstate, c_env, bm)
           (s2 ++ rest, fstate, env_stack, cstate, c_env, bm)

(** while *)

| while:
    forall (s : list instr) b rest fstate env_stack cstate c_env bm,
      run_step (While b s :: rest, fstate, env_stack, cstate, c_env, bm)
           ([IfThenElse b (s ++ (While b s :: rest)) rest], fstate, env_stack, cstate, c_env, bm)
.

Compute if_true.

Check Transfer "x" (Int 10).

(**************************************************************)
(** Binary relations on steps *)

Inductive compile_steps : CompileState -> CompileState -> Prop :=
| compile_refl : forall S,
    compile_steps S S
| compile_trans: forall S S' S'',
    compile_step S S' -> compile_steps S' S'' -> compile_steps S S''.

Inductive run_steps : ExecutionState -> ExecutionState -> Prop :=
| run_refl : forall S,
    run_steps S S
| run_trans: forall S S' S'',
    run_step S S' -> run_steps S' S'' -> run_steps S S''.


Section compile_step_examples.

Let contract := [Declare_Aexp_Field "token";
                 Define_Function "transfer" [Define_Aexp ("amount", Int 10) ; Transfer "receiver" (AId "amount")]]
                 .

(* Example one: compile_steps 
 *)


(* Fixpoint parse_contract (parts : contract_parts) (cstate : ContractState) : list compile_step := 
match parts with
| part :: rest => match part with 
                  | Define_Function name body => function_definition name body rest cstate cstate' :: parse_contract rest cstate'
(*                   | Declare_Aexp_Fields names => 
                  | Declare_Bexp_Fields names =>
                  | Define_Aexp_Field (name, value)
                  | Define_Bexp_Field (name, value) *)
                  end
| _ => []
end.
 *)
(* create a contract from Coq compile state *)

(* add defined contract to Ethereum contracts, i.e. to ContractsEnv *)

(* prepare contract for running *)

End compile_step_examples.


(* Theorem transfer_correct: forall  next_step,
  steps transfer next_step ->  *)



(**************************************************************)
(** Proven examples of semantics *)


(**************************************************************)
(** address.transfer(amount) *)

Section transfer.

Let receiver := "addr".
Let amount_aexp := Int 1.
Let amount_z := 1.

Let example_contracts_env := Empty_Address2ContractState.
Let new_balances := (update_balance (update_balance Empty_Address2Balance receiver amount_z) (c_address Default_ContractState) (-amount_z)).

Example transfer_ex:
  run_steps (Transfer receiver amount_aexp :: nil, Empty_FunctionState, nil, Default_ContractState, example_contracts_env, Empty_Address2Balance)
        (nil, Empty_FunctionState, nil, Default_ContractState, example_contracts_env, new_balances).
Proof.
  eapply run_trans.
  {
    eapply transfer; eauto.
  }
  {
    apply run_refl.
  }
Qed.

End transfer.


(**************************************************************)
(** function call *)

Section function_call.

Let called_fn_code := [Declare_Aexp "fn_a"].
Let called_fn := "called_fn".
Let called_contract_funs_env := define_function Empty_Functions called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let called_contract_state := mkContractState called_contract_address called_contract_funs_env Empty_Aexp_Vars Empty_Bexp_Vars.

Let calling_contract_state := Default_ContractState.

Let example_contracts_env := update_contract_state Empty_Address2ContractState called_contract_address called_contract_state.

Let msg_val := Int 0.
Let msg_val_z := 0.
Let current_vars := "a".
Let current_code := (Declare_Aexp current_vars) :: (Function_Call (Some called_contract_address) called_fn (Some msg_val)) :: nil.

Let fn_env_before_call := (update_function_aexp_locals Empty_FunctionState (declare_aexp (aexp_locals Empty_FunctionState) current_vars)).
Let called_fn_env := update_function_msg_data Empty_FunctionState (mkMsg  msg_val_z (c_address calling_contract_state)).

Example Step_Into_Call :
  run_steps (current_code, Empty_FunctionState, nil, calling_contract_state, example_contracts_env, Empty_Address2Balance)
        (called_fn_code, called_fn_env, (fn_env_before_call, calling_contract_state) :: nil,
         called_contract_state, example_contracts_env, Empty_Address2Balance).
Proof.
  eapply run_trans.
  - eapply declare_aexp_local; eauto.
  - eapply run_trans.
    * eapply function_call; eauto.
    * apply run_refl.
Qed.

End function_call.


(**************************************************************)
(** function exit *)

Section function_exit.

Let fstate_with_remaining_code := update_function_next_code Empty_FunctionState (Skip :: nil).
Let called_contract_address := "called_contract".
Let called_contract_state := mkContractState called_contract_address Empty_Functions Empty_Aexp_Vars Empty_Bexp_Vars.

Let calling_contract_state := Default_ContractState.

Let example_contracts_env := update_contract_state 
(update_contract_state Empty_Address2ContractState called_contract_address called_contract_state)
Default_Address calling_contract_state.

Example Function_exit:
  run_steps (nil, Empty_FunctionState, (fstate_with_remaining_code, calling_contract_state)::nil,
  called_contract_state, example_contracts_env, Empty_Address2Balance)
  (next_code fstate_with_remaining_code, fstate_with_remaining_code, nil,
   calling_contract_state, example_contracts_env, Empty_Address2Balance).
Proof.
  eapply run_trans.
  {
    eapply function_exit; eauto.
  }
  {
    apply run_refl.
  }
  Qed.

End function_exit.


(**************************************************************)
(** Contract and local variables *)

Section contract_and_local_var.

Let called_fn_code := [Define_Aexp ("local_a", Int 100); Assign_Aexp (AId "contract_a") (AId "local_a")].
Let called_fn := "called_fn".
Let called_contract_funs_env := define_function Empty_Functions called_fn (Body called_fn_code).
Let called_contract_address := "called_contract".
Let contract_aexp_env := declare_aexp Empty_Aexp_Vars "contract_a".
Let called_contract_state := 
mkContractState called_contract_address called_contract_funs_env contract_aexp_env Empty_Bexp_Vars.
Let final_contract_state :=
update_contract_aexp_vars called_contract_state (update_aexp_vars contract_aexp_env (Some "contract_a") 100).
Let initial_fn_env := update_function_aexp_locals Empty_FunctionState contract_aexp_env.
Let final_fn_env := 
update_function_aexp_locals initial_fn_env (update_aexp_vars (update_aexp_vars contract_aexp_env (Some "local_a") 100) (Some "contract_a") 100).

Example contract_and_local_var:
run_steps (called_fn_code, initial_fn_env, [], called_contract_state, Empty_Address2ContractState, Empty_Address2Balance)
      ([], final_fn_env, [], final_contract_state, Empty_Address2ContractState, Empty_Address2Balance).
Proof.
  eapply run_trans.
  {
    eapply define_aexp_local; eauto.
  }
  eapply run_trans.
  eapply assign_aexp_contract; eauto.
  eapply run_refl.
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

Let initial_balances := update_balance (update_balance Empty_Address2Balance address_Jane 0) address_Alice 2.
Let final_balances := update_balance (update_balance initial_balances address_Jane 1) address_Alice 1.

Let fun_code_Alice := [While (Aexp_Gt (BalanceOf address_Alice) (BalanceOf address_Jane)) [Transfer address_Jane (Int 1)]].
Let fun_name_Alice := "Alice_Fun".
Let funs_env_Alice := define_function Empty_Functions fun_name_Alice (Body fun_code_Alice).

Let contract_Alice := mkContractState address_Alice funs_env_Alice Empty_Aexp_Vars Empty_Bexp_Vars.

Example Looped_Transfer:
run_steps (fun_code_Alice, Empty_FunctionState, [], contract_Alice, Empty_Address2ContractState, initial_balances)
      ([], Empty_FunctionState, [], contract_Alice, Empty_Address2ContractState, final_balances).
Proof.
  econstructor.
  {
    repeat econstructor; eauto.
  }
  econstructor.
  {
    repeat econstructor; eauto.
  }
  econstructor.
  {
    repeat econstructor; eauto.
  }
  econstructor.
  {
    repeat econstructor; eauto.
  }
  econstructor.
  {
    eapply if_false; eauto.
  }
  econstructor.
Qed.


(* Proof.
  eapply run_trans.
  {
    eapply while; eauto.
  }
  eapply run_trans.
  {  
    eapply if_true; eauto.
  }
  eapply run_trans.
  {
    eapply transfer; eauto.
  }
  eapply run_trans.
  {
    eapply while; eauto.
  }
  eapply run_trans.
  {  
    eapply if_false; eauto.
  }
  apply run_refl.
Qed. *)

End looped_transfer.




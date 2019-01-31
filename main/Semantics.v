Require Import ZArith.
Require Import String.
Require Import List.

Require Import main.Syntax.

Open Scope list_scope.


(* TODO: Move to Proofs *)
Let fn_vars := "fa"%string :: nil.
Let fn_code := Declare_Aexp fn_vars  :: nil.
Let fname := "called_fn"%string.
Definition cc_funs_env := defineFunction Empty_Functions_Env fname (Body fn_code).


Let calling_contract := Default_ContractState.
Let called_addr := "called_contract"%string.
Let called_contract := mkContractState called_addr true cc_funs_env Empty_Aexp_Env Empty_Bexp_Env.


Definition c_env (addr : address) : ContractState :=
match addr with
| called_addr => called_contract
end.


Definition EnvStack := list (FunctionEnv * ContractState).

Definition ExecutionState : Type :=  Code * FunctionEnv * EnvStack * ContractState.

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

| function_call:
    forall called_addr msg_val env env_stack c_st c_st' fenv fcode fname rest,
      c_st' = c_env called_addr ->
      fcode = getFunctionCode ((fn_env c_st') fname) ->
      fenv = mkEnv (Empty_Aexp_Env) (Empty_Bexp_Env) (rest) (balance_map env) (mkMsg msg_val (c_address c_st)) ->
      step ((Function_Call called_addr fname msg_val) :: rest, env, env_stack, c_st) (fcode, fenv, (env, c_st) :: env_stack, c_st')

| function_exit:
    forall (fenv fenv' : FunctionEnv) (c_st c_st' : ContractState) env_stack,
      step (nil, fenv, (fenv', c_st') :: env_stack, c_st)
           (next_code fenv', fenv', env_stack, c_st')

| skip:
    forall rest env env_stack c_st,
      step (Skip :: rest, env, env_stack, c_st) (rest, env, env_stack, c_st)

| declare_aexp:
    forall aexp_names rest env env' env_stack c_st,
      let aexp_env' := declareAexpList (aexp_env env) aexp_names in
      env' = mkEnv aexp_env' (bexp_env env) (next_code env) (balance_map env) (msg_data env) ->
      step ((Declare_Aexp aexp_names) :: rest, env, env_stack, c_st) (rest, env', env_stack, c_st)

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



(* Examples *)

Let receiver := "addr"%string.
Let amount := 1%Z.

Example transfer_ex:
  steps (Transfer receiver amount :: nil, Empty_FunctionEnv, nil, Default_ContractState)
        (nil, replace_bmap Empty_FunctionEnv (updateBalance (updateBalance Empty_BalanceMap receiver amount) (c_address Default_ContractState) (-amount)), nil, Default_ContractState)
  .
Proof.
  apply trans with (S' := (nil, replace_bmap Empty_FunctionEnv (updateBalance (updateBalance Empty_BalanceMap receiver amount) (c_address Default_ContractState) (-amount)), nil, Default_ContractState)).
  {
    apply transfer. simpl. reflexivity.
  }
  {
    apply refl.
  }
  Qed.



Let msg_val := 0%Z.

Let current_vars := "a"%string :: nil.
Let current_code := (Declare_Aexp current_vars) :: (Function_Call called_addr fname msg_val) :: nil.

Let initial_env := Empty_FunctionEnv.
Let env_before_call := (replace_aexp_env initial_env (declareAexpList (aexp_env initial_env) current_vars)).
Let called_fn_env := replace_msg_data initial_env (mkMsg msg_val (c_address calling_contract)).


Example Step_Into_Call :
  steps (current_code, initial_env, nil, calling_contract)
        (fn_code, called_fn_env, (env_before_call, calling_contract) :: nil, called_contract).
Proof.
  apply trans with (S' := ((Function_Call called_addr fname msg_val) :: nil, env_before_call, nil, calling_contract)).
  - apply declare_aexp. simpl. reflexivity.
  -apply trans with (S' := (fn_code, called_fn_env, (env_before_call, calling_contract) :: nil, called_contract)).
    *apply function_call.
     {
      reflexivity.
     }
     {
      reflexivity.
     }
     {
      reflexivity.
     }
    * apply refl.
  Qed.


(** Old, needs change *)
(*
Example Call_With_Code_After :
  steps ((Declare_Aexp "n" :: nil) :: Function_Call "SUM" :: Assignment_Aexp "n" (Int 99) :: nil,
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
  
*)
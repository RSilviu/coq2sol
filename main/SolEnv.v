Require Import main.Syntax.

Definition ContractsEnv := address -> ContractState.
Definition Empty_ContractsEnv : ContractsEnv := fun x => Default_ContractState.

Definition c_env := Empty_ContractsEnv.

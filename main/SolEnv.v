Require Import main.Syntax.

Definition ContractsEnv := address -> ContractState.
Definition Empty_ContractsEnv : ContractsEnv := fun x => Default_ContractState.

<<<<<<< HEAD


=======
>>>>>>> e38b0592a4c7822536590831bbead2d881c21133
Definition c_env := Empty_ContractsEnv.

Require Import ZArith.
Require Import String.

Require Import List.

Inductive aexp :=
| Int : Z -> aexp
| AId : string -> aexp
| Plus : aexp -> aexp -> aexp
| Mul : aexp -> aexp -> aexp
| Div : aexp -> aexp -> aexp
| Rem : aexp -> aexp -> aexp.

Check aexp.

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


Inductive instr :=
| Assignment_Aexp : string -> aexp -> instr
(* | Assignment_Bexp : string -> bexp -> instr *)
| IfThenElse : bexp -> list instr -> list instr -> instr
| While : bexp -> list instr -> instr
| Skip : instr
| Function_Call : string -> instr.

(* Notation "id ()" := (Function_Call id) (at level 50).

Let fn := "pay"%string.

Check fn ().
 *)
Inductive err :=
| VarError.

(* Record function :=
mkFunction{
 name : string;
 body : list instr
}. *)

Inductive function_body :=
| Body : list instr -> function_body
| EmptyBody : function_body.

Definition Code := list instr.

(* Definition Env := string ->  option Z. *)
Definition Env (T : Type) := string -> option T.

Definition Aexp_Env := Env Z.
Definition Empty_Aexp_Env : Aexp_Env := fun x => None.

Definition Bexp_Env := Env bool.
Definition Empty_Bexp_Env : Bexp_Env := fun x => None.

Definition Functions_Env := Env function_body.
Definition Empty_Functions_Env : Functions_Env := fun x => None.

Record AlphaEnv :=
mkEnv {
(*  names : list string; *)
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 fn_env : Functions_Env;
 next_code : Code
}.

Definition Empty_AlphaEnv := {| aexp_env := Empty_Aexp_Env; bexp_env := Empty_Bexp_Env; fn_env := Empty_Functions_Env; next_code := nil |}.

Definition defineFunction (env : Functions_Env) (name : string) (body : function_body) : Functions_Env :=
  fun x => if (string_dec x name) then Some body
  else (env x).


Definition getFunctionCode (opt_body : option function_body) : Code :=
  match opt_body with
  | Some (Body code) => code
  | _ => nil
  end.

(* Let body := Body (Skip :: nil).
Let emptyBody := EmptyBody.
Let emptyFnEnv : Functions_Env := fun f => None.
Let fn_name : string := "foo".

Let fun_env := defineFunction emptyFnEnv fn_name emptyBody.

Compute getFunctionCode (fun_env "foo"%string). *)


(* UTILS *)
Definition declareAexp (ident : string) : Aexp_Env :=
  fun x => if (string_dec x ident) then Some 0%Z
           else None.

Definition updateAexp (env : Aexp_Env) (var : string) (val : Z) : Aexp_Env :=
  fun x => if (string_dec x var) then Some val
  else (env x).


Fixpoint evalaexp (env : Aexp_Env) (a : aexp) : option Z :=
  match a with
  | Int z => Some z
  | AId x => env x
  | Plus a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                  | Some v1, Some v2 => Some (Z.add v1 v2)
                  | _, _ => None
                  end
  | Mul a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                  | Some v1, Some v2 => Some (Z.mul v1 v2)
                  | _, _ => None
                  end
  | Div a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.div v1 v2)
                 | _, _ => None
                 end
  | Rem a1 a2 => match (evalaexp env a1), (evalaexp env a2) with
                 | Some v1, Some v2 => if (Z.eqb 0 v2) then None else Some (Z.rem v1 v2)
                 | _, _ => None
                 end
  end.


Fixpoint evalbexp (aexp_env : Aexp_Env) (bexp_env : Bexp_Env) (b : bexp) : option bool :=
  match b with
  | Boolean b' => Some b'
  | BId x => bexp_env x
  | Aexp_Lt a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.ltb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Leq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.leb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Eq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.eqb v1 v2)
                    | _, _ => None
                    end
  | Aexp_Geq a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.geb v1 v2)
                    | _, _ => None
                     end
  | Aexp_Gt a1 a2 => match (evalaexp aexp_env a1), (evalaexp aexp_env a2) with
                    | Some v1, Some v2 => Some (Z.gtb v1 v2)
                    | _, _ => None
                    end
  | Not b' => match (evalbexp aexp_env bexp_env b') with
              | Some b'' => Some (negb b'')
              | _ => None
              end
  | And b1 b2 => match (evalbexp aexp_env bexp_env b1), (evalbexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (andb b1' b2')
                 | _, _ => None
                 end
  | Or b1 b2 => match (evalbexp aexp_env bexp_env b1), (evalbexp aexp_env bexp_env b2) with
                 | Some b1', Some b2' => Some (orb b1' b2')
                 | _, _ => None
                 end
  end.


(* Let n := AId "n".
Let x := AId "x".

Let x_decl := declareAexp "x" emptyEnv.

Compute evalaexp x_decl x.

Let vars := updateAexp x_decl "n" 10.

Compute evalaexp vars n.
Compute evalaexp vars x.

Let new_vars := updateAexp vars "x" 1.

Compute evalaexp new_vars x.

Compute evalaexp vars n. *)

(* Inductive DataType :=
| int : DataType
| bool : DataType. *)


Require Import ZArith.
Require Import String.
Require Import List.

Open Scope list_scope.


Definition EnvStack := list AlphaEnv.
Definition State : Type :=  Code * AlphaEnv * EnvStack.


(* ecord AlphaEnv :=
{
(*  names : list string; *)
 aexp_env : Aexp_Env;
 bexp_env : Bexp_Env;
 fn_env : Functions_Env
}. *)

Definition unfoldOptionZ (opt_z : option Z) :=
match opt_z with
| Some v => v
| _ => 0%Z
end.

Inductive step : State -> State -> Prop :=
| function_call:
    forall env env_stack fenv fcode fname rest,
      fcode = getFunctionCode ((fn_env env) fname) ->
      fenv = mkEnv Empty_Aexp_Env Empty_Bexp_Env (fn_env env) (rest ++ (next_code env)) ->
      step ((Function_Call fname) :: rest, env, env_stack) (fcode, fenv, env :: env_stack)(*  ->
      step (fcode ++ rest, fenv, env :: env_stack) (rest, env, env_stack) *)
| function_exit:
    forall (env fenv : AlphaEnv) env_stack (fcode rest : Code),
      fenv = mkEnv (aexp_env fenv) (bexp_env fenv) (fn_env fenv) rest ->
      step (fcode, fenv, env :: env_stack)
           (rest, env, env_stack)
| skip:
    forall rest env env_stack,
      step (Skip :: rest, env, env_stack) (rest, env, env_stack)
| assign_aexp : 
    forall a x rest env env' env_stack,
      let v := unfoldOptionZ (evalaexp (aexp_env env) a) in
      let aexp_env' := updateAexp (aexp_env env) x v in
      env' = mkEnv aexp_env' (bexp_env env) (fn_env env) (next_code env) ->
      step (Assignment_Aexp x a :: rest, env, env_stack) (rest, env', env_stack)
| if_true :
    forall b s1 s2 rest env env_stack,
      Some true = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack) (s1 ++ rest, env, env_stack)
| if_false :
    forall b s1 s2 rest env env_stack,
      Some false = (evalbexp (aexp_env env) (bexp_env env) b) ->
      step (IfThenElse b s1 s2 :: rest, env, env_stack) (s2 ++ rest, env, env_stack)
| while:
    forall (s : list instr) b rest env env_stack,
      step (While b s :: rest, env, env_stack)
           ((IfThenElse b (s ++ While b s :: nil) (Skip :: nil)) :: rest, env, env_stack)
(* | termination:
    forall code env env' env_stack env_stack',
      step (code :: nil, env, env_stack) (nil, env', env_stack') *)
.

Inductive steps : State -> State -> Prop :=
| refl : forall S,
    steps S S
| trans: forall S S' S'',
    step S S' -> steps S' S'' -> steps S S''.


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

Definition Program_Env := mkEnv Empty_Aexp_Env Empty_Bexp_Env fun_env nil.

Definition Program := Assignment_Aexp "n" (Int 1) :: 
                      Function_Call fn_name :: nil.

Let targetCode := Assignment_Aexp "n" (Int 10) :: nil.

Let stackEnv := mkEnv (updateAexp (aexp_env Program_Env) "n" 1) Empty_Bexp_Env fun_env nil.

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















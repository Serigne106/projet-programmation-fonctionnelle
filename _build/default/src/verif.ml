
open Syntax 
(*env_type associe un identifiant de variable à son type et 
un identifiant de fonction à une paire (liste des types des arguments, type de retour)
type env_type = (idvar * typ) list | (idfun * (typ list * typ)) list*)

 
let rec comparer_type env1 env2 = match (env1, env2) with
| ([], []) -> true
| ((idvar1, typ1) ::t1, (idvar2, typ2) ::t2) 
             -> if idvar1 = idvar2 && typ1 = typ2 then comparer_type t1 t2 else false
| _ -> false   

(* Fonction récursive pour chercher une variable dans l'environnement *)
let rec chercher_var x env =
  match env with
  | [] -> failwith("Variable non définie: " ^ x)
  | (y,_) :: rest -> if x = y then true else chercher_var x rest
  | _ -> failwith("Erreur dans l'environnement")

(* Fonction récursive pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env =
  match env with
  | [] -> failwith ("Fonction non définie: " ^ id)
  | (g,(_,_)) :: rest -> if id = g.id then true                              
                              else chercher_fonction id rest
                              
                 

(* Vérification du typage des expressions 
 verif_expr (env_vars : env_type) (env_funs : env_type ) (e : expr) : typ*)

 let rec verif_expr env_vars env_funs e  = match e with
  | Var x -> chercher_var x env_vars
  | IdFun f -> chercher_fonction f env_funs
  | Int x -> TInt 
  | Bool b -> TBool 
  | BinaryOp (op, e1, e2) -> 
    let t1 = verif_expr env_vars env_funs e1 in
      let t2 = verif_expr env_vars env_funs e2 in
      match op, t1, t2 with 
      | (Plus | Minus | Mult | Div), TInt, TInt -> TInt
      | (And | Or), TBool, TBool -> TBool
      | (Equal | NEqual | Less | LessEq | Great | GreatEq), TInt, TInt -> TBool
      | _ -> failwith ("Erreur de typage dans une opération binaire")
  | UnaryOp (Not, e) -> 
      match verif_expr env_vars env_funs e with
      | TBool -> TBool
      | _ -> failwith("L'opérateur 'not' attend un booléen")
  | If (cond, e1, e2) -> 
      if verif_expr env_vars env_funs cond <> TBool then
        failwith("Condition d'un 'if' doit être un booléen");
      let t1 = verif_expr env_vars env_funs e1 in
      let t2 = verif_expr env_vars env_funs e2 in
      if t1 = t2 then t1
      else failwith ("Les deux branches du 'if' doivent avoir le même type")
  | Let (x, typ, e1, e2) ->
      let t1 = verif_expr env_vars env_funs e1 in
      if t1 = typ then
        let new_env = (x, typ) :: env_vars in
        verif_expr new_env env_funs e2
      else
        failwith("Mauvais typage dans 'let' pour la variable " ^ x)
  | App (f, args) -> (
      let (params_types, ret_type) = chercher_fonction f env_funs in
      if List.length args <> List.length params_types then
        failwith("Mauvais nombre d'arguments pour la fonction " ^ f);
      List.iter2
        (fun expr typ_attendu ->
          let typ_expr = verif_expr env_vars env_funs expr in
          if typ_expr <> typ_attendu then
            failwith("Mauvais type d'argument pour la fonction " ^ f))
        args params_types;
      ret_type)
      
    | _ -> failwith("Erreur de typage")

    (* verif_decl_fun: fun_decl -> env_type -> bool *)
  let rec verif_decl_fun f env = match (f.var_list, env) with
    | (_, []) -> false
    | (h,(g,(l,_))::rest)->  if f.id = g  then comparer_type h l else verif_decl_fun f rest
    | _ -> failwith("Erreur de typage") 
    
  
  (* verif_prog: programme -> env_type -> bool *)
  let rec verif_prog prog env = match prog with
    | [] -> true
    | f :: rest -> if verif_decl_fun f env then verif_prog rest env else false
    | _ -> failwith("Erreur de typage") 
    


exception Type_error of string

(*env_type associe un identifiant de variable à son type et 
un identifiant de fonction à une paire (liste des types des arguments, type de retour)
type env_type = (idvar * typ) list | (idfun * (typ list * typ)) list*)

exception Type_error of string

(* Fonction récursive pour chercher une variable dans l'environnement *)
let rec chercher_var x env =
  match env with
  | [] -> raise (Type_error ("Variable non définie: " ^ x))
  | (y, typ) :: rest -> if x = y then typ else chercher_var x rest

(* Fonction récursive pour chercher une fonction dans l'environnement *)
let rec chercher_fonction f env =
  match env with
  | [] -> raise (Type_error ("Fonction non définie: " ^ f))
  | (g,(l, t_retour)) :: rest -> if f = g then 
                      else chercher_fonction f rest

(* Vérification du typage des expressions 
 verif_expr (env_vars : env_type) (env_funs : env_type ) (e : expr) : typ*)
let rec verif_expr env_vars env_funs e  = match e with

  | Var x -> chercher_var x env_vars
  | IdFun f -> snd (chercher_fonction f env_funs)
  | Int _ -> TInt
  | Bool _ -> TBool
  | BinaryOp (op, e1, e2) -> (
      let t1 = verif_expr env_vars env_funs e1 in
      let t2 = verif_expr env_vars env_funs e2 in
      match op, t1, t2 with
      | (Plus | Minus | Mult | Div), TInt, TInt -> TInt
      | (And | Or), TBool, TBool -> TBool
      | (Equal | NEqual | Less | LessEq | Great | GreatEq), TInt, TInt -> TBool
      | _ -> raise (Type_error "Erreur de typage dans une opération binaire"))
  | UnaryOp (Not, e) -> (
      match verif_expr env_vars env_funs e with
      | TBool -> TBool
      | _ -> raise (Type_error "L'opérateur 'not' attend un booléen"))
  | If (cond, e1, e2) -> (
      if verif_expr env_vars env_funs cond <> TBool then
        raise (Type_error "Condition d'un 'if' doit être un booléen");
      let t1 = verif_expr env_vars env_funs e1 in
      let t2 = verif_expr env_vars env_funs e2 in
      if t1 = t2 then t1
      else raise (Type_error "Les deux branches du 'if' doivent avoir le même type"))
  | Let (x, typ, e1, e2) ->
      let t1 = verif_expr env_vars env_funs e1 in
      if t1 = typ then
        let new_env = (x, typ) :: env_vars in
        verif_expr new_env env_funs e2
      else
        raise (Type_error ("Mauvais typage dans 'let' pour la variable " ^ x))
  | App (f, args) -> (
      let (params_types, ret_type) = chercher_fonction f env_funs in
      if List.length args <> List.length params_types then
        raise (Type_error ("Mauvais nombre d'arguments pour la fonction " ^ f));
      List.iter2
        (fun expr typ_attendu ->
          let typ_expr = verif_expr env_vars env_funs expr in
          if typ_expr <> typ_attendu then
            raise (Type_error ("Mauvais type d'argument pour la fonction " ^ f)))
        args params_types;
      ret_type)



let verif_decl_fun _ = failwith "Not yet implemented"

let verif_prog _ = failwith "Not yet implemented"

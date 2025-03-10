open Syntax 

(* Définition des environnements *)
type env_type = {
  var_env : (idvar * typ) list;  (* Environnement des variables : liste d'associations (nom de variable, type) *)
  fun_env : (idfun * ((idvar * typ) list * typ)) list;  (* Environnement des fonctions : liste d'associations (nom de fonction, (liste de paramètres, type de retour)) *)
}

(* Environnement vide *)
let env_vide = {
  var_env = [];  (* Pas de variables *)
  fun_env = [];  (* Pas de fonctions *)
}

(* Fonction pour comparer deux listes de types *)
let rec comparer_type env1 env2 = match (env1, env2) with
| ([], []) -> true  (* Les deux listes sont vides, elles sont donc égales *)
| ((idvar1, typ1) :: t1, (idvar2, typ2) :: t2) -> 
    if idvar1 = idvar2 && typ1 = typ2 then comparer_type t1 t2  (* Les têtes des listes sont égales, on compare les queues *)
    else false  (* Les têtes des listes sont différentes, les listes ne sont pas égales *)
| _ -> false  (* Les listes ont des longueurs différentes, elles ne sont pas égales *)

(* Fonction pour chercher une variable dans l'environnement *)
let rec chercher_var x env_vars =
  match env_vars with
  | [] -> failwith ("Variable non définie: " ^ x)  (* La variable n'est pas trouvée *)
  | (y, typ) :: rest -> if x = y then typ else chercher_var x rest  (* Si la variable est trouvée, on retourne son type, sinon on continue la recherche *)

(* Fonction pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env_funs =
  match env_funs with
  | [] -> failwith ("Fonction non définie: " ^ id)  (* La fonction n'est pas trouvée *)
  | (g, (params, ret_type)) :: rest -> 
      if id = g then (params, ret_type) else chercher_fonction id rest  (* Si la fonction est trouvée, on retourne ses paramètres et son type de retour, sinon on continue la recherche *)

(* Vérification du typage des expressions *)
let rec verif_expr env e typ_attendu =
  match e with
  | Var x -> 
      let t = chercher_var x env.var_env in  (* On cherche le type de la variable *)
      if t = typ_attendu then true  (* Si le type correspond au type attendu, on retourne true *)
      else failwith ("La variable " ^ x ^ " n'a pas le type attendu")

  | Int _ -> typ_attendu = TInt  (* Si l'expression est un entier, le type attendu doit être TInt *)

  | Bool _ -> typ_attendu = TBool  (* Si l'expression est un booléen, le type attendu doit être TBool *)

  | BinaryOp (op, e1, e2) -> (
      match op with
      | Plus | Minus | Mult | Div -> 
          if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
          verif_expr env e1 TInt && verif_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)

      | And | Or -> 
          if typ_attendu <> TBool then failwith "Une opération logique doit retourner un booléen";
          verif_expr env e1 TBool && verif_expr env e2 TBool  (* Les deux opérandes doivent être des booléens *)

      | Equal | NEqual -> 
          let t1 = match e1 with 
            | Var x -> chercher_var x env.var_env 
            | _ -> failwith "Expression incorrecte, une variable est attendue"
          in
          let t2 = match e2 with 
            | Var x -> chercher_var x env.var_env 
            | _ -> failwith "Expression incorrecte, une variable est attendue"
          in
          if t1 = t2 then typ_attendu = TBool  (* Les deux opérandes doivent être du même type et le type attendu doit être TBool *)
          else failwith "Les deux opérandes d'une comparaison doivent être du même type"

      | Less | LessEq | Great | GreatEq -> 
          if typ_attendu <> TBool then failwith "Une comparaison doit retourner un booléen";
          verif_expr env e1 TInt && verif_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)
    )

  | UnaryOp (Not, e) -> 
      if typ_attendu <> TBool then failwith "L'opérateur 'not' doit retourner un booléen";
      verif_expr env e TBool  (* L'opérande doit être un booléen *)

  | If (cond, e1, e2) -> 
      if not (verif_expr env cond TBool) then
        failwith "La condition d'un 'if' doit être un booléen";
      verif_expr env e1 typ_attendu && verif_expr env e2 typ_attendu  (* Les deux branches doivent avoir le type attendu *)

  | Let (x, typ_x, e1, e2) ->
      if not (verif_expr env e1 typ_x) then
        failwith ("Mauvais typage dans 'let' pour la variable " ^ x);
      let new_env = { env with var_env = (x, typ_x) :: env.var_env } in  (* On ajoute la nouvelle variable à l'environnement *)
      verif_expr new_env e2 typ_attendu  (* On vérifie le typage de l'expression e2 dans le nouvel environnement *)

  | App (f, args) ->
      let (params_types, ret_type) = chercher_fonction f env.fun_env in  (* On cherche les paramètres et le type de retour de la fonction *)
      if List.length args <> List.length params_types then
        failwith ("Mauvais nombre d'arguments pour la fonction " ^ f);
      List.iter2
        (fun expr typ_attendu ->
          if not (verif_expr env expr typ_attendu) then
            failwith ("Mauvais type d'argument pour la fonction " ^ f))
        args (List.map snd params_types);  (* On vérifie le typage de chaque argument *)
      ret_type = typ_attendu  (* Le type de retour doit correspondre au type attendu *)

  | _ -> failwith "Erreur de typage"

(* Vérification de la déclaration d'une fonction *)
let rec verif_decl_fun f env =
  match env.fun_env with
  | [] -> false  (* La fonction n'est pas trouvée *)
  | (g, (param_types, _)) :: rest ->
      if f.id = g then comparer_type f.var_list param_types else verif_decl_fun f { var_env = env.var_env; fun_env = rest }  (* On compare les types des paramètres *)

(* Vérification du programme *)
let rec verif_prog prog env =
  match prog with
  | [] -> true  (* Le programme est vide, il est donc correct *)
  | f :: rest -> if verif_decl_fun f env then verif_prog rest env  (* On vérifie chaque fonction du programme *)
                 else failwith "Erreur de typage dans le programme"
      



(*#######################################################################################################*)
(*
open Syntax 
(*env_type associe un identifiant de variable à son type et 
un identifiant de fonction à une paire (liste des types des arguments, type de retour)
type env_type = (idvar * typ) list | (idfun * (typ list * typ)) list*)

(*env_type associe un identifiant de variable à son type et 
un identifiant de fonction à une paire (liste des arguments et leurs types , type de retour de la fonction)*)
type env_type = 
   | VarEnv of  (idvar * typ) list
   | FunEnv of  (idfun * ((idvar*typ) list * typ)) list 

type env_val = (idvar * typ) list 

let env_vide = {
  var_env = [];
  fun_env =  [];
}

(* Fonction pour ajouter une variable à l'environnement *)

 
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
  (*| _-> failwith("Erreur dans l'environnement")*)

(* Fonction récursive pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env =
  match env with
  | [] -> failwith ("Fonction non définie: " ^ id)
  | (g,(_,_)) :: rest -> if id = g.id then true                              
                              else chercher_fonction id rest
                              
                 

(* Vérification du typage des expressions 
 verif_expr (env_vars : env_type) (env_funs : env_type ) (e : expr) : typ

 let rec verif_expr env_vars env_funs e  = match e with 
  | Var x -> chercher_var x env_vars
  | IdFun f -> chercher_fonction f env_funs 
  | Int x -> true
  | Bool b -> true  
  | BinaryOp (op, e1, e2)   -> *)
  let rec verif_expr env_vars e typ_attendu = match e with
    | Var x -> 
        let t = chercher_var x env_vars in
        if t = typ_attendu then true
        else failwith ("La variable " ^ x ^ " n'a pas le type attendu")
  
    | Int _ -> typ_attendu = TInt
  
    | Bool _ -> typ_attendu = TBool  
  
    | BinaryOp (op, e1, e2) -> (
        match op with
        | Plus | Minus | Mult | Div -> 
            if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
            verif_expr env_vars e1 TInt &&
            verif_expr env_vars e2 TInt
  
        | And | Or -> 
            if typ_attendu <> TBool then failwith "Une opération logique doit retourner un booléen";
            verif_expr env_vars e1 TBool &&
            verif_expr env_vars e2 TBool
  
        | Equal | NEqual -> 
            let t1 = chercher_var_type env_vars e1 in
            let t2 = chercher_var_type env_vars e2 in
            if t1 = t2 then typ_attendu = TBool
            else failwith "Les deux opérandes d'une comparaison doivent être du même type"
  
        | Less | LessEq | Great | GreatEq -> 
            if typ_attendu <> TBool then failwith "Une comparaison doit retourner un booléen";
            verif_expr env_vars e1 TInt &&
            verif_expr env_vars e2 TInt
      )
  
    | UnaryOp (Not, e) -> 
        if typ_attendu <> TBool then failwith "L'opérateur 'not' doit retourner un booléen";
        verif_expr env_vars e TBool
  
    | If (cond, e1, e2) -> 
        if not (verif_expr env_vars cond TBool) then
          failwith "La condition d'un 'if' doit être un booléen";
        verif_expr env_vars e1 typ_attendu &&
        verif_expr env_vars e2 typ_attendu
  
    | Let (x, typ_x, e1, e2) ->
        if not (verif_expr env_vars e1 typ_x) then
          failwith ("Mauvais typage dans 'let' pour la variable " ^ x);
        let new_env = (x, typ_x) :: env_vars in
        verif_expr new_env e2 typ_attendu
  
    | _ -> failwith "Erreur de typage"
  

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
    

*)
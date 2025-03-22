open Syntax 

(* Définition des environnements *)
type env_type = {
  (* Environnement des variables : liste d'associations (nom de variable, type) *)
  var_env : (idvar * typ) list;  
  (* Environnement des fonctions : liste d'associations (nom de fonction, (liste de paramètres, type de retour)) *)
  fun_env : (idfun * ((idvar * typ) list * typ)) list;  
}

(* Environnement initial vide *)
let init_env = { 
  var_env = []; 
  fun_env = [] 
}

(* Fonction pour comparer deux listes de types *)
let rec comparer_type env1 env2 = match (env1, env2) with
   (* Les deux listes sont vides, elles sont donc égales *)
| ([], []) -> true 
    (* Les têtes des listes sont égales, on compare les queues *)
| ((idvar1, typ1) :: t1, (idvar2, typ2) :: t2) -> 
    if idvar1 = idvar2 && typ1 = typ2 then comparer_type t1 t2  
    (* Les têtes des listes sont différentes, les listes ne sont pas égales *)
    else false  
    (* Les listes ont des longueurs différentes, elles ne sont pas égales *)
| _ -> false  

(* Fonction pour chercher une variable dans l'environnement *)
let rec chercher_var x env_vars =
  match env_vars with
     (* La variable n'est pas trouvée *)
  | [] -> failwith ("Variable non définie: " ^ x) 
      (* Si la variable est trouvée, on retourne son type *)
  | (y, typ) :: rest -> 
      if x = y then typ  
      (* Sinon, on continue la recherche *)
      else chercher_var x rest  

(* Fonction pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env_funs =
  match env_funs with
      (* La fonction n'est pas trouvée *)
  | [] -> failwith ("Fonction non définie: " ^ id)  
      (* Si la fonction est trouvée, on retourne ses paramètres et son type de retour *)
  | (g, (params, ret_type)) :: rest -> 
      if id = g then (params, ret_type)  
      (* Sinon, on continue la recherche *)
      else chercher_fonction id rest  


(* Vérification du typage des expressions *)
let rec verif_expr env e typ_attendu =
  match e with
  | Var x -> 
      (* On cherche le type de la variable *)
      let t = chercher_var x env.var_env in 
      (* Si le type correspond au type attendu, on retourne true *)
      if t = typ_attendu then true  
      else failwith ("La variable " ^ x ^ " n'a pas le type attendu")

  | Int _ -> 
      (* Si l'expression est un entier, le type attendu doit être TInt *)
      typ_attendu = TInt  

  | Bool _ -> 
      (* Si l'expression est un booléen, le type attendu doit être TBool *)
      typ_attendu = TBool 

  | Float _ -> 
      (* Si l'expression est un flottant, le type attendu doit être TFloat *)
      typ_attendu = TFloat  
  
      (* Si l'expression est de type unité, le type attendu doit être TUnit *) 
  | Unit -> typ_attendu = TUnit
   
  
      (*Les operations binaires *)
  | BinaryOp (op, e1, e2) -> (
      (* Vérification des opérations binaires *)
      match (op, typ_attendu) with
      | (Plus | Minus | Mult | Div), TInt -> 
          (* Les deux opérandes doivent être des entiers *)
          verif_expr env e1 TInt && verif_expr env e2 TInt  
      
      | (PlusPT | MinusPT | MultPT | DivPT), TFloat ->
          (* Les deux opérandes doivent être des flottants *)
          verif_expr env e1 TFloat && verif_expr env e2 TFloat  
    
      | (And | Or), TBool -> 
          (* Les deux opérandes doivent être des booléens *)
          verif_expr env e1 TBool && verif_expr env e2 TBool  

      | (Equal | NEqual), TBool -> 
          (* Les deux opérandes doivent être soit des entiers, soit des flottants *)
          ((verif_expr env e1 TInt && verif_expr env e2 TInt) || 
          (verif_expr env e1 TFloat && verif_expr env e2 TFloat))
       
      | (Less | LessEq | Great | GreatEq), TBool -> 
          (* Les deux opérandes doivent être soit des entiers, soit des flottants *)
          ((verif_expr env e1 TInt && verif_expr env e2 TInt) || 
          (verif_expr env e1 TFloat && verif_expr env e2 TFloat)) 
      
      | _ -> false  
    )

  | UnaryOp (Not, e) -> 
      (* Vérification de l'opérateur unaire 'not' *)
      if typ_attendu <> TBool then failwith "L'opérateur 'not' doit retourner un booléen";
      (* L'opérande doit être un booléen *)
      verif_expr env e TBool  

  | If (cond, e1, e2) -> 
      (* Vérification d'une structure conditionnelle *)
      if not (verif_expr env cond TBool) then
        failwith "La condition d'un 'if' doit être un booléen";
      (* Les deux branches doivent avoir le type attendu *)
      verif_expr env e1 typ_attendu && verif_expr env e2 typ_attendu  

  | Let (x, typ_x, e1, e2) ->
      (* Vérification d'une déclaration locale *)
      if not (verif_expr env e1 typ_x) then
        failwith ("Mauvais typage dans 'let' pour la variable " ^ x);
      (* On ajoute la nouvelle variable à l'environnement *)
      let new_env = { env with var_env = (x, typ_x) :: env.var_env } in  
      (* On vérifie le typage de l'expression suivante *)
      verif_expr new_env e2 typ_attendu  

  | App (f, args) ->
      (* Vérification d'un appel de fonction *)
      let (params_types, ret_type) = chercher_fonction f env.fun_env in  
      (* On vérifie que le nombre d'arguments correspond au nombre de paramètres *)
      if List.length args <> List.length params_types then
        failwith ("Mauvais nombre d'arguments pour la fonction " ^ f);
      (* On vérifie le typage de chaque argument *)
      List.iter2
        (fun expr typ_attendu ->
          if not (verif_expr env expr typ_attendu) then
            failwith ("Mauvais type d'argument pour la fonction " ^ f))
        args (List.map snd params_types);  
      (* Le type de retour doit correspondre au type attendu *)
      ret_type = typ_attendu  
  | PrintInt e -> 
      (* Vérification de l'expression print_int *)
      if typ_attendu <> TUnit then failwith "L'opérateur 'print_int' doit retourner un unit";

        verif_expr env e TUnit  

  | LetRec (f, params, ret_type, e1, _) ->
          (* Vérification d'une déclaration de fonction récursive *)
          let new_env = { env with fun_env = (f, (params, ret_type)) :: env.fun_env } in  
          (* On vérifie le typage de l'expression suivante *)
          verif_expr new_env e1 typ_attendu

  | _ -> failwith "Erreur de typage"

(* Vérification du typage d'une déclaration de fonction *)
let verif_decl_fun env fdecl =
  (* Création d'un environnement local pour les paramètres *)
  let params_env = {
    var_env = List.map (fun (x, t) -> (x, t)) fdecl.var_list; 
    fun_env = env.fun_env
  } in 
  (* Vérifie que le corps de la fonction est bien typé *)
  verif_expr params_env fdecl.corps fdecl.typ_retour 
 
(* Vérification d'un programme *)
let verif_prog prog =
  (* Construire un environnement initial avec toutes les fonctions *)
  let init_env = {
    var_env = []; (* Pas de variables globales *)
    fun_env = List.map (fun f -> 
      (f.id, (f.var_list, f.typ_retour)) (* Stocke les paramètres et le type de retour *)
    ) prog
  } in 
  (* Vérifier que toutes les fonctions sont bien typées *)
  let tout_funs_ok = List.for_all (fun f -> verif_decl_fun init_env f) prog in

  (* Vérifier la présence d'une fonction `main` sans paramètres *)
  let est_valid_main = List.exists (fun f -> f.id = "main" && f.var_list = []) prog in
  
  (* Retourne vrai si tout est bien typé et que main() est défini *)
  tout_funs_ok && est_valid_main 
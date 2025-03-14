open Syntax 


type valeur = 
  | ValInt of int 
  | ValBool of bool

type var_val = {var:idvar; valeur:valeur}
type env_val = var_val list

(*Fonction pour chercher la valeur  d'une variable dans l'environnement *)
let rec chercher_val x env_val =
  match env_val with
  | [] -> failwith ("Variable non définie: " ^ x)  (* La variable n'est pas trouvée *)
  | c :: rest -> if x = c.var then c.valeur else chercher_val x rest  (* Si la variable est trouvée, on retourne son type, sinon on continue la recherche *)


let rec eval_expr env e typ_attendu=
  match e with
  | Var x -> chercher_val x env

  | Int x-> ValInt

  | Bool b-> chercher_val b env
  
  | BinaryOp (op, e1, e2) -> (
      match op with
      | Plus  -> 
          if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
          eval_expr env e1 TInt + eval_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)
      | Minus -> 
        if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
                eval_expr env e1 TInt - eval_expr env e2 TInt

      | Mult ->  if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
                 eval_expr env e1 TInt * eval_expr env e2 TInt
      | Div ->  if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier";
                eval_expr env e1 TInt / eval_expr env e2 TInt
      | And -> 
          if typ_attendu <> TBool then failwith "Une opération logique doit retourner un booléen";
          eval_expr env e1 TBool && eval_expr env e2 TBool  (* Les deux opérandes doivent être des booléens *)
        | Or -> 
          if typ_attendu <> TBool then failwith "Une opération logique doit retourner un booléen";
          eval_expr env e1 TBool || eval_expr env e2 TBool
      | Equal ->eval_expr env e1 typ_attendu = eval_expr env e2 typ_attendu
      | NEqual -> eval_expr env e1 typ_attendu <> eval_expr env e2 typ_attendu

      | Less -> 
          if typ_attendu <> TInt then failwith "Une comparaison doit retourner un booléen";
          eval_expr env e1 TInt < eval_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)
      | LessEq ->if typ_attendu <> TInt then failwith "Une comparaison doit retourner un booléen";
          eval_expr env e1 TInt <= eval_expr env e2 TInt
      | Great ->if typ_attendu <> TInt then failwith "Une comparaison doit retourner un booléen";
          eval_expr env e1 TInt > eval_expr env e2 TInt
      | GreatEq ->if typ_attendu <> TInt then failwith "Une comparaison doit retourner un booléen";
          eval_expr env e1 TInt >= eval_expr env e2 TInt
    )

  | UnaryOp (Not, e) -> match e with
      (*if typ_attendu <> TBool then failwith "L'opérateur 'not' doit retourner un booléen";*)
      |true->false
      |false->true
  | _ -> failwith "Erreur de typage"





let verif_decl_fun env fdecl =
  let params_val = {
    val_env = List.map (fun (x, t) -> (x, t)) fdecl.var_list; 
    fun_env = env.fun_env
  } in
  verif_expr params_env fdecl.corps fdecl.typ_retour *)
  
(* La fonction suivante récupère le nom de fichier passé en argument de la ligne de commande,
ouvre le fichier et applique l'analyse lexicale dessus, renvoyant une valeur de type Lexing.lexbuf *)
let get_lineBuffer () =
  (* Vérifie si le nom de fichier a été passé en argument *)
  if Array.length Sys.argv < 2 then
    failwith "Le nom de fichier à évaluer n'a pas été passé en argument."
  else
    try 
       (* Récupère le nom de fichier depuis les arguments de la ligne de commande *)
      let filename = Sys.argv.(1) in
      (* Ouvre le fichier en mode lecture *)
      let inBuffer = open_in filename in
      (* Crée un buffer lexical à partir du canal d'entrée *)
      Lexing.from_channel inBuffer
    with
    (* Gestion des erreurs système, par exemple si le fichier n'existe pas *)
    | Sys_error msg -> failwith ("Erreur : " ^ msg)
    (* Gestion des erreurs de syntaxe lors de l'analyse lexicale *)
    | Lexer.SyntaxError msg ->
        failwith ("Erreur de parsing dans le programme fourni en entrée :" ^ msg)
        (* Gestion des erreurs de syntaxe lors de l'analyse syntaxique *) 
    | Parser.Error ->
        failwith "Erreur de syntaxe dans le programme fourni en entrée."

        (* Point d'entrée principal du programme *)
let () =
  (* Récupère le buffer lexical à partir du fichier d'entrée *)
  let lineBuffer = get_lineBuffer () in
  try
    (* Analyse syntaxique du programme à partir du buffer lexical *)
    let prog = Parser.prog Lexer.token lineBuffer in
      (* Décommenter la ligne suivante pour afficher le programme analysé *)
    (* print_string (Syntax.string_of_programme prog); *)
    (* Vérifie le typage du programme *)
    (*print_string (Syntax.string_of_programme prog);*)
    let type_ok = Verif.verif_prog prog in
    if type_ok then 
      (* Évalue le programme si le typage est correct *)
      Evaluateur.eval_prog prog
    else 
       (* Signale une erreur de typage si le programme est mal typé *)
      failwith "Erreur de typage dans le programme fourni en entrée."
  with 
  (* Gestion des erreurs de syntaxe lors de l'analyse syntaxique *)
  Parser.Error ->
    failwith
      ("Erreur de syntaxe dans le programme fourni en entrée à la position "
      ^ string_of_int (Lexing.lexeme_start lineBuffer)) 

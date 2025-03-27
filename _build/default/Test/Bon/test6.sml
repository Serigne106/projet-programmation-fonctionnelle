let rec fact (n : int) : int =
  if n = 0 then 1 else n * fact (n - 1)

let main () : unit =
  print_int (fact 5)


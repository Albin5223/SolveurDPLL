open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :cc
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste 
   couou*)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
(* 
  Si clause contient i supprime la clause
  Si clause contient -i alors supprime les -i
*)
 let simplifie i clauses =
  let filter l = 
    if List.mem i l then None
    else 
      Some(let check x = if x <> (-i) then Some(x) else None in (filter_map check l)) 
  in filter_map filter (clauses)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* let () = print_modele (solveur_split exemple_7_2 []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

  let unitaire clauses = 
    let rec check l = match l with
      | [] -> raise Not_found
      | hd::tl -> match hd with
        | [hd] -> hd
        |  _ -> check tl
    in check clauses

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  let rec check l acc = match l with 
    | [] -> raise (Failure "Pas de littéral pur")
    | hd::tl -> 
      if not(List.mem(hd) acc || List.mem (-hd) acc) && not(List.mem(-hd) tl) then hd 
      else check tl (hd::acc)
  
  in check (List.flatten(clauses)) [] 

(* solveur_dpll_rec : int list list -> int list -> int list option *)
(* Idée: On simplifie en priorité par les littéraux unitaire ou pur, on ne simplifie pas par leur dual l barre *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  try let uni = unitaire(clauses) in solveur_dpll_rec (simplifie uni clauses)(uni::interpretation) with
    | Not_found ->
        try let pure = pur(clauses) in solveur_dpll_rec (simplifie pure clauses) (pure::interpretation) with
          | (Failure _ ) -> 
              let l = List.hd (List.hd clauses) in
              let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
              match branche with
                | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
                | _    -> branche
(* tests *)

(* let () = print_modele (solveur_dpll_rec exemple_7_2 []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

(** lib.ml -- utility functions and modules  *)

(* -------------------------------------------------------------------------- *)
(* Basic                                                                      *)
(* -------------------------------------------------------------------------- *)

let id x = x

let const x y = x

let ( % ) f g = fun x -> f (g x)

let flip f x y = f y x

let dup f x = f x x

let cross (f, g) (x, y) = (f x, g y)

let fork (f, g) x = (f x, g x)

let on f g = fun x y -> f (g x) (g y)

let uncurry f (x, y) = f x y

let curry f x y = f (x, y)

let pair x y = (x, y)

let triple x y z = (x, y, z)

let map_pair f (x, y) = (f x, f y)

let dup_pair x = (x, x)

let total f x = try Some (f x) with exn -> None

let partial e f x = match f x with Some y -> y | None -> raise e

let can f x = try (f x; true) with _ -> false

let check p x = if p x then x else failwith "check"

let check_opt p x = total (check p) x

let compare_with f = on compare f

let with_flag flag value f x =
  let old = !flag in
  let _ = flag := value in
  let res = try f x with e -> (flag := old; raise e) in
  ignore (flag := old); res


(* -------------------------------------------------------------------------- *)
(* Fixpoint combinator                                                        *)
(* -------------------------------------------------------------------------- *)

let rec fix f x = f (fix f) x

let memo_fix ?size =
  let size = match size with None -> 100 | Some s -> s in
  let rec fix table f x =
    if Hashtbl.mem table x then
      Hashtbl.find table x
    else
      let res = f (fix table f) x in
      Hashtbl.add table x res;
      res
  in fix (Hashtbl.create size)


(* -------------------------------------------------------------------------- *)
(* Functions on lists                                                         *)
(* -------------------------------------------------------------------------- *)

(* Bring commonly used functions to the top-level *)
let hd = List.hd
let tl = List.tl
let mem = List.mem
let map = List.map
let rev = List.rev
let zip = List.combine
let find = List.find
let flat = List.flatten
let assoc = List.assoc
let length = List.length
let forall = List.for_all
let exists = List.exists
let filter = List.filter
let filtermap = List.filter_map
let partition = List.partition

let filter_out p = filter (not % p)

let tabulate f n = List.init n f

let replicate n x = tabulate (const x) n

let foldl f acc xs = List.fold_left (flip f) acc xs

let foldr f acc xs = List.fold_right f xs acc

let is_nil = function [] -> true | _ -> false

let elem_of ls x = mem x ls

let rec last = function
  | [] -> failwith "last"
  | [e] -> e
  | _::t -> last t

let rec split_at n = function
  | [] -> ([],[])
  | h::t as ls ->
    if n = 0 then ([],ls)
    else let p,q = split_at (n-1) t in (h::p,q)

let rec no_duplicates = function
  | [] -> true
  | h::t -> not (List.exists ((=) h) t) && no_duplicates t

let is_unique = no_duplicates

(* let index n lst =
  let rec aux n c = function
    | [] -> raise Not_found
    | h::t -> if n=h then c else aux n (c+1) t
  in aux n 0 lst *)

let rec unzip ls =
  match ls with
  | [] -> ([], [])
  | (a,b) :: t -> let p,q = unzip t in (a::p, b::q)

let rec destutter ls =
  match ls with
  | h::(y::_ as t) -> let t' = destutter t in if h=y then t' else h::t'
  | _ -> ls

let nub xs =
  let rec aux ls acc =
    match ls with
    | [] -> []
    | h::t -> if mem h acc then aux t acc else h :: aux t (h :: acc)
  in aux xs []

let rec foldr1 f xs =
  match xs with
  | [] -> failwith "foldr1: empty list"
  | [h] -> h
  | h::t -> f h (foldr1 f t)

let rec foldl1 f xs =
  match xs with
  | [] -> failwith "foldl1: empty list"
  | h::t -> foldl f h t

let rec foldr2 f e xs ys =
  match xs, ys with
  | [], [] -> e
  | h1::t1, h2::t2 -> f h1 h2 (foldr2 f e t1 t2)
  | _ -> failwith "foldr2"

let rec foldl2 f e xs ys =
  match xs, ys with
  | [], [] -> e
  | h1::t1, h2::t2 -> foldl2 f (f h1 h2 e) t1 t2
  | _ -> failwith "foldl2"

let rec scanl f e ls =
  e :: match ls with [] -> [] | h::t -> scanl f (f e h) t

let rec scanr f e ls =
  match ls with
  | [] -> [e]
  | h::t -> let t' = scanr f e t in (f h (hd t')) :: t'

let interleave xs ys = foldr2 (fun x y t -> x::y::t) [] xs ys

let rec take n xs =
  match xs with
  | [] -> []
  | h::t -> if n <= 0 then [] else h :: take (n-1) t

let rec drop n xs =
  match xs with
  | [] -> []
  | h::t -> if n > 0 then drop (n-1) t else xs

let rec take_while p xs =
  match xs with
  | h::t when p h -> h :: take_while p t
  | _ -> []

let rec drop_while p xs =
  match xs with
  | h::t when p h -> drop_while p t
  | _ -> xs

let rec concat_map f xs =
  match xs with
  | [] -> []
  | h::t -> f h @ concat_map f t

let rec concat_filter_map f xs =
  match xs with
  | [] -> []
  | h::t ->
    let t' = concat_filter_map f t in
    match f h with None -> t' | Some h' -> h' @ t'

let rev_assoc b = find (fun (x,y) -> b = y)

let ucons x ls = if mem x ls then ls else x :: ls

let rec first f xs =
  match xs with
  | [] -> raise Not_found
  | h::t -> match f h with Some y -> y | None -> first f t

let first_opt f xs = total (first f) xs

let add_to_list ?(append=false) l e =
  if append then l := !l @ [e] else l := e :: !l

(* Set operations on lists *)
let union s1 s2 = foldr ucons s2 s1

let unions ss = foldr union [] ss

let intersect s1 s2 = filter (elem_of s2) s1

let diff s1 s2 = filter (not % elem_of s2) s1

let subset s1 s2 = forall (elem_of s2) s1

let set_eq s1 s2 = subset s1 s2 && subset s2 s1


(* -------------------------------------------------------------------------- *)
(* Functions on characters and strings                                        *)
(* -------------------------------------------------------------------------- *)

let uppercase = String.uppercase_ascii
let lowercase = String.lowercase_ascii

let enclose l r s = l ^ s ^ r

let parens = enclose "(" ")" and quote = enclose "\"" "\""

let explode s =
  let rec loop l n =
    if n = -1 then l
    else loop (s.[n] :: l) (n-1)
  in loop [] (String.length s - 1)

let implode l =
  let s = Bytes.create (List.length l) in
  let rec loop n = function
    | [] -> s
    | h::t -> Bytes.set s n h; loop (n+1) t
  in Bytes.to_string (loop 0 l)

let getchar str =
  let len = String.length str in
  if len = 0 then None
  else Some (str.[0], String.sub str 1 (len-1))

let print s = print_endline s

let warn msg = print ("[Warning]: " ^ msg)


(* -------------------------------------------------------------------------- *)
(* Applicative and Monad syntax for commonly used types                       *)
(* -------------------------------------------------------------------------- *)

module Option = struct
  include Stdlib.Option

  module Monad_syntax = struct
    let ( let* ) = bind

    let ( and* ) ma mb =
      match ma, mb with
      | Some a, Some b -> Some (a,b)
      | _, _ -> None
  end

  let return = some

  let ( <|> ) ma mb = if is_none ma then mb else ma

  let sequence (ma: 'a option list) : 'a list option =
    let open Monad_syntax in
    let seq h t = let* p = h and* q = t in return (p :: q)
    in foldr seq (some []) ma

  let map2 f x y =
    let open Monad_syntax in
    let* p = x in let* q = y in return (f p q)

  let guard b = if b then return () else None
end

module Result = struct
  include Stdlib.Result

  module Monad_syntax = struct
    let ( let* ) = bind

    let ( and* ) ma mb =
      match ma, mb with
      | Ok a, Ok b -> Ok (a,b)
      | Error m, _ | _, Error m -> Error m
  end

  let return a = Ok a

  let guard b msg = if b then ok () else Error msg

  let ( <|> ) ma mb = if is_error ma then mb else ma

  let sequence (ma: ('a,'b)result list) : ('a list,'b) result =
    let open Monad_syntax in
    let seq h t = let* p = h and* q = t in return (p :: q)
    in foldr seq (ok []) ma

  let map2 f x y =
    let open Monad_syntax in
    let* p = x in let* q = y in return (f p q)
end


(* -------------------------------------------------------------------------- *)
(* Functions to create Sets, Maps, and Hash tables                            *)
(* -------------------------------------------------------------------------- *)

module type Ordered = Set.OrderedType
module type Hashed  = Hashtbl.HashedType

let mk_ordered_type (type a) compare = (module struct
  type t = a
  let compare = compare
end : Ordered with type t = a)

let mk_hashed_type (type a) equal hash = (module struct
  type t = a
  let equal = equal
  let hash = hash
end : Hashed with type t = a)

let mk_set (type a) compare =
  let (module T : Ordered with type t = a) = mk_ordered_type compare in
  (module (Set.Make (T)) : Set.S with type elt = a)

let mk_map (type a) compare =
  let (module T : Ordered with type t = a) = mk_ordered_type compare in
  (module (Map.Make (T)) : Map.S with type key = a)

let mk_hashtbl (type a) equal hash =
  let (module T : Hashed with type t = a) = mk_hashed_type equal hash in
  (module (Hashtbl.Make (T)) : Hashtbl.S with type key = a)

let generic_hash = Hashtbl.hash

(* Example:
   module IS = (val mk_set Int.compare : Set.S with type elt = int)
   module IM = (val mk_map Int.compare : Map.S with type key = int) *)


(* -------------------------------------------------------------------------- *)
(* System utilities                                                           *)
(* -------------------------------------------------------------------------- *)

let get_progname () = Sys.argv.(0)

let open_file_or_exit fname =
  try open_in fname
  with Sys_error m ->
  Printf.fprintf stderr "%s: %s\n" (get_progname()) m;
  exit 1

let read_file fname =
  let fd = open_file_or_exit fname in
  let lines = ref [] in
  let rec loop () =
    match input_line fd with
    | l -> lines := l :: !lines; loop ()
    | exception End_of_file -> close_in fd
  in loop () ; String.concat "\n" (rev !lines)


(* -------------------------------------------------------------------------- *)
(* Miscellaneous functions                                                    *)
(* -------------------------------------------------------------------------- *)

let pp_as_string pp x =
  pp Format.str_formatter x;
  Format.flush_str_formatter ()

let time_it f x =
  let start = Sys.time () in
  let res = f x in
  let finish = Sys.time () in
  Printf.printf "Time: %F\n" (finish -. start);
  res

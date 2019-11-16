type wartosc =
  | Single of int
  | Range of int * int

type t =
  | Node of wartosc * t * t * int
  | Null

let height = function
  | Node (_, _, _, h) -> h
  | Null -> 0

let ( <. ) (x: wartosc) (y: wartosc) =
  match x, y with
  | Single(a), Single(b) -> a < b
  | Range(_, a), Single(b) -> a < b
  | Single(a), Range(b, _) -> a < b
  | Range(_, a), Range(b, _) -> a < b

let ( >. ) (x: wartosc) (y: wartosc) =
  match x, y with
  | Single(a), Single(b) -> a > b
  | Range(a, _), Single(b) -> a > b
  | Single(a), Range(_, b) -> a > b
  | Range(a, _), Range(_, b) -> a > b

let in_range (Single(a)) (y: wartosc) =
  match y with
  | Single(b) -> a = b
  | Range(c, d) -> c <= a && a <= d

let overlap (x: wartosc) (y: wartosc) =
  match x, y with
  | Single(a), Single(b) ->
    abs (a - b) <= 1
  | Range(a, b), Single(p) ->
    p >= a - 1 && p <= b + 1
  | Single(a), Range(p, q) ->
    a >= p - 1 && a <= q + 1
  | Range(a, b), Range(p, q) ->
    (a >= p - 1 && a <= q - 1) || (b >= p - 1 && b <= q - 1)

let merge (x: wartosc) (y: wartosc) =
  match x, y with
  | Single(a), Single(b) ->
    if a = b then Single(a)
    else Range(min a b, max a b)

  | Range(a, b), Single(p) ->
    Range(min a p, max b p)

  | Single(a), Range(p, q) ->
    Range(min a p, max a q)

  | Range(a, b), Range(p, q) ->
    Range(min a p, max b q)

let make (x, y) =
  if x = y then Single(x)
  else Range(x, y)

(** The empty set *)
let (empty: t) = Null

(** returns true if the set is empty. *)
let is_empty (x: t) =
  x = Null

(**  ---------------------DODAJ-BALANS--------------------- **)

(** [add (x, y) s] returns a set containing the same elements as [s],
    plus all elements of the interval [[x,y]] including [x] and [y].
    Assumes [x <= y]. *)
let add (x, y) (s: t) =
  let rec helper p drzewo =
    match drzewo with
    | Null -> (Node(p, Null, Null, 0), true)
    | Node( v, l, r, h) ->
      if overlap v p then (Node(merge v p, l, r, h), false)
      else if p <. v then
        let (a, b) = helper p l in
        if b then
          if abs (height a - height r) <= 1 then (Node(v, a, r, h + 1), false)
          else (*TEST*)(Node(v, a, r, h), false)
        else
          (Node(v, a, r, h), false)
      else
        let (a, b) = helper p r in
        if b then
          if abs (height a - height r) <= 1 then (Node(v, l, a, h + 1), false)
          else (*TEST*)(Node(v, l, a, h), false)
        else
          (Node(v, l, a, h), false)

  in let (Node(v, l, r, h), nowy) = helper (make (x, y)) s in
  if nowy then (Node(v, l, r, h + 1)) else Node(v, l, r, h)



(** [remove (x, y) s] returns a set containing the same elements as [s],
    except for all those which are included between [x] and [y].
    Assumes [x <= y]. *)

exception Found
(** [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)
let rec mem (x: int) (s: t) =
  let sx = Single(x) in
  try
    match s with
    | Null -> false
    | Node(v, l, r, h) ->
      if sx <. v then mem x l
      else if sx >. v then mem x r
      else if in_range sx v then raise(Found)
      else false
  with
  | Found -> true

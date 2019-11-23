(*--------------------------------Typy--------------------------------*)

(* Typ w wezlach drzewa *)
type wartosc =
  | Single of int       (* Pojedyncza wartosc *)
  | Range of int * int  (* Przedzial *)
  | Null                (* Pusty *)

(* Typ drzewa *)
type tree =
  | Node of tree * wartosc * tree * int   (* lewe, wartosc wezla, prawe, wysokosc *)
  | Empty

(* zbior drzew z operatorem porownania *)
type t =
  {
    cmp : wartosc -> wartosc -> int;
    set : tree;
  }

(*--------------------------------Funkcje pomocnicze--------------------------------*)

(*---------------------Funkcje do wartosci---------------------*)
let print_wartosc = function
  | Single(x) -> print_int (x)
  | Range(x, y) -> print_string ("<"); print_int (x); print_string(" ,"); print_int (y); print_string ("> ")
  | Null -> print_string("<Null> ")

let left = function
  | Node (l, _, _, _) -> l
  | Empty -> Empty

let value = function
  | Node (_, x, _, _) -> x
  | Empty -> Null

let right = function
  | Node (_, _, r, _) -> r
  | Empty -> Empty

let height = function
  | Node (_, _, _, h) -> h
  | Empty -> 0

(* Porownanie wartosci *)
let compare_wartosc (x: wartosc) (y: wartosc) =
  match x, y with
  | _, Null -> assert false
  | Null, _ -> assert false
  | Single(a), Single(c) ->
    if a > c then 1
    else if a = c then 0
    else -1
  | Single(a), Range(c, d) ->
    if a > d then 1
    else if a >= c && a <= d then 0
    else -1
  | Range(a, b), Single(c) ->
    if a > c then 1
    else if a <= c && c <= b then 0
    else -1
  | Range(a, b), Range(c, d) ->
    if a > d then 1
    else if b < c then -1
    else 0

(* Czy wartosci nachodza na siebie aby je polaczyc *)
let overlap (x: wartosc) (y: wartosc) =
  match x, y with
  | Null, _ -> false
  | _, Null -> false
  | Single(a), Single(b) ->
    if b = max_int then
      a >= max_int - 1
    else if b = min_int then
      a <= min_int + 1
    else
      a >= b - 1 && a <= b + 1

  | Range(a, b), Single(p) ->
    if p = max_int then
      b >= max_int -1
    else if p = min_int then
      a <= min_int + 1
    else
      p + 1 >= a && p - 1 <= b

  | Single(a), Range(p, q) ->
    if a = max_int then
      q >= max_int - 1
    else if a = min_int then
      p <= min_int + 1
    else
      a + 1 >= p && a - 1 <= q

  | Range(a, b), Range(p, q) ->

    if a = min_int && b = max_int then true
    else if a = max_int then
      q >= max_int - 1
    else if a = min_int then
      p <= b + 1
    else if b = max_int then
      q >= a - 1
    else if b = min_int then
      p <= min_int + 1
    else
      (a + 1 >= p && a - 1 <= q ) || (b + 1 >= p  && b - 1 <= q ) || (a <= p && b >= q)

(* Konstruktor *)
let make_wartosc (x, y) =
  if x = y then Single(x)
  else if x < y then Range(x, y)
  else Null

let break_wartosc (x: wartosc) =
  match x with
  | Null -> assert false
  | Single(a) -> (a, a)
  | Range(a, b) -> (a, b)

(* Odejmnowanie wartosci *)
let remove_wartosc (x: wartosc) (y: wartosc) =
  match x, y with
  | _, Null -> assert false
  | Null, _ -> assert false
  | Single(a), Single(c) ->
    (Null, Null)
  | Single(a), Range(c, d) ->
    if a = min_int then
      make_wartosc (c + 1, d), Null
    else if a = max_int then
      make_wartosc (c, d - 1), Null
    else
      make_wartosc (c, a - 1), make_wartosc (a + 1, d)
  | Range(a, b), Single(c) ->
    (Null, Null)
  | Range(a, b), Range(c, d) ->
    if a = min_int && b = max_int then Null, Null
    else if a = min_int then
      make_wartosc (b + 1, d), Null
    else if b = max_int then
      make_wartosc (c, a - 1), Null
    else
      make_wartosc (c, a - 1), make_wartosc (b + 1, d)

(* Laczenie wartosci *)
let merge_wartosc (x: wartosc) (y: wartosc) =
  match x, y with
  | a, Null -> a
  | Null, a -> a
  | Single(a), Single(b) ->
    if a = b then Single(a)
    else Range(min a b, max a b)

  | Range(a, b), Single(p) ->
    Range(min a p, max b p)

  | Single(a), Range(p, q) ->
    Range(min a p, max a q)

  | Range(a, b), Range(p, q) ->
    Range(min a p, max b q)

(* moze jakies rzeczy z max bla bla*)
let wartosc_length (w: wartosc) =
  match w with
  | Null -> assert false
  | Single(_) -> 1
  | Range(a, b) ->
      if b - a + 1 <= 0 then max_int
      else b - a + 1
      (* if a >= 1 then b - a + 1
      else if b <= -2 then b - a + 1
      else if a = 0 then b
      else if b <= -1 then b - a + 1
        let da = -1 - a
        and db = b - 1 in
        if da = max_int || db = max_int then max_int
        else if da >= max_int - db - 3 then max_int
        else da + db +  *)

(*---------------------Funkcje do drzew---------------------*)

let rec print_tree = function
  | Empty -> print_string ("(Empty) ")
  | Node (l, k, r, h) ->
    print_string ("("); print_tree l; print_wartosc k; print_tree r; print_int (h); print_string (") ")

let make l (k: wartosc) r = Node (l, k, r, max (height l) (height r) + 1)

let bal l (k: wartosc) r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1)

let rec min_elt = function
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt = function
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

let rec add_one cmp (x: wartosc) (t: tree) =
  let rec loop stan = function
    | Node (l, k, r, h) ->
        let c = cmp x k
        and c1 = overlap x k in

        if c1 = true then

          let l_loop = loop true l in
          let r_loop = loop true r in
          (* print_string("-----"); print_tree l_loop; print_tree r_loop; print_string ("\n\n");
          print_wartosc (value l_loop); print_wartosc (k); print_wartosc( value r_loop); print_string("-----\n\n"); *)

          if overlap (value l_loop) k && overlap (value r_loop) k then
            (* let _ = print_string("1 if\t\t") in *)
            (* Node (Empty, merge_wartosc (value r_loop) (merge_wartosc (value l_loop) k), Empty, 1) *)
            make (merge (left l_loop) (right l_loop)) (merge_wartosc (value r_loop) (merge_wartosc (value l_loop) k)) (merge (left r_loop) (right r_loop))
          else if overlap (value l_loop) k then
            (* let _ = print_string("2 if\t\t") in *)
            (* Node (merge (left l_loop) (right l_loop), merge_wartosc x (merge_wartosc (value l_loop) k), r, height r + 1) *)
            make (merge (left l_loop) (right l_loop)) (merge_wartosc x (merge_wartosc (value l_loop) k)) r
          else if overlap (value r_loop) k then
            (* let _ = print_string("3 if\t\t") in *)
            make l (merge_wartosc x (merge_wartosc (value r_loop) k)) (merge (left r_loop) (right r_loop))
            (* Node (l, merge_wartosc x (merge_wartosc (value r_loop) k), merge (left r_loop) (right r_loop), height l + 1) *)
          else
            (* let _ = print_string("4 if\t\t") in *)
            make l (merge_wartosc x k) r
            (* Node (l, merge_wartosc x k, r, h) *)

        else if c < 0 then
          let nl = loop stan l in
          bal nl k r
        else
          let nr = loop stan r in
          bal l k nr
    | Empty ->
        if stan then Empty
        else Node (Empty, x, Empty, 1)
  in loop false t

let rec join cmp l v r =
  match (l, r) with
    (Empty, _) -> add_one cmp v r
  | (_, Empty) -> add_one cmp v l
  | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
      if lh > rh + 2 then bal ll lv (join cmp lr v r) else
      if rh > lh + 2 then bal (join cmp l v rl) rv rr else
      make l v r

(*--------------------------------Funkcje z zadania--------------------------------*)

(** The empty set *)
let (empty: t) = { cmp = compare_wartosc; set = Empty }

(** returns true if the set is empty. *)
let is_empty x =
  x.set = Empty

(** [add (x, y) s] returns a set containing the same elements as [s],
    plus all elements of the interval [[x,y]] including [x] and [y].
    Assumes [x <= y]. *)
let add (x, y) { cmp = cmp; set = set } =
  { cmp = cmp; set = add_one cmp (make_wartosc (x,y)) set }

(** [remove (x, y) s] returns a set containing the same elements as [s],
    except for all those which are included between [x] and [y].
    Assumes [x <= y]. *)
let remove (a, b) { cmp = cmp; set = set } =
  let x = make_wartosc (a, b) in
  let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        if c = 0 then


          let l_loop = loop l in
          let r_loop = loop r in
          (* print_tree l_loop; print_tree r_loop; print_string ("\n\n"); *)
          (* na pewno nie laczymy bo by sie wczesniej polaczylo *)

          (* (make Empty res2 Empty) (merge l r)
            (add res1 { cmp = cmp; set = (merge l r) }).set *)
          match remove_wartosc x k with
          | Null, Null -> merge l_loop r_loop
          | Null, res2 -> join cmp l_loop res2 r_loop
            (* merge (make Empty res2 Empty) (merge l_loop r_loop) *)
          | res1, Null -> join cmp l_loop res1 r_loop
            (* merge (make Empty res1 Empty) (merge l_loop r_loop) *)
          | res1, res2 ->
            (* merge (make Empty res2 Empty) (merge (merge l_loop r_loop) (make Empty res1 Empty)) *)
             add_one cmp res1 (join cmp l_loop res2 r_loop) (* XDDDD zamienilem res1 z res2 miejscami i dziala xd *)

        else
        if c < 0 then bal (loop l) k r else bal l k (loop r)
    | Empty -> Empty in
  { cmp = cmp; set = loop set }

(** [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)
let mem (a: int) { cmp = cmp; set = set } =
  let rec loop x = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        c = 0 || loop x (if c < 0 then l else r)
    | Empty -> false in
  loop (make_wartosc (a, a)) set

(** [iter f s] applies [f] to all continuous intervals in the set [s].
    The intervals are passed to [f] in increasing order. *)
let iter f { set = set } =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _) -> loop l; f (break_wartosc k); loop r
  in loop set

(** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], where x1
    ... xN are all continuous intervals of s, in increasing order. *)
let fold f { cmp = cmp; set = set } acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _) ->
        loop (f (break_wartosc k) (loop acc l)) r
  in loop acc set

(** Return the list of all continuous intervals of the given set.
    The returned list is sorted in increasing order. *)
let elements { set = set } =
  let rec loop acc = function
    | Empty -> acc
    | Node(l, k, r, _) -> loop ((break_wartosc k) :: loop acc r) l in
  loop [] set

(** [below n s] returns the number of elements of [s] that are lesser
    or equal to [n]. If there are more than max_int such elements,
    the result should be max_int. *)
let below (n: int) { cmp = cmp; set = set } =
  let safe_sum cr cl v =
    if cr = max_int || cl = max_int || v = max_int then max_int
    else if cr >= max_int - cl - v then max_int
    else cr + cl + v in

  let rec loop = function
    | Empty -> 0
    | Node(l, k, r, _) ->
      let c = cmp (make_wartosc (n, n)) k in

      if c < 0 then
        loop l
      else if c = 0 then
        let (a, _) = break_wartosc k in

        safe_sum (loop r) (loop l) (wartosc_length (make_wartosc (a, n)))

      else (* c > 0 *)
        safe_sum (loop r) (loop l) (wartosc_length k)

  in loop set

(** [split x s] returns a triple [(l, present, r)], where
    [l] is the set of elements of [s] that are strictly lesser than [x];
    [r] is the set of elements of [s] that are strictly greater than [x];
    [present] is [false] if [s] contains no element equal to [x],
    or [true] if [s] contains an element equal to [x]. *)
let split a { cmp = cmp; set = set } =
  let x = Single(a) in
  let rec loop x = function
    | Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0 then

      (*(merge (make Empty res1 Empty) l, true, r)
      (merge (make Empty res1 Empty) l, true, merge (make Empty res2 Empty) r)*)

          match remove_wartosc x v with
            | Null, Null -> (l, true, r)
            | Null, res2 -> (l, true, add_one cmp res2 r)
            | res1, Null -> (add_one cmp res1 l, true, r)
            | res1, res2 -> (add_one cmp res1 l, true, add_one cmp res2 r)

        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  { cmp = cmp; set = setl }, pres, { cmp = cmp; set = setr }

(*
** An implementation of substitution, normalization via beta-reduction, and a
** simple implementation of type inference (NOT elaboration; in other words,
** all lambdas are type-annotated) for dependent types.
**
** The code here is largely adapated from the following article:
**   http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/
** except retrofitted to work with de bruijn indices, and a (possibly naiive?)
** implementation of cumulative universes.
**
** This version is written in Amulet: https://amulet.works/
*)

include import "prelude.ml"

(*
** Core
*)

type nam <- string
type exp_t 't =                                      (* D ::=            *)
  | Ref of nam                                       (* | x              *)
  | Idx of 't                                        (* | #              *)
  | Lam of nam      * exp_t 't * exp_t 't            (* | λx: D. D       *)
  | App of exp_t 't * exp_t 't                       (* | D D            *)
  | Pi  of nam      * exp_t 't * exp_t 't            (* | Πx: D. D       *)
  | Unv of int                                       (* | U0, U1, U2, ...*)
  | Tup of nam      * exp_t 't * exp_t 't * exp_t 't (* | (x : D = D, D) *)
  | Sgm of nam      * exp_t 't * exp_t 't            (* | Σx: D. D       *)
type exp <- exp_t int

(*
** Typeclass Instances
*)

instance eq 't => eq (exp_t 't) begin
  let a == b =
    match a, b with
    | Ref a, Ref b -> a == b
    | Idx a, Idx b -> a == b
    | Lam (an, at, ae), Lam (bn, bt, be) -> an == bn && at == bt && ae == be
    | App (a, b), App (c, d) -> a == c && b == d
    | Pi (an, at, ae), Pi (bn, bt, be) -> an == bn && at == bt && ae == be
    | Unv a, Unv b -> a == b
    | Tup (an, at, aa, ab), Tup (bn, bt, ba, bb) ->
      an == bn && at == bt && aa == ba && ab == bb
    | Sgm (an, at, ae), Sgm (bn, bt, be) -> an == bn && at == bt && ae == be
    | _, _ -> false
end

instance show 'a => show (exp_t 'a) begin
  let show = function
    | Ref n         -> n
    | Idx i         -> show i
    | Lam (_, t, e) -> "\\" ^ show t ^ "]. " ^ show e
    | App (a, b)    -> "(" ^ show a ^ ") " ^ show b
    | Pi (_, t, e)  -> "^" ^ show t ^ ". " ^ show e
    | Unv u         -> "Set" ^ show u
    | Tup (_, t, a, b) -> "(" ^ show a ^ ": " ^ show t ^ ", " ^ show b ^ ")"
    | Sgm (_, t, e) -> "&" ^ show t ^ ". " ^ show e
end

instance functor exp_t begin
  let f <$> e =
    match e with
    | Ref n            -> Ref n
    | Idx i            -> Idx (f i)
    | Lam (n, t, e)    -> Lam (n, f <$> t, f <$> e)
    | App (a, b)       -> App (f <$> a, f <$> b)
    | Pi (n, t, e)     -> Pi  (n, f <$> t, f <$> e)
    | Unv u            -> Unv u
    | Tup (n, t, a, b) -> Tup (n, f <$> t, f <$> a, f <$> b)
    | Sgm (n, t, e)    -> Sgm (n, f <$> t, f <$> e)
end

(*
** Substitution
*)

let subst_var k w i =
  if i == k then
    w
  else if i > k then
    Idx (i - 1)
  else
    Idx i

let rec subst_raw k w = function
  | Ref n            -> Ref n
  | Idx i            -> subst_var k w i
  | Lam (n, t, e)    -> Lam (n, subst_raw k w t, subst_raw (k + 1) w e)
  | App (a, b)       -> App (subst_raw k w a, subst_raw k w b)
  | Pi (n, t, e)     -> Pi  (n, subst_raw k w t, subst_raw (k + 1) w e)
  | Unv u            -> Unv u
  | Tup (n, t, a, b) ->
    Tup (n, subst_raw k w t, subst_raw k w a, subst_raw (k + 1) w b)
  | Sgm (n, t, e)    -> Sgm (n, subst_raw k w t, subst_raw (k + 1) w e)
let subst = subst_raw 0

(*
** Normalization
*)

type gam <- (list exp, list (nam * (exp * option exp)))
let gempty = ([], [])

let rec norm (s, m) = function
  | Ref n ->
    match lookup n m with
    | Some (_, Some x) -> Right x
    | Some (_, None)   -> Right @@ Ref n
    | None -> Left @@ "Unknown identifier: " ^ n
  | Idx i -> Right @@ Idx i
  | Lam (n, t, e) -> begin
      with t' <- norm (s, m) t
      with e' <- norm (s, m) e
      Right @@ Lam (n, t', e')
    end
  | App (a, b) -> begin
      with a' <- norm (s, m) a
      with b' <- norm (s, m) b
      Right @@ App (a', b')
    end
  | Pi (n, t, e) -> begin
      with t' <- norm (s, m) t
      with e' <- norm (s, m) e
      Right @@ Pi (n, t', e')
    end
  | Unv u -> Right @@ Unv u
  | Tup (n, t, a, b) -> begin
      with t' <- norm (s, m) t
      with a' <- norm (s, m) a
      with b' <- norm (s, m) b
      Right @@ Tup (n, t', a', b')
    end
  | Sgm (n, t, e) -> begin
      with t' <- norm (s, m) t
      with e' <- norm (s, m) e
      Right @@ Sgm (n, t', e')
    end

(*
** Type Inference + Checking
*)

let passes a b =
  match a, b with
  | Unv a, Unv b -> a <= b
  | a, b -> a == b

let check_passes a b =
  if passes a b then
    Right ()
  else
    Left @@ "Attempt to pass " ^ show a ^ " as " ^ show b

let rec infer (s, m) = function
  | Ref n ->
    match lookup n m with
    | Some (t, _) -> Right t
    | None -> Left @@ "Unknown identifier: " ^ n
  | Idx i ->
    if i < length s then
      Right @@ (+ (i + 1)) <$> nth i s
    else
      Left @@ "Index out of bounds: " ^ show i
  | Lam (n, t, e) -> begin
      with t' <- norm (s, m) t
      with _ <- infer_unv (s, m) t'
      with et <- infer (t' :: s, m) e
      Right @@ Pi (n, t', et) 
    end
  | App (a, b) -> begin
      with a' <- norm (s, m) a
      with (_, t, e) <- infer_pi (s, m) a'
      with b' <- norm (s, m) b
      with bt <- infer (s, m) b'
      with _ <- check_passes bt t
      Right @@ subst b' e
    end
  | Pi (_, t, e) -> begin
      with t' <- norm (s, m) t
      with tu <- infer_unv (s, m) t'
      with eu <- infer_unv (t' :: s, m) e
      Right @@ Unv @@ (if tu > eu then tu else eu)
    end
  | Unv u -> Right @@ Unv (u + 1)
  | Tup (x, t, a, b) -> begin
      with t' <- norm (s, m) t
      with _ <- infer_unv (s, m) t'
      with at <- infer (s, m) a
      with _ <- check_passes at t'
      with bt <- infer (s, m) b
      Right @@ Sgm (x, t', bt)
    end
  | Sgm (_, t, e) -> begin
      with t' <- norm (s, m) t
      with e' <- norm (s, m) e
      with tu <- infer_unv (s, m) t'
      with eu <- infer_unv (s, m) e'
      Right @@ Unv @@ (if tu > eu then tu else eu)
    end
and infer_unv (s, m) e = begin
    with t <- infer (s, m) e
    with t' <- norm (s, m) t
    match t' with
    | Unv u -> Right u
    | _ -> Left "Expected type."
  end
and infer_pi (s, m) e = begin
    with t <- infer (s, m) e
    with t' <- norm (s, m) t
    match t' with
    | Pi (n, t, e) -> Right (n, t, e)
    | _ -> Left "Expected function."
  end


let lam x t e = Lam (x, t, e)
let pit x t e = Pi (x, t, e)
let app a b = App (a, b)

let eid =
  lam "t" (Unv 1) (
    lam "x" (Idx 0) (
      Idx 0
    )
  )

let edollar =
  lam "t" (Unv 1) (
    lam "f" (pit "ft" (Idx 0) (Idx 1)) (
      lam "x" (Idx 1) (
        app (Idx 1) (Idx 0)
      )
    )
  )

let test n e =
  put_line @@ " -- " ^ n ^ " --"
  put_line @@ "Raw:  " ^ show e
  put_line @@ "Norm: " ^ (show @@ from_right e @@ infer gempty e)

let () =
  test "$" edollar
  test "$ Unv 0" (app edollar (Unv 0))
  test "id" eid
  test "id Unv 0" (app eid (Unv 0))

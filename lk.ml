
type ('a, 'e) result = Ok of 'a | Err of 'e

let (let*) x k = match x with Ok y -> k y | Err e -> Err e

let ( *> ) m1 m2 = let* _ = m1 in m2

(* Types

τ ∷= 0 | 1
   | τ + ..
   | τ × ..
   | σ → τ
   | ¬ τ

*)
type ty
  = Void | Unit
  | Sum of ty list
  | Prod of ty list
  | Neg of ty
  | Vdash of ty list * ty list
  | TVar of int
  | Mu of int * ty

(* τ[σ/x] *)
let rec ty_subst t s x =
  let go t = ty_subst t s x in
  match t with
  | Void -> Void
  | Unit -> Unit
  | Sum ts -> Sum (List.map go ts)
  | Prod ts -> Prod (List.map go ts)
  | Neg t -> Neg (go t)
  | Vdash (ss, ts) -> List.(Vdash (map go ss, map go ts))
  | TVar x' as t -> if x = x' then s else t
  | Mu (x', t') as t -> if x = x' then t else Mu (x', go t')

(* Typing contexts: Γ, Δ ∷= · | Γ, x : τ *)

type var = Var of int
type covar = Covar of int

type 'a ctx = 'a -> (ty, [`NotFound]) result
let empty : 'a ctx = fun _ -> Err `NotFound
let extend (x : 'a) (t : ty) (c : 'a ctx) : 'a ctx =
  fun x' -> if x = x' then Ok t else c x'

let extends (vs : 'a list) (ts : ty list) (vts : 'a ctx) : 'a ctx =
  let open List in
  fold_right (fun (v, t) vts -> extend v t vts) (combine vs ts) vts

(* Terms *)

type exp
  (* Variables
     | [k]x
     | let x : τ = κ k. e₁ in e₂ *)
  = Axiom of covar * var
  | Cut of ty * covar * exp * var * exp
  (* Unit and zero
     | absurd x
     | [k]★ *)
  | Absurd of var
  | Trivial of covar
  (* Products
     | [k](κ h. e, ..)
     | let (y, ..) = x in e *)
  | Tuple of covar * (covar * exp) list
  | Untuple of var list * var * exp
  (* Sums
     | let [j, ..] = k in e
     | case x of y -> e | .. end *)
  | Uncase of covar list * covar * exp
  | Case of var * (var * exp) list
  (* Negation
     | let x -> k in e
     | let x <- k in e *)
  | ToCo of var * covar * exp
  | OfCo of var * covar * exp
  (* Sequents
     | [k](λ x .. . κ j .. . e)
     | case x (κ k. e₁) .. of (λ y. e₂) .. end *)
  | LK of covar * var list * covar list * exp
  | LKApp of var * (covar * exp) list * (var * exp) list
  (* Recursive types
     | [k](κ j. roll e)
     | let y = unroll x in e *)
  | Roll of covar * covar * exp
  | Unroll of var * var * exp

(* Typing *)

let find_var x vars =
  match vars x with
  | Err `NotFound -> Err (`NoVar x)
  | Ok t -> Ok t

let find_covar k covars =
  match covars k with
  | Err `NotFound -> Err (`NoCovar k)
  | Ok t -> Ok t

let as_unit m =
  let* ty = m in
  match ty with
  | Unit -> Ok ()
  | _ -> Err (`ExGot ("1", ty))

let as_prod m =
  let* ty = m in
  match ty with
  | Prod ts -> Ok ts
  | _ -> Err (`ExGot ("_ × ..", ty))

let as_sum m =
  let* ty = m in
  match ty with
  | Sum ts -> Ok ts
  | _ -> Err (`ExGot ("_ + ..", ty))

let as_neg m =
  let* ty = m in
  match ty with
  | Neg t -> Ok t
  | _ -> Err (`ExGot ("¬ _", ty))

let as_vdash m =
  let* ty = m in
  match ty with
  | Vdash (ss, ts) -> Ok (ss, ts)
  | _ -> Err (`ExGot ("_ ⊢ _", ty))

let as_mu m =
  let* ty = m in
  match ty with
  | Mu (a, t) -> Ok (a, t)
  | _ -> Err (`ExGot ("μ _. _", ty))

let fresh =
  let x = ref (-1) in
  let fresh () =
    x := !x + 1;
    !x
  in fresh

let mapM_ f xs = List.fold_left (fun m x -> m *> f x) (Ok ()) xs

(* Γ ⊢ e ⊣ Δ *)
let rec check (vars : var ctx) (e : exp) (covars : covar ctx) =
  match e with
  (* Axiom (context lookup)
       
    ——————————————————————————
    Γ, x : τ ⊢ [k]x ⊣ k : τ, Δ
 
       Γ ⊢ [k]x ⊣ Δ
    ——————————————————— x ≠ y
    Γ, y : τ ⊢ [k]x ⊣ Δ
 
       Γ ⊢ [k]x ⊣ Δ
    ——————————————————— j ≠ k
    Γ ⊢ [k]x ⊣ j : τ, Δ       *)
  | Axiom (k, x) ->
    let* t = find_var x vars in
    let* t' = find_covar k covars in
    if t = t' then Ok () else Err (`Mismatch (t, t'))
  (* Γ ⊢ e₁ ⊣ k : τ, Δ    Γ, x : τ ⊢ e₂ ⊣ Δ
     ——————————————————————————————————————
        Γ ⊢ cut (κ k. e₁) (λ x. e₂) ⊣ Δ      *)
  | Cut (t, k, e1, x, e2) ->
    check vars e1 (extend k t covars) *>
    check (extend x t vars) e2 covars
  (*
    ——————————————————    ——————————————
    x : 0 ⊢ absurd x ⊣    ⊢ [k]★ ⊣ k : 1 *)
  | Absurd x -> Ok ()
  | Trivial k -> as_unit (find_covar k covars)
  (*       Γ ⊢ e ⊣ j : τ, Δ    ..
     ———————————————————————————————————
     Γ ⊢ [k](κ j. e, ..) ⊣ k : τ × .., Δ *)
  | Tuple (k, jes) ->
    let* ts = as_prod (find_covar k covars) in
    let open List in
    if length jes <> length ts then Err (`TupleArity (jes, ts)) else
    mapM_ (fun ((j, e), t) -> check vars e (extend j t covars)) (combine jes ts)
  (*           Γ, y : τ, .. ⊢ e ⊣ Δ
     ————————————————————————————————————————
     Γ, x : τ × .. ⊢ let (y, ..) = x in e ⊣ Δ *)
  | Untuple (ys, x, e) ->
    let* ts = as_prod (find_var x vars) in
    if List.(length ys <> length ts) then Err (`UntupleArity (ys, ts)) else
    check (extends ys ts vars) e covars
  (*           Γ ⊢ e ⊣ j : τ, .., Δ
     ————————————————————————————————————————
     Γ ⊢ let [j, ..] = k in e ⊣ k : τ + .., Δ *)
  | Uncase (js, k, e) ->
    let* ts = as_sum (find_covar k covars) in
    if List.(length js <> length ts) then Err (`UncaseArity (js, ts)) else
    check vars e (extends js ts covars)
  (*          Γ, y : τ ⊢ e ⊣ Δ    ..
     —————————————————————————————————————————
     Γ, x : τ + .. ⊢ case x of y -> e | .. end *)
  | Case (x, yes) ->
    let* ts = as_sum (find_var x vars) in
    let open List in
    if length yes <> length ts then Err (`CaseArity (yes, ts)) else
    mapM_ (fun ((y, e), t) -> check (extend y t vars) e covars) (combine yes ts)
  (*         Γ ⊢ e ⊣ k : τ, Δ
     ————————————————————————————————
     Γ, x : ¬ τ ⊢ let x -> k in e ⊣ Δ *)
  | ToCo (x, k, e) ->
    let* t = as_neg (find_var x vars) in
    check vars e (extend k t covars)
  (*         Γ, x : τ ⊢ e ⊣ Δ
     ————————————————————————————————
     Γ ⊢ let x <- k in e ⊣ k : ¬ τ, Δ *)
  | OfCo (x, k, e) ->
    let* t = as_neg (find_covar k covars) in
    check (extend x t vars) e covars
  (*            Γ, x : σ, .. ⊢ e ⊣ j : τ, .., Δ
     —————————————————————————————————————————————————————
     Γ ⊢ [k](λ x .. . κ j .. . e) ⊣ k : (σ, .. ⊢ τ, ..), Δ *)
  | LK (k, xs, js, e) ->
    let* (ss, ts) = as_vdash (find_covar k covars) in
    let open List in
    if length xs <> length ss then Err (`LKArgArity (xs, ss)) else
    if length js <> length ts then Err (`LKContArity (js, ts)) else
    check (extends xs ss vars) e (extends js ts covars)
  (*          Γ ⊢ e₁ ⊣ k : σ, Δ    ..    Γ, y : τ ⊢ e₂ ⊣ Δ    ..
     ————————————————————————————————————————————————————————————————————
     Γ, x : (σ, .. ⊢ τ, ..) ⊢ case x (κ k. e₁) .. of (λ y. e₂) .. end ⊣ Δ *)
  | LKApp (x, kes, yes) ->
    let* (ss, ts) = as_vdash (find_var x vars) in
    let open List in
    if length kes <> length ss then Err (`LKAppArgArity (kes, ss)) else
    if length yes <> length ts then Err (`LKAppContArity (yes, ts)) else
    mapM_ (fun ((k, e), s) -> check vars e (extend k s covars)) (combine kes ss) *>
    mapM_ (fun ((y, e), t) -> check (extend y t vars) e covars) (combine yes ts)
  (*      Γ ⊢ e ⊣ j : τ[μ α. τ/α], Δ
     ————————————————————————————————————
     Γ ⊢ [k](κ j. roll e) ⊣ k : μ α. τ, Δ *)
  | Roll (k, j, e) ->
    let* (a, t) = as_mu (find_covar k covars) in
    check vars e (extend j (ty_subst t (Mu (a, t)) a) covars)
  (*        Γ, y : τ[μ α. τ/α] ⊢ e ⊣ Δ
     —————————————————————————————————————————
     Γ, x : μ α. τ ⊢ let y = unroll x in e ⊣ Δ *)
  | Unroll (y, x, e) ->
    let* (a, t) = as_mu (find_var x vars) in
    check (extend y (ty_subst t (Mu (a, t)) a) vars) e covars

(* Conversion to lambda calculus *)

type lc
  = LVar of string
  | Lam of string * lc
  | App of lc * lc
  | LTrivial
  | LAbsurd of lc
  | In of int * lc
  | LCase of lc * (string * lc) list
  | LTuple of lc list
  | LUntuple of string list * lc * lc
  | LRoll of lc
  | LUnroll of lc

let s_x (Var x) = "x" ^ string_of_int x
let s_k (Covar k) = "k" ^ string_of_int k
let c_x x = LVar (s_x x)
let c_k k = LVar (s_k k)

let ( $ ) e1 e2 = App (e1, e2)
let vlam ve = let v = "v" ^ string_of_int (fresh ()) in Lam (v, ve (LVar v))
let xlam (Var x) e = Lam ("x" ^ string_of_int x, e)
let klam (Covar k) e = Lam ("k" ^ string_of_int k, e)

let rec c_exp : exp -> lc = function
  (* [[ [k]x ]] = k x *)
  | Axiom (k, x) -> c_k k $ c_x x
  (* [[ cut (κ k. e₁) (λ x. e₂) ]] = (λ k. [[e₁]]) (λ x. [[e₂]]) *)
  | Cut (_, k, e1, x, e2) -> klam k (c_exp e1) $ xlam x (c_exp e2)
  (* [[ [k]★ ]] = k ★ *)
  | Trivial k -> c_k k $ LTrivial
  (* [[ absurd x ]] = case x of end *)
  | Absurd x -> LAbsurd (c_x x)
  (* [[ [k](κ j. e, ..) ]] = (λ j. [[e]]) (λ v. .. (λ .. . k (v, ..))) *)
  | Tuple (k, jes) ->
    let open List in
    let vs = map (fun _ -> fresh ()) jes in
    fold_left
      (fun res (j, e) -> res $ Lam (s_k j, c_exp e))
      (c_k k $ LTuple (map (fun v -> LVar (s_x (Var v))) vs)) jes
  (* [[ let (y, ..) = x in e ]] = let (y, ..) = x in [[e]] *)
  | Untuple (ys, x, e) -> LUntuple (List.map s_x ys, c_x x, c_exp e)
  (* [[ let [j, ..] = k in e ]] = (λ j .. . [[e]]) (λ v. k (ι₁ v)) .. *)
  | Uncase (js, k, e) ->
    let open List in
    snd (fold_left
      (fun (n, e) j -> (n + 1, e $ vlam (fun v -> c_k k $ In (n, v))))
      (0, fold_right klam js (c_exp e))
      js)
  (* [[ case x of y -> e | .. end ]] = case x of ι₁ y -> [[e]] | .. end *)
  | Case (x, yes) -> LCase (c_x x, List.map (fun (y, e) -> (s_x y, c_exp e)) yes)
  (* [[ let x -> k in e ]] = (λ k. [[e]]) x *)
  | ToCo (x, k, e) -> klam k (c_exp e) $ c_x x
  (* [[ let x <- k in e ]] = k (λ x. [[e]]) *)
  | OfCo (x, k, e) -> c_k k $ xlam x (c_exp e)
  (* [[ [k](λ x .. . κ j .. . e) ]] = k (λ x .. j .. . [[e]]) *)
  | LK (k, xs, js, e) -> let open List in c_k k $ fold_right xlam xs (fold_right klam js (c_exp e))
  (* [[ case x (κ k. e₁) .. of y -> e₂ | .. end ]] = (λ k. [[e₁]]) (λ v. .. (λ .. . x v .. (λ y. [[e₂]]) ..)) *)
  | LKApp (x, kes, yes) ->
    let open List in
    let vs = map (fun _ -> s_x (Var (fresh ()))) kes in
    fold_right (fun (v, (k, e1)) e -> klam k (c_exp e1) $ Lam (v, e)) (combine vs kes)
      (fold_left (fun e (y, e2) -> e $ xlam y (c_exp e2))
        (fold_left (fun e v -> (e $ LVar v)) (c_x x) vs)
        yes)
  (* [[ [k](κ j. roll e) ]] = (λ j. [[e]]) (λ v. k (roll v)) *)
  | Roll (k, j, e) -> klam j (c_exp e) $ vlam (fun v -> c_k k $ LRoll v)
  (* [[ let y = unroll x in e ]] = (λ y. [[e]]) (unroll x) *)
  | Unroll (y, x, e) -> xlam y (c_exp e) $ LUnroll (c_x x)

(* Pretty-printing for sequent calculus terms *)

let cat = String.concat ""
let cat_map sep f xs = String.concat sep (List.map f xs)
let unwords_by f xs = cat_map " " f xs
let commas_by f xs = cat_map ", " f xs
let arms_by f xs = cat_map " | " f xs
let uncurry f (x, y) = f x y

let p_x (Var x) = "x" ^ string_of_int x
let p_k (Covar k) = "k" ^ string_of_int k

let rec p_ty : ty -> string = function
  | Void -> "0"
  | Unit -> "1"
  | Sum ts -> cat ["("; cat_map " + " p_ty ts; ")"]
  | Prod ts -> cat ["("; cat_map " × " p_ty ts; ")"]
  | Neg t -> cat ["¬"; p_ty t]
  | Vdash (ss, ts) -> cat ["("; commas_by p_ty ss; " ⊢ "; commas_by p_ty ts; ")"]
  | TVar a -> cat ["α"; string_of_int a]
  | Mu (a, t) -> cat ["(μ α"; string_of_int a; ". "; p_ty t; ")"]

let paren s = cat ["("; s; ")"]

let rec p_exp : exp -> string = function
  | Axiom (k, x) -> cat ["["; p_k k; "]"; p_x x]
  | Cut (t, k, e1, x, e2) ->
    cat ["cut "; p_ty t; " "; paren (p_kappa k e1); " "; paren (p_lambda x e2)]
  | Absurd x -> cat ["absurd "; p_x x]
  | Trivial k -> cat ["["; p_k k; "]★"]
  | Tuple (k, jes) -> cat ["["; p_k k; "]("; commas_by (uncurry p_kappa) jes; ")"]
  | Untuple (ys, x, e) -> cat ["let ("; commas_by p_x ys; ") = "; p_x x; " in "; p_exp e]
  | Uncase (js, k, e) -> cat ["let ["; commas_by p_k js; "] = "; p_k k; " in "; p_exp e]
  | Case (x, yes) -> cat ["case "; p_x x; " of "; arms_by (uncurry p_arm) yes; " end"]
  | ToCo (x, k, e) -> cat ["let "; p_x x; " -> "; p_k k; " in "; p_exp e]
  | OfCo (x, k, e) -> cat ["let "; p_x x; " <- "; p_k k; " in "; p_exp e]
  | LK (k, xs, js, e) ->
    cat ["["; p_k k; "](λ "; unwords_by p_x xs; ". κ "; unwords_by p_k js; ". "; p_exp e]
  | LKApp (x, kes, yes) ->
    cat ["case "; p_x x; " "; unwords_by (fun (k, e) -> paren (p_kappa k e)) kes; " of ";
      unwords_by (fun (y, e) -> p_arm y e) yes; " end"]
  | Roll (k, j, e) -> cat ["["; p_k k; "](κ "; p_k j; ". roll "; p_exp e; ")"]
  | Unroll (y, x, e) -> cat ["let "; p_x y; " = unroll "; p_x x; " in "; p_exp e]
and p_kappa k e = cat ["κ "; p_k k; ". "; p_exp e]
and p_lambda x e = cat ["λ "; p_x x; ". "; p_exp e]
and p_arm x e = cat [p_x x; " -> "; p_exp e]

(* Pretty-printing for lambda terms *)

let rec p_lx x = "x" ^ string_of_int x
let rec p_lc : lc -> string = function
  | LVar x -> x
  | Lam (x, e) -> cat ["(λ "; x; ". "; p_lc e; ")"]
  | App (e1, e2) -> cat ["("; p_lc e1; " "; p_lc e2; ")"]
  | LTrivial -> "★"
  | LAbsurd e -> cat ["case "; p_lc e; " of end"]
  | In (n, e) -> cat ["(ι"; string_of_int n; " "; p_lc e; ")"]
  | LCase (e, yes) ->
    cat ["case "; p_lc e; " of "; arms_by (fun (x, e) -> cat [x; " -> "; p_lc e]) yes; " end"]
  | LTuple es -> cat ["("; commas_by p_lc es; ")"]
  | LUntuple (ys, e1, e2) ->
    cat ["let ("; commas_by (fun y -> y) ys; ") = "; p_lc e1; " in "; p_lc e2]
  | LRoll e -> cat ["(roll "; p_lc e; ")"]
  | LUnroll e -> cat ["(unroll "; p_lc e; ")"]

(* Tests *)

let () = print_endline (p_lc (vlam (fun x -> x $ x)))

let (dne_l, dne_lx, dne_lk) =
  let x = Var (fresh ()) in
  let j = Covar (fresh ()) in
  let y = Var (fresh ()) in
  let k = Covar (fresh ()) in
  (ToCo (x, j, OfCo (y, j, Axiom (k, y))), x, k)

let () = print_endline (p_exp dne_l)
let () = print_endline (p_lc (c_exp dne_l))

let dne_r =
  let x = Var (fresh ()) in
  let y = Var (fresh ()) in
  let k = Covar (fresh ()) in
  let j = Covar (fresh ()) in
  OfCo (y, k, ToCo (y, j, Axiom (j, x)))

let () = print_endline (p_exp dne_r)
let () = print_endline (p_lc (c_exp dne_r))

(* x : ¬ ¬ 1 ⊢ let x -> j in let y <- j in k[y] ⊣ k : 1 *)
let res = check (extend dne_lx (Neg (Neg Unit)) empty) dne_l (extend dne_lk Unit empty)

let res = check (extend dne_lx (Neg (Neg Unit)) empty) (Axiom (dne_lk, dne_lx)) (extend dne_lk Unit empty)

let rec tri k = k (fun n j -> if n = 0 then j 0 else tri (fun tri -> tri (n - 1) (fun m -> j (n + m))))

let rec evn k = k (fun n j -> if n = 0 then j true else odd (fun odd -> odd (n - 1) j))
and odd k = k (fun n j -> if n = 0 then j false else evn (fun evn -> evn (n - 1) j))

let evn_odds : bool list * bool list =
  evn (fun evn -> odd (fun odd ->
  evn 0 (fun evn0 -> evn 1 (fun evn1 -> evn 2 (fun evn2 ->
  odd 0 (fun odd0 -> odd 1 (fun odd1 -> odd 2 (fun odd2 ->
  ([evn0; evn1; evn2], [odd0; odd1; odd2])))))))))

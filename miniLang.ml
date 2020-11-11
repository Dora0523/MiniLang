(************************************************* define mini lang ********************************************)
(* define Types *)
type tp =
  | Arrow of tp list * tp   (* function type: S1 S2 ... Sn -> T *)
  | Int
  | Bool

(* define name for variables/identifiers *)
type name = string

(* define the primitive operations *)
type primop = Equals | LessThan | Plus | Minus | Times | Negate

(* define Expressions *)
type exp =
  | I of int                          (* 0 | 1 | 2 | ... *)
  | B of bool                         (* true | false *)
  | If of exp * exp * exp             (* if e then e1 else e2 *)
  | Primop of primop * exp list       (* e1 <op> e2  or <op> e *)
  | Fn of ((name * tp) list * exp)    (* fn (x1: t1, ..., xn: tn) => e *)
  | Rec of (name * tp * exp)          (* rec (f: t) => e *)
  | Let of (name * exp * exp)         (* let x = e1 in e2 end *)
  | Apply of exp * (exp list)         (* e (e_1, e_2, ..., e_n) *)
  | Var of name                       (* x *)



(************************************************** unused vars ************************************************)

(* delete xs from l 
        delete [1;2] [1;2;3] ==> [3] *)
let rec delete xs l =
  List.filter (fun x -> not (List.mem x xs)) l 
  
  
  
(* free_variables 
       free_variables e = list of names occurring free in e
       Invariant: every name occurs at most once. *)
let rec free_variables = 
  (* union [1;2] [2;3] => [1;2;3] *)
  let union l1 l2 =
    let l1' = List.filter (fun x -> not (List.mem x l2)) l1 in
    l1' @ l2
    
  in
  (* taking all unions of a list of all free variables*)
  let union_fvs es =
    List.fold_left (fun acc exp -> union acc (free_variables exp)) [] es
 
 
 in
  function
  | Var y -> [y]                                  (* fv (x) = [x]                                      *)
  | I _ | B _ -> []                               (* fv (1) = []; fv (true) = []                       *)
  | If(e, e1, e2) -> union_fvs [e; e1; e2]        (* fv (if(e)then(e1)else(e2))= fv (union[e;e1;e2])   *)
  | Primop (po, args) -> union_fvs args           (* fv (a1+a2) = fv (union [a1;a2] )                  *) 
  | Fn (xs, e) ->                                 (* fv (fun (a:tp1, b:tp2) => e) =                    *)                                   
      let xs = List.map fst xs in                 (*         xs=[a;b] in                               *)
      delete xs (free_variables e)                (*          delete [a,b] from fv(e)                  *)
  | Rec (x, t, e) ->                              (* fv (rec(x:tp)=>e) = delete [x] from fv(e)         *)
      delete [x] (free_variables e)
  | Let (x, e1, e2) ->                            (* fv (let x=e1 in e2) =                             *)
      let e1_vars = free_variables e1 in          (*      union( fv(e1), fv(e2)\[x] )                  *)
      let e2_vars = delete [x] (free_variables e2) in
      union e1_vars e2_vars
  | Apply (e, es) -> union_fvs (e :: es)          (* fv (apply e (e1,e2)) = union_fv([e;e1;e2])        *)


(* unused vars*)
let rec unused_vars =
  function
  | Var _ | I _ | B _ -> []                                               (*  no unusedvars                              *)
  | If (e, e1, e2) -> unused_vars e @ unused_vars e1 @ unused_vars e2     (* unused(e)::unused(e1)::unused(e2)           *)
  | Primop (_, args) ->                                                   (* unused(+,(a,b)) = unused(a)::unused(b)      *)
      List.fold_left (fun acc exp -> acc @ unused_vars exp) [] args
  | Let (x, e1, e2) ->                                                    (* unused (let x=e1 in e2) =                   *)
      let unused = unused_vars e1 @ unused_vars e2 in                     (*      if x in fv(e2)                         *)
      if List.mem x (free_variables e2) then                              (*           => unused(e1)@unused(e2)          *)
        unused                                                            (*      else => x::unused(e1)@unused(e2)       *)
      else
        x :: unused

  | Rec (x, _, e) ->                                                      (* unused(rec(x:tp)=>e) =                      *)
      if List.mem x (free_variables e) then [] @ unused_vars e            (*      if x in fv(e)                          *)
          else [x] @ unused_vars e                                        (*            => unused(e)                     *)
                                                                          (*      else  => x::unused(e)                  *)
  
  
  
  | Fn (xs, e) ->                                                         (* unused (fun [a:tp1;b:tp2]=>e) =                     *)
      (let (namelst,tplst) = List.split (xs) in                           (*      unused(e)@(fv(e)/[a;b])                        *)
       unused_vars e @ delete (free_variables e) namelst 
      ) 

  | Apply (e, es) ->                                                          (* unused (apply (f,[e1;e2;e3])) =             *)
      (unused_vars e) @ List.fold_left (fun b a -> unused_vars a @ b) [] es   (*      unused(f) @ unused(e1@e2@e3)           *)
                  
      
      
      
(************************************************** subst ************************************************)
type subst = exp * name     

(* substitute variables into expressions *)
let rec subst ((e', x) as s) exp =

  match exp with
  | Var y ->                          (* subst(e',x) (x) => (e') *)
      if x = y then e'
      else Var y
  | I n -> I n                         (* subst(e',x) (int | bool) => (int | bool) *)
  | B b -> B b
  | Primop (po, args) -> Primop (po, List.map (subst s) args)   (* subst(e',x) (x+y)) => (subst(s)(x) + subst(s)(y)) *)
  | If (e, e1, e2) ->                                           (* if (subst(s)(e), then subst(s)(e1), else subst(s)(e2)  *)
      If (subst s e, subst s e1, subst s e2)
  | Let (y, e1, e2) ->                                  (*  subst (e',x)(let x = e1 in e2)          *)
      let e1' = subst s e1 in                           (*      => let e'=e1 in e2                  *)
      if y = x then
        Let (y, e1', e2)
      else                                              (*  if y is in fv(e')                           *)
        let (y, e2) =                                   (*    then (y,e2)=(rename y e2)                 *)
            rename y e2                                 (*  else keep the old variable name             *)
          else                                          (*     => let y = e1' in subst(s)(e2)           *)
            (y, e2)
        in
        Let (y, e1', subst s e2)

          
  | Rec (y, t, e) ->                                    (*   subst(e',x) (rec(x:tp)=>e)  => exp            *)
      if x = y then exp                                 (*   subst(e',x) (rec(y:tp)=>e)  =>                *)
      else                                              (*       if y in fv(e')  then rename(y,exp)        *)
        let (y',exp') =                                 (*       else keep old var name                    *)
          if List.mem y (free_variables e')             (*       rec(y:tp)=> subst(s)(e)                   *)
          then rename y e
          else (y,e)
        in Rec (y',t, subst s exp') 
  

  | Fn (xs, e) ->                                                                         (*  subst(e',x)(fun [a:tp1,b:tp2,c:tp3] e)    *)
      let namelst = (List.map (fun (n,_) -> n) xs) in                                     (*      if x in [a;b;c] => exp                *)
      
      if List.mem x namelst then exp 
        
      else                                                                                   (*      else                                           *)
        let filtername = List.filter (fun x -> (List.mem x (free_variables e'))) namelst  in (*        rename all ele in [a;b;c] that is in fv(e')  *)
        let (name',e') = rename_all filtername e in                                          (*        l=[(a,a');(b,b');(c,c')]                     *)
        let l = List.combine filtername name' in
        let newl =
                                                                                              (*        loop through xs , newl=xs after renaming     *)                                                                             
          let rec nlst xs l acc =                                                             (*         fun(newl, subst(s)(e'))                     *)
            match (xs,l) with
            |(lst,[]) -> (acc @ lst)
            |(((h,e)::tl),((x,x')::xs)) ->
                if h = x
                then nlst (tl) (xs) (acc@ [(x',e)])
                else
                  nlst (tl) (l) (acc@[(h,e)]) 
            |_ ->[]
          in nlst xs l []
        in Fn (newl, subst s e')
        
      
  
  | Apply (e, es) ->                                        (* subst (Apply(f,[e1;e2])) =  Apply (subst(s)(f), [subst(s)(e1);subst(s)(e2)]*)
      Apply (subst s e, List.map (subst s) es) 

and rename x e =                      (* rename x in expression e into x',e' *)
  let x' = freshVar x in
  (x', subst (Var x', x) e)

and rename_all names exp =            (* rename all x in its expression in a list *)
  List.fold_right
    (fun name (names, exp) -> 
       let (name', exp') = rename name exp in
       (name' :: names, exp'))
    names
    ([], exp)
    
(* Applying a list of substitutions to an expression, leftmost first *)
let subst_list subs exp =
  List.fold_left (fun exp sub -> subst sub exp) exp subs


(************************************************** eval ************************************************)
(* Runtime errors that may be raised by eval. *)
type runtime_error =
  | Free_variable of name   (*free var*)
  | Bad_primop_args         (*primop does not match*)
  | If_non_true_false       (* if condition not boolean*)
  | Arity_mismatch          (* applied list != function input requirements*)
  | Apply_non_fn            (* Apply(e,es) not a function *)
exception Stuck of runtime_error

(* Evaluates a primitive operation *)
let eval_op op exps =
  match op, exps with
  | (Equals,   [I i; I i']) -> Some (B (i = i'))
  | (LessThan, [I i; I i']) -> Some (B (i < i'))
  | (Plus,     [I i; I i']) -> Some (I (i + i'))
  | (Minus,    [I i; I i']) -> Some (I (i - i'))
  | (Times,    [I i; I i']) -> Some (I (i * i'))
  | (Negate,   [I i])       -> Some (I (-i))
  | _                       -> None
  
  
(* eval *)
let rec eval exp =
  match exp with
  (* Values evaluate to themselves *)
  | I _ -> exp          (* evaluation of int/boolean/function should be itself*)
  | B _ -> exp
  | Fn _ -> exp
  | Var x -> raise (Stuck (Free_variable x))  (*there should be no variable left since all vars should be subst during evaluation *)
  | Primop (po, args) ->                      (* Primitive operations: +, -, *, <, = *)
      let args = List.map eval args in
      begin
        match eval_op po args with            (* evaluate by matching primops, raise error if no match*)
        | None -> raise (Stuck Bad_primop_args)
        | Some v -> v
      end

  | If (e, e1, e2) ->                         (* evaluate by condition, raise error if e not boolean *)
      begin
        match eval e with
        | B true -> eval e1
        | B false -> eval e2
        | _ -> raise (Stuck If_non_true_false)
      end

  | Let (x, e1, e2) ->                (* evaluate e1 first, then subst(e1,x) to e2 *)
      let e1 = eval e1 in
      eval (subst (e1, x) e2)

  | Rec (f, _, e) ->                  (* subst f by exp, then evaluate *)
      eval (subst (exp,f) e)

  | Apply (e, es) ->                  (* e has to be a function, else, raise error                   *)
      match eval e with               (* if applied list es != function required length, raise error *)
      |Fn(xs,exp) ->
          if List.length es != List.length xs then raise (Stuck Arity_mismatch)
          else
            let lst = List.combine (List.map eval es) (List.map (fun (n,t) -> n) xs)
            in eval (subst_list lst exp)
              
      |_ -> raise (Stuck Apply_non_fn)
              
(************************************************** infer ************************************************)
(* Type contexts *)
type context = (name * tp) list
let empty = []


(* Looks up the topmost x in ctx and returns its corresponding type.*)
let lookup (x: name) (ctx: context) = List.assoc x ctx  


(* Adds a new type ascription (x,tau) to a context. *)
let extend ctx (x, tau) = (x, tau) :: ctx
(* Adds multiple new type ascriptions (l,ctx) to a context. *)
let extend_list (ctx: context) (l: (name * tp) list) =
  List.fold_left extend ctx l



(* Type errors that may be raised by infer *)
type type_error =
  | Free_variable of name
  | Apply_non_arrow of tp (* expected an arrow type, but instead found other tp *)
  | Arity_mismatch
  | Type_mismatch of tp * tp (* (expected type, actual type) *)

exception TypeError of type_error



(* Convenience function for raising type mismatch errors *)
let type_mismatch expected_type inferred_type =
  raise (TypeError (Type_mismatch (expected_type, inferred_type)))


(* Computes the type of a primitive operation.
   The result is a tuple representing the domain and range of the primop.
 *)
let primopType (p: primop): tp list * tp = 
match p with
  | Equals   -> ([Int; Int], Bool)
  | LessThan -> ([Int; Int], Bool)
  | Plus     -> ([Int; Int], Int)
  | Minus    -> ([Int; Int], Int)
  | Times    -> ([Int; Int], Int)
  | Negate   -> ([Int], Int)
;;



(* infer *)
let rec infer ctx e =
  match e with
  | Var x ->
      begin
        try lookup x ctx                                           (* lookup var x, raise error if x is free *)
        with Not_found -> raise (TypeError (Free_variable x))
      end
  | I _ -> Int
  | B _ -> Bool
  
  | Primop (po, exps) ->                             (* recursively check domain & infer context. infer = range if exps and domains are all empty*)
      let (domain, range) = primopType po in
      check ctx exps domain range

  | If (e, e1, e2) ->                           (*  e1 and e2 must have same type inference *)
      begin
        match infer ctx e with
        | Bool ->
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            if t1 = t2 then t1
            else type_mismatch t1 t2
        | t -> type_mismatch Bool t
      end

  | Let (x, e1, e2) ->                        (* infer e1 first, extend context, infer whole exp *)
      let t1 = infer ctx e1 in
      infer (extend ctx (x, t1)) e2

  | Rec (f(*name*), t(*type*), e(*exp*)) ->   (* infered function type == exp *)
      let et = infer (extend ctx (f,t)) e in
      if et<>t then raise (TypeError (type_mismatch t et));
      et

  | Fn (xs, e) -> 
      let (nl,tl) = List.split xs in 
      let t = infer (extend_list (ctx) (xs)) e  (* returns Arrow: typelist (tl) --> infered exp (t) *)
      in Arrow (tl,t)
  
  | Apply (e, es) ->                            (* type(tv) == type(es) *)
      begin match infer ctx e with
        |Arrow (tv,exp) -> 
            let l1 = tv in
            let l2 = (List.map (fun x -> infer ctx x) es)
            in
            let rec f l1 l2 =
              match l1,l2 with
              |([],[]) -> exp
              |(t1::ts1),(t2::ts2) -> 
                  if t1 <> t2 then raise (TypeError (type_mismatch t1 t2)) 
                  else f ts1 ts2
              |_ -> raise(TypeError (Arity_mismatch)) 
            in f l1 l2 
        |t -> raise (TypeError( Apply_non_arrow (t)))
      end
  

and check ctx exps tps result =
  match exps, tps with
  | [], [] -> result
  | e :: es, t :: ts ->
      let t' = infer ctx e in
      if t = t' then check ctx es ts result
      else type_mismatch t t'
  | _ -> raise (TypeError Arity_mismatch)

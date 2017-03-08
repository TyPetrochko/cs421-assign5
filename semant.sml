signature SEMANT =
sig
  type ir_code
  val transprog : Absyn.exp -> {exp: ir_code, ty: Types.ty}
end

structure Semant : SEMANT = 
struct

  structure A = Absyn
  structure E = Env
  structure S = Symbol
  structure T = Types
  val error = ErrorMsg.error
  type ir_code = unit (* not used for the time being *)

  
  (*** FILL IN DETAILS OF YOUR TYPE CHECKER PLEASE !!! ***)

  (*************************************************************************
   *                       UTILITY FUNCTIONS                               *
   *************************************************************************)

  (* ...... *)

  fun checkInt ({exp, ty}, pos) = case ty of T.INT => ()
                                     | T.STRING => (error pos "integer required, string found"; ())
                                     | T.NIL => (error pos "integer required, nil found"; ())
                                     | T.UNIT => () (* don't print error message; happened upstream *)
                                     | _ => (error pos "integer required, unknown type found"; ())

  (*  T.NAME --> T.ty *)
  fun getBaseType(t) = case t of T.NAME(name, typeRef) =>
              (let val deRefed = !typeRef
              in
                case deRefed of SOME(T.NAME(n, t)) => getBaseType(T.NAME(n, t))
                   | SOME(typ: T.ty) => typ
                   | NONE => T.NIL
              end)
         | _ => T.NIL

  fun doTypesMatch(ty1, ty2) =
    case (ty1, ty2) of (T.INT, T.INT) => true
       | (T.STRING, T.STRING) => true
       | (T.NIL, T.NIL) => true
       | (T.UNIT, T.UNIT) => true
       | (T.RECORD(lst1, uniq1), T.RECORD(lst2, uniq2)) => (uniq1 = uniq2)
       | (T.ARRAY(t1, uniq1), T.ARRAY(t2, uniq2)) => (uniq1 = uniq2)
       (* | (T.NAME(s1, t1), T.NAME(s2, t2)) => (s1 = s2 andalso t1 = t2) *) (* TODO is this right? *)
       | (T.NAME(name1, typeRef1), T.NAME(name2, typeRef2)) => 
           (getBaseType(ty1) = getBaseType(ty2))
       | (T.NAME(name, typeRef), _) => 
           (getBaseType(ty1) = ty2)
       | (_ , T.NAME(name, typeRef)) =>
           (getBaseType(ty2) = ty1)
       | (_, _) => false

  fun checkEqualityTypes ({exp=exp1, ty=ty1}, {exp=exp2, ty=ty2}, pos) =
    case (ty1, ty2) of (T.INT, T.INT) => ()
       | (_, _) => ((error pos "TODO eq and neq only cover ints"); ())

  fun getValue (lst : (S.symbol * T.ty) list, key : S.symbol, pos) =
    case lst of [] => (error pos ("record type not found for field "^S.name(key)); T.UNIT)
       | (k, v)::rest => if (key = k) then v else getValue(rest, key, pos)

  fun getVarName(var) = case var of A.SimpleVar(symbol, pos) => S.name(symbol)
                           | A.FieldVar(var, symbol, pos) => getVarName(var)^"."^S.name(symbol)
                           | A.SubscriptVar(var, exp, pos) => getVarName(var)^"[]"

  (* TODO make RECORD and ARRAY more friendly *)
  fun getTypeName t = case t of T.RECORD(lst, uniq) => "RECORD"
                         | T.NIL => "NIL"
                         | T.INT => "INT"
                         | T.STRING => "STRING"
                         | T.UNIT => "UNIT"
                         | T.NAME(sym, reference) => (case !reference of NONE => "NAME" 
                                                      | SOME(t) => getTypeName(t))
                         | T.ARRAY(ty, uniq) => "ARRAY"
  
  fun printKVList l = case l of [] => []
                         | (s, t)::rest => ((print ("Entry: ("^S.name(s)^","^getTypeName(t)^")\n")); (s, t)::(printKVList rest))

  fun debugRecord r = case r of T.RECORD(l, u) => (printKVList l)
                         | _ => ("Not a record!"; [])

  fun checkHasFieldMatch(name, fields, sym, ty, pos) = 
    case fields of [] => 
      ((error pos ("field "^S.name(sym)^" of type "^getTypeName(ty)^
      " does not exist for type "^S.name(name))); ())
       | (s, t)::rest => if (S.name(s) = S.name(sym) andalso t = ty) then ()
                         else checkHasFieldMatch(name, rest, sym, ty, pos)
  
  fun getVarType(var, env, tenv) = case var of A.SimpleVar(symbol, pos) => 
    (case S.look(env, symbol) of SOME(E.VARentry{access, ty}) => ty
        | _ => (error pos ("var "^S.name(symbol)^" does not exist"); T.NIL))
       | A.FieldVar(var, symbol, pos) =>
           (case S.look(tenv, S.symbol (getVarName(var))) of SOME(T.RECORD(fields, uniq)) => 
             let val fieldtype = getValue(fields, symbol, pos)
             in
               if (fieldtype = T.UNIT) then T.NIL else fieldtype
             end
              | NONE => (error pos "error in programming, should not reach here"; T.NIL)
              | SOME(typ) => (error pos ("var "^getVarName(var)^" is not a record"); T.NIL))
       | A.SubscriptVar(var, exp, pos) => getVarType(var, env, tenv)
  
  (* fun getVarType(var, env) = 
    case var of A.SimpleVar(symbol, pos) => 
      (case S.look(env, symbol) of 
            NONE => (error pos "error in programming, should not reach here"; T.NIL)
          | SOME(typ) => typ)
          | A.FieldVar(var, symbol, pos) => 
              (case S.look(env, S.symbol(getVarName(var))) of )
              *)



 (**************************************************************************
  *                   TRANSLATING TYPE EXPRESSIONS                         *
  *                                                                        *
  *              transty : (E.tenv * A.ty) -> (T.ty * A.pos)               *
  *************************************************************************)
  fun transty (tenv, A.ArrayTy(id, pos)) = 
    (* TODO: figure out uniq stuff (ref unit) *)
  let val typ = S.look (tenv, id (* ARRAY TYPE: type a = array of int *))
  in
    case typ of SOME ty => (T.ARRAY(ty, ref ()), pos)
       | NONE => (error pos "missing type"; (T.ARRAY(T.UNIT, ref ()), pos))
  end
    | transty (tenv, A.NameTy(id, pos)) = (* NAME TYPE: type a = int *)
  let val typ = S.look (tenv, id)
  in
    (T.NAME(id, ref typ), pos)
  end
    | transty (tenv, A.RecordTy fields) = (* RECORD TYPE: type a = {key : int, value : int}*)
    case fields of [] =>
      (T.RECORD([], ref ()), 0)
       | {name, typ, pos}::rest =>
      (T.RECORD(map(
        fn {name, typ, pos} => 
          let val ty = S.look (tenv, typ)
          in
            case ty of NONE => (error pos ("unknown type: "^S.name(typ)); (name, T.UNIT))
               | SOME ty => (name, ty)
          end
        ) fields, ref ()), pos)




 (**************************************************************************
  *                   TRANSLATING EXPRESSIONS                              *
  *                                                                        *
  *  transexp : (E.env * E.tenv) -> (A.exp -> {exp : ir_code, ty : T.ty})  *
  **************************************************************************)
  fun transexp (env, tenv) expr =
    let fun g (A.OpExp {left,oper=A.NeqOp,right,pos}) = 
                   (checkEqualityTypes (g left, g right, pos); {exp=(), ty=T.INT})

          | g (A.OpExp {left,oper=A.EqOp,right,pos}) =
                   (checkEqualityTypes (g left, g right, pos); {exp=(), ty=T.INT})

          | g (A.OpExp {left,oper,right,pos}) =
 		   (checkInt (g left, pos);
		    checkInt (g right, pos);
 		    {exp=(), ty=T.INT})

          | g (A.RecordExp {typ,fields,pos}) = 
            (* Define an aux function to make sure they all match up *)
            let fun doFieldsMatchUp(recordName, requiredFields, actualFields, idx, pos) = 
                  (case (requiredFields, actualFields) of ([], []) => true
                     | ([], _) => (error pos ("type "^recordName^" has no param at index "^Int.toString(idx)); false)
                     | (_, []) => (error pos ("type "^recordName^" missing param at index "^Int.toString(idx)); false)
                     | ((paramName, paramType)::moreParams, (argName, toExecute, pos)::moreArgs) =>
                         let val {exp, ty} = g(toExecute) in
                           if (paramName = argName andalso doTypesMatch(paramType, ty))
                           then doFieldsMatchUp(recordName, moreParams, moreArgs, idx + 1, pos)
                           else
                             (error pos ("type "^recordName^" expected "^S.name(paramName)
                                ^" : "^getTypeName(paramType)
                                ^" but found "^S.name(argName)^" : "
                                ^getTypeName(ty)^" at position "
                                ^Int.toString(idx));
                              doFieldsMatchUp(recordName, moreParams, moreArgs, idx + 1, pos))
                         end
                    )
              val ty = S.look(tenv, typ) in
              case ty of 
                   SOME(T.RECORD(recfields, uniq)) => 
                    (doFieldsMatchUp(S.name(typ), recfields, fields, 0, pos); {exp=(), ty=T.RECORD(recfields, uniq)})
                   (*{exp=(), ty=T.RECORD (map (
                      fn (sym, ex, pos) => let val {exp, ty} = g(ex)
                                           in
                                             (checkHasFieldMatch(typ, recfields, sym, ty, pos));
                                             (sym, ty)
                                           end
                                           ) fields, uniq)}*)
                 | NONE => (error pos ("unknown type: "^S.name(typ)); {exp=(), ty=T.RECORD([], ref ())})
                 | _ => (error pos ("may not be a record: "^S.name(typ)); {exp=(), ty=T.RECORD([], ref ())})
            end
          | g (A.StringExp (s, pos)) =
                   {exp=(), ty=T.STRING}
          | g (A.NilExp) =
                   {exp=(), ty=T.NIL}
          | g (A.IntExp i) =
                   {exp=(), ty=T.INT}
          | g (A.AppExp {func, args, pos}) =
          let
            val potentialFunEntry = S.look(env, func)
            fun checkFunCalledCorrectly(name, E.FUNentry{level, label, formals, result}, args : A.exp list, env, tenv, pos) = 
              (case (formals, args) of ([],[]) => result
                  | (_, []) => (error pos ("function "^S.name(name)^" called with not enough arguments"); result)
                  | ([], _) => (error pos ("function "^S.name(name)^" called with too many arguments"); result)
                  | (t::moreTypes, a::moreArgs) => 
                      let val {exp, ty} = g(a) in 
                      if doTypesMatch(ty, t) then 
                        checkFunCalledCorrectly(name, E.FUNentry{level=level, label=label, formals=moreTypes, result=result}, moreArgs, env, tenv, pos)
                      else
                       (* TODO need a better error printout for two records of diff types but with same field names *)
                        (error pos ("function "^S.name(name)^" expected type "^getTypeName(t)^" but got "^getTypeName(ty)); result)
                   end)
                  | checkFunCalledCorrectly _ = (error pos "programming error, should not reach here";T.UNIT)
          in
            case potentialFunEntry of NONE => (error pos ("function "^S.name(func)^" does not exist");{exp=(), ty=T.UNIT})
               | SOME(e) =>
                   {exp=(), ty=checkFunCalledCorrectly(func, e, args, env, tenv, pos)}
          end
          | g (A.SeqExp seqs) =
                   (* Expression sequence *)
            (case seqs of [] => {exp=(), ty=T.UNIT}
               | [(ex, pos)] => (transexp (env, tenv) ex)
               | (ex, pos)::rest => ((transexp (env, tenv)); g (A.SeqExp rest)))
          | g (A.AssignExp {var, exp, pos}) =
            let 
              val {exp, ty} = g(exp)
              val assignedVarType = getVarType(var, env, tenv)
            in
              if(doTypesMatch(assignedVarType, ty) andalso not(assignedVarType = T.NIL))
              then {exp=(), ty=T.UNIT}
              else
                (error pos ("variable "^getVarName(var)^" must be of type "^getTypeName(assignedVarType)^", not "^getTypeName(ty));
                {exp=(), ty=T.UNIT})
            end
          | g (A.IfExp {test, then', else' : A.exp option, pos}) =
                   (* TODO *) {exp=(), ty=T.INT}
          | g (A.WhileExp {test, body, pos}) =
                   (* TODO *) {exp=(), ty=T.INT}
          | g (A.ForExp {var, lo, hi, body, pos}) =
                   (* TODO *) {exp=(), ty=T.INT}
          | g (A.BreakExp pos) =
                   (* TODO implement this *) {exp=(), ty=T.INT}
          | g (A.LetExp {decs, body, pos}) =
                   (* let exp *)
                     transexp(transdecs(env, tenv, decs)) body
          | g (A.ArrayExp {typ, size, init, pos}) =
                   (* ... *) {exp=(), ty=T.INT}
          | g (A.VarExp v) = h(v)

        (* function dealing with "var", may be mutually recursive with g *)
        and h (A.SimpleVar (id,pos)) = (* SIMPLE VAR: a *)
          let val ty = S.look(env, id) in
            case ty of NONE => (error pos ("undefined variable "^S.name(id)); {exp=(), ty=T.UNIT})
               | SOME (E.VARentry{access, ty}) => {exp=(), ty=ty}
               | _ => (error pos ("not a variable entry, probably a func:"^S.name(id)); {exp=(), ty=T.UNIT})
          end
	  | h (A.FieldVar (v,id,pos)) = (* FIELD VAR: a.key *)
      let val {exp, ty} = h(v) in
        case ty of T.RECORD(fields, uniq) => 
          let val field_ty = getValue(fields, id, pos)
          in
            {exp=(), ty=field_ty}
          end
           | _ => (error pos "not a record"; {exp=(), ty=T.UNIT})
      end

	  | h (A.SubscriptVar (v,exp,pos)) = (* ARRAY SUBSCRIPT VAR: a[23] *)
      let val {exp, ty} = h(v) in
        case ty of T.ARRAY(typ, uniq) => {exp=(), ty=typ}
           | _ => (error pos "not an array"; {exp=(), ty=T.UNIT})
      end

     in g expr
    end

 (**************************************************************************
  *                   TRANSLATING DECLARATIONS                             *
  *                                                                        *
  *  transdec : (E.env * E.tenv * A.dec) -> (E.env * E.tenv)               *
  **************************************************************************)
  and transdec (env, tenv, A.VarDec {var={name, escape}, typ, init, pos}) = 
      (* VARIABLE DECLARATION, TODO: Make sure expression of type NIL is record *)
      let val {exp, ty} = (transexp(env, tenv) init)
      in
        (* first check if constraint *)
        case typ of SOME(symbol, pos) => let val ty2 = S.look (tenv, symbol)
            in
              case ty2 of NONE => ((error pos ("undeclared type "^S.name(symbol))); ())
                 | SOME ty2 => 
                     if (not (doTypesMatch(ty, ty2))) 
                     then 
                       (error pos (S.name(name)^" must be of type "^getTypeName(ty)^", not "^getTypeName(ty2)))
                     else ()
            end
           | NONE => ();
        (S.enter(env, name, E.VARentry{access=(), ty=ty}), tenv)
      end
    | transdec (env, tenv, A.FunctionDec(declist)) =
      (case declist of [] => (env, tenv)
         | {name, params, result, body, pos}::rest =>
             (* Helper function to prepare body's environment - (env * tenv * formals)  --> env *)
             (let fun insertNestedTypes(env, tenv, formals) =
                (case formals of [] => env
                   | {var={name, escape}, typ, pos}::rest =>
                       let val potentialParamType = S.look(tenv, typ)
                       in
                         (case potentialParamType of 
                               NONE => (error pos ("undefined type "^S.name(name)); env)
                             | SOME(paramType) => insertNestedTypes(S.enter(env, name, E.VARentry{access=(), ty=paramType}), tenv, rest))
                       end);
               (* Generate environment with params for body*)
               val nestedEnv = insertNestedTypes(env, tenv, params);

               (* iterate through function declarations *)
               val {exp, ty} = (transexp(nestedEnv, tenv) body) in
                 transdec(S.enter(env, name, E.FUNentry{
                 level=(),
                 label=(),
                 formals = map(fn {var, typ, pos} => 
                 (* Convert A.formal list --> A.ty list *)
                    let val searchedType = S.look(tenv, typ)
                    in 
                      (* does this type exist? *)
                      case searchedType of SOME(t) => t
                         | _ => (error pos ("undefined type "^S.name(typ));T.UNIT)
                    end
                 ) params,
                 result = ty})
              ,tenv, A.FunctionDec(rest))
             end))
    | transdec (env, tenv, A.TypeDec(declist)) = 
      (* TYPE DECLARATION *) 
      case declist of [] => (env, tenv)
         | [{name, ty, pos}] =>
             let val (ty, pos) = transty(tenv, ty)
             in 
               (env, S.enter(tenv, name, ty))
             end
         | {name, ty, pos}::rest => 
             let val (ty, pos) = transty(tenv, ty)
             in
               transdec(env, S.enter(tenv, name, ty), A.TypeDec(rest))
             end

  (*** transdecs : (E.env * E.tenv * A.dec list) -> (E.env * E.tenv) ***)
  and transdecs (env,tenv,nil) = (env, tenv)
    | transdecs (env,tenv,dec::decs) =
	let val (env',tenv') = transdec (env,tenv,dec)
 	 in transdecs (env',tenv',decs)
	end

  (*** transprog : A.exp -> {exp : ir_code, ty : T.ty} ***)
  fun transprog prog = transexp (E.base_env, E.base_tenv) prog

end  (* structure Semant *)
  


signature ENV =
sig
  type access
  type level
  type label
  type ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table
  type env = enventry Symbol.table

  val base_tenv : tenv
  val base_env : env
end

structure Env : ENV =
struct

  structure S = Symbol
  structure T = Types

  type access = unit   (* not used for the time being *)
  type level = unit    (* not used for the time being *)
  type label = unit    (* not used for the time being *)
  type ty = T.ty

  datatype enventry 
    = VARentry of {access: access, ty: ty}
    | FUNentry of {level: level, label: label, formals: ty list, result: ty}

  type tenv = ty Symbol.table

  type env = enventry Symbol.table

  (* here you need to add all primtive types into the base_tenv *)
  val base_tenv = (* fill in the details *) S.empty
 
  (* here you need to add all primitive library functions into the base_env *)
  val base_env = (* fill in the details *) S.empty

end  (* structure Env *)
  

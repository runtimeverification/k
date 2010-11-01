open Machdep
module R = Str
module L = List
module H = Hashtbl

let preparse (s:string) : (string, string list) H.t =
  let specTable = H.create 32 in
  let commaRegexp = R.regexp "," in
  let spaceRegexp = R.regexp "[ \t]+" in
  let specRegexp = R.regexp "^\\([a-zA-Z_0-9]+\\)[ \t]*=\\(.*\\)$" in
  let specs = R.split spaceRegexp s in
  let addSpec spec = 
    if R.string_match specRegexp spec 0 then begin
      let name = R.matched_group 1 spec in
      let value = R.matched_group 2 spec in
      H.add specTable name (R.split commaRegexp value)
    end
    else
      raise (Failure ("invalid specification string " ^ spec))
  in
  L.iter addSpec specs;
  specTable

let errorWrap name f =
  try 
    f name
  with Not_found -> raise (Failure (name ^ " not specified"))
  | _ -> raise (Failure ("invalid format for " ^ name))

let getNthString n specTable name = 
  let l = H.find specTable name in
  L.nth l n

let getNthInt n specTable name =
  errorWrap name (fun name -> int_of_string (getNthString n specTable name))

let getNthBool n specTable name = 
  errorWrap name (fun name -> bool_of_string (getNthString n specTable name))

let getBool = getNthBool 0
let getInt = getNthInt 0
let getSizeof = getNthInt 0
let getAlignof = getNthInt 1

let respace = Str.global_replace (Str.regexp "_") " "

let modelParse (s:string) : mach = 
  let entries =
    try
      preparse s 
    with Failure msg -> raise (Failure msg)
    | _ -> raise (Failure "invalid machine specification")
  in
  {
    version_major = 0;
    version_minor = 0;
    version = "machine model " ^ s;
    underscore_name = getBool entries "underscore_name";
    sizeof_short = getSizeof entries "short";
    alignof_short = getAlignof entries "short";
    sizeof_bool = getSizeof entries "bool";
    alignof_bool = getAlignof entries "bool";
    sizeof_int = getSizeof entries "int";
    alignof_int = getAlignof entries "int";
    sizeof_long = getSizeof entries "long";
    alignof_long = getAlignof entries "long";
    sizeof_longlong = getSizeof entries "long_long";
    alignof_longlong = getAlignof entries "long_long";
    sizeof_ptr = getSizeof entries "pointer";
    alignof_ptr = getAlignof entries "pointer";
    sizeof_enum = getSizeof entries "enum";
    alignof_enum = getAlignof entries "enum";
    sizeof_float = getSizeof entries "float";
    alignof_float = getAlignof entries "float";
    sizeof_double = getSizeof entries "double";
    alignof_double = getAlignof entries "double";
    sizeof_longdouble = getSizeof entries "long_double";
    alignof_longdouble = getAlignof entries "long_double";
    sizeof_void = getSizeof entries "void";
    sizeof_fun = getSizeof entries "fun";
    alignof_fun = getAlignof entries "fun";
    alignof_str = getInt entries "alignof_string";
    alignof_aligned = getInt entries "max_alignment";
    size_t = respace (getNthString 0 entries "size_t");
    wchar_t = respace (getNthString 0 entries "wchar_t");
    char_is_unsigned = getBool entries "char_signed";
    const_string_literals = getBool entries "const_string_literals";
    little_endian = not (getBool entries "big_endian");
    __thread_is_keyword = getBool entries "__thread_is_keyword";
    __builtin_va_list = getBool entries "__builtin_va_list";
  }

open Constants
open Constants.K
open Prelude

module MAP =
struct

  let hook_element c lbl sort _ _ = match c with
      k1, k2 -> [Map (sort,(collection_for lbl),(KMap.singleton k1 k2))]
  let hook_unit c lbl sort _ _ = match c with
      () -> [Map (sort,(collection_for lbl),KMap.empty)]
  let hook_concat c _ _ _ _ = match c with
      ([Map (s,l1,k1)]), ([Map (_,l2,k2)])
        when (l1 = l2) -> [Map (s,l1,(KMap.union (fun _ a b -> if a = b then Some a else raise Not_implemented) k1 k2))]
    | _ -> raise Not_implemented
  let hook_lookup c _ _ _ _ = match c with
      [Map (_,_,k1)], k2 -> (try KMap.find k2 k1 with Not_found -> interned_bottom)
    | [Bottom], _ -> interned_bottom
    | _ -> raise Not_implemented
  let hook_lookupOrDefault c _ _ _ _ = match c with
      [Map (_,_,k1)], k2, k3 -> (try KMap.find k2 k1 with Not_found -> k3)
    | [Bottom], _, k3 -> k3
    | _ -> raise Not_implemented
  let hook_update c _ _ _ _ = match c with
      [Map (s,l,k1)], k, v -> [Map (s,l,(KMap.add k v k1))]
    | _ -> raise Not_implemented
  let hook_remove c _ _ _ _ = match c with
      [Map (s,l,k1)], k2 -> [Map (s,l,(KMap.remove k2 k1))]
    | _ -> raise Not_implemented
  let hook_difference c _ _ _ _ = match c with
      [Map (s,l1,k1)], [Map (_,l2,k2)]
        when (l1 = l2) -> [Map (s,l1,(KMap.filter (fun k v -> try (compare (KMap.find k k2) v) <> 0 with Not_found -> true) k1))]
    | _ -> raise Not_implemented
  let hook_keys c _ _ _ _ = match c with
      [Map (_,_,k1)] -> [Set (SortSet, Lbl_Set_,(KMap.fold (fun k _ -> KSet.add k) k1 KSet.empty))]
    | _ -> raise Not_implemented
  let hook_keys_list c _ _ _ _ = match c with
      [Map (_,_,k1)] -> [List (SortList, Lbl_List_,(match List.split (KMap.bindings k1) with l, _ -> l))]
    | _ -> raise Not_implemented
  let hook_in_keys c _ _ _ _ = match c with
      (k1, [Map (_,_,k2)]) -> [Bool (KMap.mem k1 k2)]
    | (_, [Bottom]) -> [Bool false] (* case is useful for double map lookup *)
    | _ -> raise Not_implemented
  let hook_values c _ _ _ _ = match c with
      [Map (_,_,k1)] -> [List (SortList, Lbl_List_,(match List.split (KMap.bindings k1) with (_,vs) -> vs))]
    | _ -> raise Not_implemented
  let hook_choice c _ _ _ _ = match c with
      [Map (_,_,k1)] -> (match KMap.choose k1 with (k, _) -> k)
    | _ -> raise Not_implemented
  let hook_size c _ _ _ _ = match c with
      [Map (_,_,m)] -> [Int (Z.of_int (KMap.cardinal m))]
    | _ -> raise Not_implemented
  let hook_inclusion c _ _ _ _ = match c with
      [Map (_,l1,k1)], [Map (_,l2,k2)]
        when (l1 = l2) -> [Bool (KMap.for_all (fun k v -> try (compare (KMap.find k k2) v) = 0 with Not_found -> false) k1)]
    | _ -> raise Not_implemented
  let hook_updateAll c _ _ _ _ = match c with
      ([Map (s,l1,k1)]), ([Map (_,l2,k2)])
        when (l1 = l2) -> [Map (s,l1,(KMap.union (fun _ a b -> match a, b with
                          _, v -> Some v) k1 k2))]
    | _ -> raise Not_implemented
  let hook_removeAll c _ _ _ _ = match c with
      [Map (s,l,k1)], [Set (_,_,k2)] -> [Map (s,l,KMap.filter (fun k _ -> not (KSet.mem k k2)) k1)]
    | _ -> raise Not_implemented
end

module SET =
struct
  let hook_in c _ _ _ _ = match c with
      k1, [Set (_,_,k2)] -> [Bool (KSet.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_unit c lbl sort _ _ = match c with
      () -> [Set (sort,(collection_for lbl),KSet.empty)]
  let hook_element c lbl sort _ _ = match c with
      k -> [Set (sort,(collection_for lbl),(KSet.singleton k))]
  let hook_concat c _ _ _ _ = match c with
      [Set (sort,l1,s1)], [Set (_,l2,s2)] when (l1 = l2) -> [Set (sort,l1,(KSet.union s1 s2))]
    | _ -> raise Not_implemented
  let hook_difference c _ _ _ _ = match c with
      [Set (s,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Set (s,l1,(KSet.diff k1 k2))]
    | _ -> raise Not_implemented
  let hook_inclusion c _ _ _ _ = match c with
      [Set (_,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Bool (KSet.subset k1 k2)]
    | _ -> raise Not_implemented
  let hook_intersection c _ _ _ _ = match c with
      [Set (s,l1,k1)], [Set (_,l2,k2)] when (l1 = l2) -> [Set (s,l1,(KSet.inter k1 k2))]
    | _ -> raise Not_implemented
  let hook_choice c _ _ _ _ = match c with
      [Set (_,_,k1)] -> KSet.choose k1
    | _ -> raise Not_implemented
  let hook_size c _ _ _ _ = match c with
      [Set (_,_,s)] -> [Int (Z.of_int (KSet.cardinal s))]
    | _ -> raise Not_implemented
  let hook_set2list c _ _ _ _ = match c with
      [Set (_,_,s)] -> [List (SortList,Lbl_List_, (KSet.elements s))]
    | _ -> raise Not_implemented
  let hook_list2set c _ _ _ _ = match c with
      [List (_,_,l)] -> [Set (SortSet,Lbl_Set_, (KSet.of_list l))]
    | _ -> raise Not_implemented
end

module LIST =
struct
  let hook_unit c lbl sort _ _ = match c with
      () -> [List (sort,(collection_for lbl),[])]
  let hook_element c lbl sort _ _ = match c with
      k -> [List (sort,(collection_for lbl),[k])]
  let hook_concat c _ _ _ _ = match c with
      [List (s,lbl1,l1)], [List (_,lbl2,l2)] when (lbl1 = lbl2) -> [List (s,lbl1,(l1 @ l2))]
    | _ -> raise Not_implemented
  let hook_in c _ _ _ _ = match c with
      k1, [List (_,_,k2)] -> [Bool (List.mem k1 k2)]
    | _ -> raise Not_implemented
  let hook_get c _ _ _ _ = match c with
      [List (_,_,l1)], [Int i] ->
        let i = Z.to_int i in (try if i >= 0 then List.nth l1 i else List.nth l1 ((List.length l1) + i)
                               with Failure _ -> interned_bottom | Invalid_argument _ -> interned_bottom)
    | _ -> raise Not_implemented
  let hook_range c _ _ _ _ = match c with
      [List (s,lbl,l1)], [Int i1], [Int i2] ->
        (try [List (s,lbl,(list_range (l1, (Z.to_int i1), (List.length(l1) - (Z.to_int i2) - (Z.to_int i1)))))]
         with Failure _ -> interned_bottom)
    | _ -> raise Not_implemented
  let hook_size c _ _ _ _ = match c with
      [List (_,_,l)] -> [Int (Z.of_int (List.length l))]
    | _ -> raise Not_implemented
  let hook_make _ _ _ _ _ = raise Not_implemented
  let hook_updateAll _ _ _ _ _ = raise Not_implemented
  let hook_fill _ _ _ _ _ = raise Not_implemented
  let hook_update _ _ _ _ _ = raise Not_implemented
end

module ARRAY =
struct
  let hook_make c _ sort _ _ = match c with
      [Int len], k -> [Array (sort,k,(Dynarray.make (Z.to_int len) k))]
    | _ -> raise Not_implemented
  let hook_makeEmpty c _ sort _ _ = match c with
      [Int len] -> [Array (sort,interned_bottom,(Dynarray.make (Z.to_int len) interned_bottom))]
    | _ -> raise Not_implemented
  let hook_lookup c _ _ _ _ = match c with
      [Array (_,k,a)], [Int idx] -> (try Dynarray.get a (Z.to_int idx) with Invalid_argument _ | Z.Overflow -> k)
    | _ -> raise Not_implemented
  let hook_update c _ _ _ _ = match c with
      [Array (_,_,a)] as value, [Int i], k -> (try Dynarray.set a (Z.to_int i) k with Invalid_argument _ | Z.Overflow -> ()); value
    | _ -> raise Not_implemented
  let hook_remove c _ _ _ _ = match c with
      [Array (_,k,a)] as value, [Int i] -> (try Dynarray.set a (Z.to_int i) k with Invalid_argument _ | Z.Overflow -> ()); value
    | _ -> raise Not_implemented
  let hook_updateAll c _ _ _ _ = match c with
      [Array (_,_,a)] as value, [Int i], [List (_,_,l)] -> List.iteri (fun j elt -> try Dynarray.set a (j + (Z.to_int i)) elt with Invalid_argument _ | Z.Overflow -> ()) l; value
    | _ -> raise Not_implemented
  let hook_fill c _ _ _ _ = match c with
      [Array (_,_,a)] as value, [Int i], [Int n], elt -> (try (for j = (Z.to_int i) to (Z.to_int i) + (Z.to_int n) - 1 do
        try Dynarray.set a j elt with Invalid_argument _ -> ()
      done) with Z.Overflow -> ()); value
    | _ -> raise Not_implemented
  let hook_in_keys c _ _ _ _ = match c with
      [Int i], [Array (_,k,a)] -> [Bool (try (if compare (Dynarray.get a (Z.to_int i)) k = 0 then false else true) with Invalid_argument _ | Z.Overflow -> false)]
    | _ -> raise Not_implemented

  let hook_ctor c _ sort _ _ = match c with
      _, [Int len] -> [Array (sort,interned_bottom,(Dynarray.make (Z.to_int len) interned_bottom))]
    | _ -> raise Not_implemented
end

module KREFLECTION =
struct
  let hook_sort c _ _ _ _ = match c with

      [KToken (sort, _)] -> [String (print_sort(sort))]
    | [Int _] -> [String "Int"]
    | [String _] -> [String "String"]
    | [Bytes _] -> [String "Bytes"]
    | [Bool _] -> [String "Bool"]
    | [Map (s,_,_)] -> [String (print_sort s)]
    | [List (s,_,_)] -> [String (print_sort s)]
    | [Set (s,_,_)] -> [String (print_sort s)]
    | _ -> raise Not_implemented
  let hook_getKLabel c _ _ _ _ = match c with
      [k] -> (match (normalize k) with KApply (lbl, _) -> [InjectedKLabel lbl] | _ -> interned_bottom)
    | _ -> interned_bottom
  let hook_configuration c _ _ config _ = match c with
      () -> config
  let hook_fresh c _ _ config ff = match c with
      [String sort] -> let res = ff sort config !freshCounter in freshCounter := Z.add !freshCounter Z.one; res
    | _ -> raise Not_implemented
  let hook_getenv c _ _ _ _ = match c with
      [String key] -> [String (Sys.getenv key)]
    | _ -> raise Not_implemented
  let hook_argv c _ _ _ _ = match c with
      () -> [List (SortList, Lbl_List_,(Array.fold_right (fun arg res -> [String arg] :: res) !CONFIG.sys_argv []))]
  let hook_parseKAST c _ _ _ _ = match c with
    | [String s] -> (try Lexer.parse_k s with
      | e -> [KApply1(parse_klabel("#noParse"), [String (Printexc.to_string e)])])
    | _ -> raise Not_implemented
end

module KEQUAL =
struct
  let hook_eq c _ _ _ _ = match c with
      k1, k2 -> [Bool ((compare k1 k2) = 0)]
  let hook_ne c _ _ _ _ = match c with
      k1, k2 -> [Bool ((compare k1 k2) <> 0)]
  let hook_ite c _ _ _ _ = match c with
      [Bool t], k1, k2 -> if t then k1 else k2
    | _ -> raise Not_implemented
end

module IO =
struct
  let hook_close c _ _ _ _ = match c with
      [Int i] -> unix_error (fun () -> Unix.close (Hashtbl.find file_descriptors i); [])
    | _ -> raise Not_implemented
  let hook_getc c _ _ _ _ = match c with
      [Int i] -> unix_error (fun () -> let b = Bytes.create 1 in match Unix.read (Hashtbl.find file_descriptors i) b 0 1 with
          0 -> [Int (Z.of_int (-1))]
        | _ -> [Int (Z.of_int (Char.code (Bytes.get b 0)))])
    | _ -> raise Not_implemented
  let hook_open c _ _ _ _ = match c with
      [String path], [String flags] ->
        unix_error (fun () -> let fd = Unix.openfile path (convert_open_flags flags) default_file_perm in
          let fd_int = !curr_fd in Hashtbl.add file_descriptors fd_int fd; curr_fd := (Z.add fd_int Z.one); [Int fd_int])
    | _ -> raise Not_implemented
  let hook_putc c _ _ _ _ = match c with
      [Int fd], [Int c] -> unix_error (fun () -> let _ = Unix.write (Hashtbl.find file_descriptors fd) (Bytes.make 1 (Char.chr (Z.to_int c))) 0 1 in [])
    | _ -> raise Not_implemented
  let hook_read c _ _ _ _ = match c with
      [Int fd], [Int len] -> unix_error (fun () -> let l = (Z.to_int len) in
        let b = Bytes.create l in let bread = Unix.read (Hashtbl.find file_descriptors fd) b 0 l in [String (Bytes.sub_string b 0 bread)])
    | _ -> raise Not_implemented
  let hook_seek c _ _ _ _ = match c with
      [Int fd], [Int off] -> unix_error (fun () -> let o = (Z.to_int off) in let _ = Unix.lseek (Hashtbl.find file_descriptors fd) o Unix.SEEK_SET in [])
    | _ -> raise Not_implemented
  let hook_seekEnd c _ _ _ _ = match c with
      [Int fd], [Int off] -> unix_error (fun () -> let o = (Z.to_int off) in let _ = Unix.lseek (Hashtbl.find file_descriptors fd) o Unix.SEEK_END in [])
    | _ -> raise Not_implemented
  let hook_tell c _ _ _ _ = match c with
      [Int fd] -> unix_error (fun () -> [Int (Z.of_int (Unix.lseek (Hashtbl.find file_descriptors fd) 0 Unix.SEEK_CUR))])
    | _ -> raise Not_implemented
  let hook_write c _ _ _ _ = match c with
      [Int fd], [String s] -> unix_error (fun () -> let b = Bytes.of_string s in let _ = Unix.write (Hashtbl.find file_descriptors fd) b 0 (Bytes.length b) in [])
    | _ -> raise Not_implemented
  let hook_lock c _ _ _ _ = match c with
      [Int fd], [Int len] -> unix_error (fun () -> Unix.lockf (Hashtbl.find file_descriptors fd) Unix.F_LOCK (Z.to_int len); [])
    | _ -> raise Not_implemented
  let hook_unlock c _ _ _ _ = match c with
      [Int fd], [Int len] -> unix_error (fun () -> Unix.lockf (Hashtbl.find file_descriptors fd) Unix.F_ULOCK (Z.to_int len); [])
    | _ -> raise Not_implemented

  let log_files = Hashtbl.create 2

  let hook_log c _ _ _ _ = match c with
      [String path], [String txt] ->
      let log = try
        Hashtbl.find log_files path
      with Not_found ->
        let empty = Buffer.create 16 in
        Hashtbl.add log_files path empty;
        empty
      in
      Buffer.add_string log txt;
      []
    | _ -> raise Not_implemented

  let flush_log path txt =
    let dir = Filename.dirname path in
    let base = Filename.basename path in
    let pid = string_of_int (Unix.getpid ()) in
    let new_path = Filename.concat dir (pid ^ "_" ^ base) in
    let flags = [Open_wronly; Open_append; Open_creat; Open_text] in
    let out_chan = open_out_gen flags 0o666 new_path in
    let fd = Unix.descr_of_out_channel out_chan in
    Unix.lockf fd Unix.F_LOCK 0;
    output_string out_chan (Buffer.contents txt);
    close_out out_chan

  let flush_logs () =
    Hashtbl.iter flush_log log_files

  let hook_stat _ _ _ _ _ = raise Not_implemented
  let hook_lstat _ _ _ _ _ = raise Not_implemented
  let hook_opendir _ _ _ _ _ = raise Not_implemented
  let hook_system c _ _ _ _ = match c with
    | [String path] ->
      let ic, oc, ec = Unix.open_process_full path (Unix.environment ()) in
      let buf_out = Buffer.create 4096
      and buf_err = Buffer.create 4096 in
      (try
         while true do Buffer.add_channel buf_out ic 1 done
       with End_of_file -> ());
      (try
         while true do Buffer.add_channel buf_err ec 1 done
       with End_of_file -> ());
      let exit_status = Unix.close_process_full (ic, oc, ec) in
      let exit_code = match exit_status with
        | Unix.WEXITED n -> n
        (* according to: https://unix.stackexchange.com/questions/99112/default-exit-code-when-process-is-terminated *)
        | Unix.WSIGNALED n -> (128 + n)
        | Unix.WSTOPPED n -> (128 + n)
      in
      [KApply3((parse_klabel "#systemResult(_,_,_)_K-IO"), [Int (Z.of_int exit_code)], [String (Buffer.contents buf_out)], [String (Buffer.contents buf_err)])]
    | _ -> raise Not_implemented
  let hook_mkstemp c _ _ _ _ = match c with
    | [String prefix], [String suffix] -> unix_error (fun () ->
            unix_error (fun () -> let path, outChannel = Filename.open_temp_file prefix suffix in
              let fd_int = !curr_fd in Hashtbl.add file_descriptors fd_int (Unix.descr_of_out_channel outChannel); curr_fd := (Z.add fd_int Z.one);
              [KApply2((parse_klabel "#tempFile(_,_)_K-IO"), [String path], [Int fd_int])]))
    | _ -> raise Not_implemented
  let hook_remove c _ _ _ _ = match c with
    | [String fname] -> unix_error (fun () -> Unix.unlink fname ; [])
    | _ -> raise Not_implemented

end

module BOOL =
struct
  let hook_and c _ _ _ _ = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 && b2)]
    | _ -> raise Not_implemented
  let hook_andThen = hook_and
  let hook_or c _ _ _ _ = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 || b2)]
    | _ -> raise Not_implemented
  let hook_orElse = hook_or
  let hook_not c _ _ _ _ = match c with
      [Bool b1] -> [Bool (not b1)]
    | _ -> raise Not_implemented
  let hook_implies c _ _ _ _ = match c with
      [Bool b1], [Bool b2] -> [Bool ((not b1) || b2)]
    | _ -> raise Not_implemented
  let hook_ne c _ _ _ _ = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 <> b2)]
    | _ -> raise Not_implemented
  let hook_eq c _ _ _ _ = match c with
      [Bool b1], [Bool b2] -> [Bool (b1 = b2)]
    | _ -> raise Not_implemented
  let hook_xor = hook_ne
end

module BUFFER =
struct
  let hook_empty c _ _ _ _ = match c with
      () -> [StringBuffer (Buffer.create 32)]
  let hook_concat c _ _ _ _ = match c with
      [StringBuffer buf], [String s] -> Buffer.add_string buf s; [StringBuffer buf]
    | _ -> raise Not_implemented
  let hook_toString c _ _ _ _ = match c with
      [StringBuffer buf] -> [String (Buffer.contents buf)]
    | _ -> raise Not_implemented
end

module BYTES =
struct
  let hook_empty c _ _ _ _ = match c with
      () -> [Bytes (Bytes.empty)]
  let hook_bytes2int c _ _ _ _ = match c with
      [Bytes b], [KApply0(LbllittleEndianBytes)], [KApply0(LblunsignedBytes)] ->
      [Int (Z.of_bits (Bytes.to_string b))]
    | [Bytes b], [KApply0(LblbigEndianBytes)], [KApply0(LblunsignedBytes)] ->
      [Int (Z.of_bits (Bytes.to_string (reverse b)))]
    | [Bytes b], [KApply0(LbllittleEndianBytes)], [KApply0(LblsignedBytes)] ->
      [Int (signed_extract (Z.of_bits (Bytes.to_string b)) 0 ((Bytes.length b) * 8))]
    | [Bytes b], [KApply0(LblbigEndianBytes)], [KApply0(LblsignedBytes)] ->
      [Int (signed_extract (Z.of_bits (Bytes.to_string (reverse b))) 0 ((Bytes.length b) * 8))]
    | _ -> raise Not_implemented
  let hook_int2bytes c _ _ _ _ = match c with
      [Int len], [Int i], [KApply0(endian)] ->
      let len = Z.to_int len in
      if len = 0 then [Bytes Bytes.empty] else
      let compl = Z.lt i Z.zero in
      let b = Bytes.make len (if compl then '\255' else '\000') in
      let twos = Z.extract i 0 (len * 8) in
      let s = Z.to_bits twos in
      Bytes.blit_string s 0 b 0 (min len (String.length s));
      [Bytes (if endian = LbllittleEndianBytes then b else reverse b)]
    | _ -> raise Not_implemented
  let hook_bytes2string c _ _ _ _ = match c with
      [Bytes b] -> [String (Bytes.to_string b)]
    | _ -> raise Not_implemented
  let hook_string2bytes c _ _ _ _ = match c with
      [String s] -> [Bytes (Bytes.of_string s)]
    | _ -> raise Not_implemented
  let hook_substr c _ _ _ _ = match c with
      [Bytes b], [Int off1], [Int off2] ->
      [Bytes (Bytes.sub b (Z.to_int off1) (Z.to_int (Z.sub off2 off1)))]
    | _ -> raise Not_implemented
  let hook_replaceAt c _ _ _ _ = match c with
      [Bytes b], [Int off], [Bytes b2] ->
      Bytes.blit b2 0 b (Z.to_int off) (Bytes.length b2);
      [Bytes b]
    | _ -> raise Not_implemented
  let hook_length c _ _ _ _ = match c with
      [Bytes b] -> [Int (Z.of_int (Bytes.length b))]
    | _ -> raise Not_implemented
  let hook_padRight c _ _ _ _ = match c with
      [Bytes b], [Int len], [Int v] ->
      let len = Z.to_int len in
      if len <= Bytes.length b then [Bytes b] else
      let res = Bytes.make (max (Bytes.length b) len) (Char.chr (Z.to_int v)) in
      Bytes.blit b 0 res 0 (Bytes.length b);
      [Bytes res]
    | _ -> raise Not_implemented
  let hook_padLeft c _ _ _ _ = match c with
      [Bytes b], [Int len], [Int v] ->
      let len = Z.to_int len in
      if len <= Bytes.length b then [Bytes b] else
      let res = Bytes.make (max (Bytes.length b) len) (Char.chr (Z.to_int v)) in
      Bytes.blit b 0 res (len - Bytes.length b) (Bytes.length b);
      [Bytes res]
    | _ -> raise Not_implemented
  let hook_reverse c _ _ _ _ = match c with
      [Bytes b] -> [Bytes (reverse b)]
    | _ -> raise Not_implemented
  let hook_concat c _ _ _ _ = match c with
      [Bytes b1], [Bytes b2] -> [Bytes (Bytes.cat b1 b2)]
    | _ -> raise Not_implemented
end

module STRING =
struct
  let hook_concat c _ _ _ _ = match c with
      [String s1], [String s2] -> [String (s1 ^ s2)]
    | _ -> raise Not_implemented
  let hook_lt c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) < 0)]
    | _ -> raise Not_implemented
  let hook_le c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) <= 0)]
    | _ -> raise Not_implemented
  let hook_gt c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) > 0)]
    | _ -> raise Not_implemented
  let hook_ge c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool ((String.compare s1 s2) >= 0)]
    | _ -> raise Not_implemented
  let hook_eq c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool (s1 = s2)]
    | _ -> raise Not_implemented
  let hook_ne c _ _ _ _ = match c with
      [String s1], [String s2] -> [Bool (s1 <> s2)]
    | _ -> raise Not_implemented
  let hook_chr c _ _ _ _ = match c with
      [Int i] -> [String (String.make 1 (Char.chr (Z.to_int i)))]
    | _ -> raise Not_implemented
  let hook_find c _ _ _ _ = match c with
      [String s1], [String s2], [Int i] ->
        (try [Int (Z.of_int (Str.search_forward (Str.regexp_string s2) s1 (Z.to_int i)))]
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_rfind c _ _ _ _ = match c with
      [String s1], [String s2], [Int i] ->
        (try [Int (Z.of_int (Str.search_backward (Str.regexp_string s2) s1 (Z.to_int i)))]
        with Not_found -> [Int (Z.of_int (-1))])
    | _ -> raise Not_implemented
  let hook_length c _ _ _ _ = match c with
      [String s] -> [Int (Z.of_int (String.length s))]
    | _ -> raise Not_implemented
  let hook_substr c _ _ _ _ = match c with
      [String s], [Int i1], [Int i2] -> [String (String.sub s (Z.to_int i1) (Z.to_int (Z.sub i2 i1)))]
    | _ -> raise Not_implemented
  let hook_ord c _ _ _ _ = match c with
      [String s] -> [Int (Z.of_int (Char.code (String.get s 0)))]
    | _ -> raise Not_implemented
  let hook_int2string c _ _ _ _ = match c with
      [Int i] -> [String (Z.to_string i)]
    | _ -> raise Not_implemented
  let hook_string2int c _ _ _ _ = match c with
      [String s] -> [Int (Z.of_string s)]
    | _ -> raise Not_implemented
  let hook_string2base c _ _ _ _ = match c with
      [String s], [Int i] -> [Int (Z.of_string_base (Z.to_int i) s)]
    | _ -> raise Not_implemented
  let hook_base2string c _ _ _ _ = match c with
      [Int i], [Int base] -> [String (to_string_base (Z.to_int base) i)]
    | _ -> raise Not_implemented
  let hook_string2token c _ sort _ _ = match c with
      [String value] -> [ktoken sort value]
    | _ -> raise Not_implemented
  let hook_token2string c _ _ _ _ = match c with
      [KToken(_,s)] -> [String s]
    | [Bool b] -> [String (string_of_bool b)]
    | [String s] -> [String ("\"" ^ (k_string_escape s) ^ "\"")]
    | [Int i] -> [String (Z.to_string i)]
    | [Float(f,p,e)] -> [String (precise_float_to_string (f,e,p))]
    | _ -> raise Not_implemented
  let hook_float2string c _ _ _ _ = match c with
      [Float (f,_,_)] -> [String (Gmp.FR.to_string_base_digits Gmp.GMP_RNDN 10 0 f)]
    | _ -> raise Not_implemented
  let hook_uuid c _ _ _ _ = match c with
      () -> let uuid = Uuidm.create `V4 in
      [String (Uuidm.to_string uuid)]
  let hook_floatFormat _ _ _ _ _ = raise Not_implemented
  let hook_string2float _ _ _ _ _ = raise Not_implemented
  let hook_replace _ _ _ _ _ = raise Not_implemented
  let hook_replaceAll _ _ _ _ _ = raise Not_implemented
  let hook_replaceFirst _ _ _ _ _ = raise Not_implemented
  let hook_countAllOccurrences _ _ _ _ _ = raise Not_implemented
  let hook_category _ _ _ _ _ = raise Not_implemented
  let hook_directionality _ _ _ _ _ = raise Not_implemented
  let hook_findChar _ _ _ _ _ = raise Not_implemented
  let hook_rfindChar _ _ _ _ _ = raise Not_implemented
end

module INT =
struct
  let hook_tmod c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.rem a b)]
    | _ -> raise Not_implemented
  let hook_emod c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.erem a b)]
    | _ -> raise Not_implemented
  let hook_add c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.add a b)]
    | _ -> raise Not_implemented
  let hook_le c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (Z.leq a b)]
    | _ -> raise Not_implemented
  let hook_eq c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (Z.equal a b)]
    | _ -> raise Not_implemented
  let hook_ne c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (not (Z.equal a b))]
    | _ -> raise Not_implemented
  let hook_and c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.logand a b)]
    | _ -> raise Not_implemented
  let hook_mul c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.mul a b)]
    | _ -> raise Not_implemented
  let hook_sub c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.sub a b)]
    | _ -> raise Not_implemented
  let hook_tdiv c _ _ _ _ = match c with
      [Int a], [Int b] when b <> Z.zero -> [Int (Z.div a b)]
    | _ -> raise Not_implemented
  let hook_ediv c _ _ _ _ = match c with
      [Int a], [Int b] when b <> Z.zero -> [Int (Z.ediv a b)]
    | _ -> raise Not_implemented
  let hook_shl c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.shift_left a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_lt c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (Z.lt a b)]
    | _ -> raise Not_implemented
  let hook_ge c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (Z.geq a b)]
    | _ -> raise Not_implemented
  let hook_shr c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (try (Z.shift_right a (Z.to_int b)) with Z.Overflow -> if Z.geq a Z.zero then Z.zero else Z.of_int (-1))]
    | _ -> raise Not_implemented
  let hook_gt c _ _ _ _ = match c with
      [Int a], [Int b] -> [Bool (Z.gt a b)]
    | _ -> raise Not_implemented
  let hook_pow c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.pow a (Z.to_int b))]
    | _ -> raise Not_implemented
  let hook_powmod c _ _ _ _ = match c with
      [Int a], [Int b], [Int c]-> [Int (Z.powm a b c)]
    | _ -> raise Not_implemented
  let hook_xor c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.logxor a b)]
    | _ -> raise Not_implemented
  let hook_or c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.logor a b)]
    | _ -> raise Not_implemented
  let hook_not c _ _ _ _ = match c with
      [Int a] -> [Int (Z.lognot a)]
    | _ -> raise Not_implemented
  let hook_abs c _ _ _ _ = match c with
      [Int a] -> [Int (Z.abs a)]
    | _ -> raise Not_implemented
  let hook_max c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.max a b)]
    | _ -> raise Not_implemented
  let hook_min c _ _ _ _ = match c with
      [Int a], [Int b] -> [Int (Z.min a b)]
    | _ -> raise Not_implemented
  let hook_log2 c _ _ _ _ = match c with
      [Int a] -> [Int (Z.of_int (Z.log2 a))]
    | _ -> raise Not_implemented
  let hook_bitRange c _ _ _ _ = match c with
      [Int i], [Int off], [Int len] -> if Z.equal len Z.zero then [Int Z.zero] else [Int (try (Z.extract i (Z.to_int off) (Z.to_int len)) with Z.Overflow -> if not (Z.fits_int off) then if Z.geq i Z.zero then Z.zero else Z.of_int (-1) else raise Not_implemented)]
    | _ -> raise Not_implemented
  let hook_signExtendBitRange c _ _ _ _ = match c with
      [Int i], [Int off], [Int len] -> [Int (try (signed_extract i (Z.to_int off) (Z.to_int len)) with Z.Overflow -> if not (Z.fits_int off) then if Z.geq i Z.zero then Z.zero else Z.of_int (-1) else raise Not_implemented)]
    | _ -> raise Not_implemented
  let hook_rand c _ _ _ _ = match c with
      [Int max] -> let mpz = Gmp.Z.urandomm Gmp.RNG.default (from_zarith max) in
          [Int (to_zarith mpz)]
    | _ -> raise Not_implemented
  let hook_srand c _ _ _ _ = match c with
      [Int seed] -> let () = Gmp.Z.randseed Gmp.RNG.default (from_zarith seed) in []
    | _ -> raise Not_implemented
end

module FLOAT =
struct
  let hook_isNaN c _ _ _ _ = match c with
      [Float (f,_,_)] -> [Bool (Gmp.FR.is_nan f)]
    | _ -> raise Not_implemented
  let hook_maxValue c _ _ _ _ = match c with
      [Int prec], [Int exp] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((Gmp.FR.nexttoward (emin e p) (emax e) (Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 "inf") Gmp.FR.zero),e,p))]
    | _ -> raise Not_implemented
  let hook_minValue c _ _ _ _ = match c with
      [Int prec], [Int exp] -> let e = Z.to_int exp and p = Z.to_int prec in
        [round_to_range(Float ((Gmp.FR.nexttoward (emin e p) (emax e) Gmp.FR.zero (Gmp.FR.from_string_prec_base p Gmp.GMP_RNDN 10 "inf")),e,p))]
    | _ -> raise Not_implemented
  let hook_round c _ _ _ _ = match c with
      [Float (f,_,_)], [Int prec], [Int exp] ->
        [round_to_range (Float (f,(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_abs c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.abs_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_ceil c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.rint_prec p Gmp.GMP_RNDU f),e,p))]
    | _ -> raise Not_implemented
  let hook_floor c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.rint_prec p Gmp.GMP_RNDD f),e,p))]
    | _ -> raise Not_implemented
  let hook_acos c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.acos_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_asin c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.asin_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_atan c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.atan_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_cos c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.cos_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_sin c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.sin_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_tan c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.tan_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_exp c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.exp_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_log c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.log_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_neg c _ _ _ _ = match c with
      [Float (f,e,p)] -> [round_to_range(Float ((Gmp.FR.neg_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_add c _ _ _ _ = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.add_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_sub c _ _ _ _ = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.sub_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_mul c _ _ _ _ = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.mul_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_div c _ _ _ _ = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.div_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_pow c _ _ _ _ = match c with
      [Float (f1,e1,p1)], [Float (f2,e2,p2)]
        when e1 = e2 && p1 = p2 -> [round_to_range(Float ((Gmp.FR.pow_prec p1 Gmp.GMP_RNDN f1 f2),e1,p1))]
    | _ -> raise Not_implemented
  let hook_eq c _ _ _ _ = match c with
      [Float (f1,_,_)], [Float (f2,_,_)] -> [Bool (Gmp.FR.equal f1 f2)]
    | _ -> raise Not_implemented
  let hook_lt c _ _ _ _ = match c with
      [Float (f1,_,_)], [Float (f2,_,_)] -> [Bool (Gmp.FR.less f1 f2)]
    | _ -> raise Not_implemented
  let hook_le c _ _ _ _ = match c with
      [Float (f1,_,_)], [Float (f2,_,_)] -> [Bool (Gmp.FR.lessequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_gt c _ _ _ _ = match c with
      [Float (f1,_,_)], [Float (f2,_,_)] -> [Bool (Gmp.FR.greater f1 f2)]
    | _ -> raise Not_implemented
  let hook_ge c _ _ _ _ = match c with
      [Float (f1,_,_)], [Float (f2,_,_)] -> [Bool (Gmp.FR.greaterequal f1 f2)]
    | _ -> raise Not_implemented
  let hook_precision c _ _ _ _ = match c with
      [Float (_,_,p)] -> [Int (Z.of_int p)]
    | _ -> raise Not_implemented
  let hook_exponentBits c _ _ _ _ = match c with
      [Float (_,e,_)] -> [Int (Z.of_int e)]
    | _ -> raise Not_implemented
  let hook_float2int c _ _ _ _ = match c with
      [Float (f,_,_)] -> [Int (to_zarith (Gmp.FR.to_z_f f))]
    | _ -> raise Not_implemented
  let hook_int2float c _ _ _ _ = match c with
      [Int i], [Int prec], [Int exp] ->
        [round_to_range(Float ((Gmp.FR.from_z_prec (Z.to_int prec) Gmp.GMP_RNDN (from_zarith i)),(Z.to_int exp),(Z.to_int prec)))]
    | _ -> raise Not_implemented
  let hook_min _ _ _ _ _ = raise Not_implemented
  let hook_max _ _ _ _ _ = raise Not_implemented
  let hook_rem _ _ _ _ _ = raise Not_implemented
  let hook_root c _ _ _ _ = match c with
    | [Float (f,e,p)], [Int i] when Z.to_int i = 2 ->
        [round_to_range(Float ((Gmp.FR.sqrt_prec p Gmp.GMP_RNDN f),e,p))]
    | _ -> raise Not_implemented
  let hook_sign c _ _ _ _ = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (s,_,_) -> [Bool s])
    | _ -> raise Not_implemented
  let hook_significand c _ _ _ _ = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (_, _, Some s) -> [Int s]
        | _ -> raise Not_implemented)
    | _ -> raise Not_implemented
  let hook_atan2 _ _ _ _ _ = raise Not_implemented
  let hook_exponent c _ _ _ _ = match c with
      [Float (f,e,p)] -> (match deconstruct_float f e p with (_, exp, _) -> [Int (Z.of_int exp)])
    | _ -> raise Not_implemented
end

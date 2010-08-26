
(** {b Options} *)
(** We define a type for option descriptors. Such options can be set from the 
  * command line or from the UI *)
type optionDescr = {
    optInUI: string;
    (** The way the option should appear in the UI. Use & before a letter to 
     * indicate the shortcut letter  *)

    optRestart: bool; 
    (** Whether setting this option requires restarting the Engine *)
      
    optKind: optionKind;
    (** The option kind. *)

    optExtra: unit -> unit;
    (** An extra thing to do after setting the ref.
        This can be used, for instance, to set several refs
        with one option. *)

    optCommandLine: string;
    (** How the option should appear in the command line. The empty string 
     * means that this option does not appear among the command line options.*)

    optHelp: string;
    (** A help string that is printed when the --help argument is given or as 
      * a tooltip in the GUI *)
  } 

and optionKind = 
  | OUnit                        
  | OBool of bool ref            (** A boolean option *)
  | OInt  of int ref             (** An integer option *)
  | OString of string ref        (** A string option *)
  | OStringList of char * string list ref 
     (** A list of strings, with a separator. This means that the option can 
      * also appear multiple times *)
  | OOutChannel of (out_channel * string) option ref
      (** Takes a filename from the command line, opens a channel to that file,
       *  and updates the ref with the channel and the filename.
       *  The file is opened in text mode.
       *  Uses stdout if the argument is "-" or "stdout". *)

val optionToArgs: optionDescr -> (string * Arg.spec * string) list 

val splitStringList: char -> string -> string list


